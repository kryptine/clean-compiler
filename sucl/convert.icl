implementation module convert

// $Id$

import newtest
import newfold
import coreclean
import rule
import dnc
import graph
import basic
import checksupport
import syntax
import RWSDebug
import StdEnv

mstub = stub "convert"
block func = mstub func "blocked"

// Cocl to Sucl for functions
cts_function ::
    Int                                                     // Index of current module
    u:{#FunDef}                                             // Function definitions (from ICL)
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]   // Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                                 // Strict arguments (just main args for now)
    , [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]   // Arity and rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                         // Kind of symbol
    , v:{#FunDef}                                           // Consulted function definitions
    )
 ,  [u<=v]

//cts_function main_dcl_module_n fundefs = block "cts_function"
cts_function main_dcl_module_n fundefs
= (typerules,stricts,funbodies,funkinds,fundefs`)
  where ((typerules,stricts,funbodies,funkinds),fundefs`)
        = foldrarray (convert_fundef main_dcl_module_n) ([],[],[],[]) fundefs

//foldrarray :: (a .b -> .b) .b u:{#a} -> (.b,v:{#a}) | uselect_u,usize_u a, [u<=v]
foldrarray f i xs
= fold 0 (usize xs)
  where fold j (n,xs)
        | j>=n
          = (i,xs)
        = (f x i`,xs``)
          where (x,xs`) = xs![j]
                (i`,xs``) = fold (j+1) (n,xs`)

foldlarrayindex f (a,xs0)
= fold 0 a xs1
  where (s,xs1) = usize xs0
        fold j a0 xs2
        | j<s
          = fold (j+1) a1 xs3
        = (a0,xs2)
          where a1 = f a0 j xj
                (xj,xs3) = xs2![j]

convert_fundef
 :: Int
    FunDef
    ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]   // Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                                 // Strict arguments (just main args for now)
    , [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]   // Arity and rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                         // Kind of symbol
    )
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]   // Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                                 // Strict arguments (just main args for now)
    , [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]   // Arity and rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                         // Kind of symbol
    )

convert_fundef main_dcl_module_n fundef (typerulemap,strictsmap,fundefs0,kindmap)
 = ( [(funsym,typerule):typerulemap]
   , [(funsym,stricts):strictsmap]
   , fundefs1
   , [(funsym,kind):kindmap]
   )
   where {fun_body,fun_type,fun_index,fun_kind} = fundef
         funsym = SuclUser (SK_Function {glob_module=main_dcl_module_n,glob_object=fun_index})
         (typerule,stricts) = foldoptional notyperule convert_symboltype fun_type
         notyperule = abort "convert: convert_fundef: fun_type is absent"
         fundefs1 = convert_functionbody main_dcl_module_n funsym fun_body fundefs0
         kind = convert_kind fun_kind

/******************************************************************************
*  TYPE CONVERSION                                                            *
******************************************************************************/

/* Convert the SymbolType data structure
   This type describes the types of (function) symbols
   We use the principal type
   Strictness annotations are only handled for direct function arguments
*/
convert_symboltype :: SymbolType -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])
convert_symboltype {st_vars,st_args,st_arity,st_result,st_context,st_attr_vars,st_attr_env}
 = (mkrule typeargs typeroot graph``,stricts)
   where (heap`,(graph``,typeargs,stricts)) = convert_atypes (sucltypeheap,graph`) st_args // _ => forget annotations of subtypes
         (_,(graph`,[typeroot:_],[_:_])) = convert_atype st_result (heap`,(emptygraph,[],[])) // _ => forget annotations of result

/* Convert a list of attributed type (deriving its principal type for now)
   Intended to be used by foldlr.
   A type heap moves from left to right through the list, and is used recursively.
   The graph is built from right to left, also recursively.
   The converted types are collected so they may be used as argument to another type application.
*/
convert_atypes
 :: ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable)
    )
    [AType]
 -> ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable],[Bool])
    )
convert_atypes (heap,graph) atypes
 = foldlr convert_atype (heap,(graph,[],[])) atypes

convert_atype
 :: AType
    ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable],[Bool])
    )
 -> ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable],[Bool])
    )

convert_atype atype (heap,(graph,rest,srest))
 = (resheap,(resgraph,[restype:rest],[atype.at_annotation==AN_Strict:srest]))
   where (resheap,resgraph,restype)
         = case atype.at_type
           of

              // An ordinary type application
              TA typename atypes
               -> (heap``,updategraph typevar (typesym,typeargs) graph`,typevar)
                  where (heap``,(graph`,typeargs,_)) = convert_atypes (heap`,graph) atypes // _ => forget annotations of subtypes
                        [typevar:heap`] = heap
                        typesym = SuclUSER typename.type_index

              // A function type (a->b)
              functype --> argtype
               -> (heap```,graph```,suclrestype)
                  where (heap``,(graph``,fnargs,[_:_])) = convert_atype functype (heap`,(graph`,suclargtype,[])) // _ => forget annotations of subtypes
                        (heap```,(graph`,suclargtype,[_:_])) = convert_atype argtype (heap``,(graph,[],[])) // _ => forget annotations of subtypes
                        [suclrestype:heap`] = heap
                        graph``` = updategraph suclrestype (SuclFN 1,fnargs) graph``

              // A basic type, which is translated to an application of a basic type symbol to the empty list of arguments
              TB basictype
               -> (heap`,graph`,suclbasictype)
                  where [suclbasictype:heap`] = heap
                        graph` = updategraph suclbasictype (convert_btype basictype,[]) graph

              // A type variable, used in polymorphism
              TV tvname
               -> (heap,graph,SuclNAMED tvname)

              // A type error
              TE
               -> (heap`,graph`,typevar)
                  where [typevar:heap`] = heap
                        graph` = updategraph typevar (SuclERROR,[]) graph

              // Anything else will produce an error when actually used
              otherform
               -> (heap`,graph`,typevar)
                  where [typevar:heap`] = heap
                        graph` = updategraph typevar (notimpl,[]) graph
                        notimpl = error ("convert_atype: unknown form of Type: "+++showTypeConstr otherform)

showTypeConstr (TA _ _) = "TA"
showTypeConstr (_ --> _) = "-->"
showTypeConstr (_ :@: _) = ":@:"
showTypeConstr (TB _) = "TB"
showTypeConstr (TFA _ _) = "TFA"
showTypeConstr (GTV _) = "GTV"
showTypeConstr (TV _) = "TV"
showTypeConstr (TempV _) = "TempV"
showTypeConstr (TQV _) = "TQV"
showTypeConstr (TempQV _) = "TempQV"
showTypeConstr (TLifted _) = "TLifted"
showTypeConstr (TE) = "TE"

// Convert a basic type to a basic type symbol
convert_btype :: BasicType -> SuclTypeSymbol
convert_btype BT_Int = SuclINT
convert_btype BT_Char = SuclCHAR
convert_btype BT_Real = SuclREAL
convert_btype BT_Bool = SuclBOOL
convert_btype (BT_String _) = SuclSTRING
convert_btype BT_Dynamic = SuclDYNAMIC
convert_btype BT_File = SuclFILE
convert_btype BT_World = SuclWORLD
convert_btype _ = error "convert: convert_btype: unhandled BasicType constructor"


/******************************************************************************
*  ALGEBRAIC TYPE CONVERSION                                                  *
******************************************************************************/


cts_getconstrs ::
    {#DclModule}    // Info from used DCL modules
    Int             // Index of current module in DCL module array
    CommonDefs      // CommonDefs in ICL module (excluding FunDefs)
 -> [(SuclTypeSymbol,[(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))])]
                    // List of constructor symbols for each type symbol

// cts_getconstrs dcl_mods main_dcl_module_n icl_common = block "cts_getconstrs"
cts_getconstrs dcl_mods main_dcl_module_n icl_common
= flatten (zipwith f (a2l dcl_mods) [0..])
  where f dcl_mod dcli
        = [convert_typedef commondefs.com_cons_defs dcli typedef \\ typedef <-: commondefs.com_type_defs]
          where commondefs = if (dcli==main_dcl_module_n) icl_common dcl_mod.dcl_common

a2l a = [e \\ e<-:a]

convert_typedef :: {#ConsDef} Index (TypeDef TypeRhs) -> (SuclTypeSymbol,[(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))])
convert_typedef constructors dcli typedef
= (SuclUSER (mkglobal dcli typedef.td_index),getconstrs constructors dcli typedef.td_rhs)

getconstrs constructors dcli (AlgType constrs)
= map mkalgconstr constrs
  where mkalgconstr defsymb = (SuclUser (SK_Constructor (mkglobal dcli defsymb.ds_index)),convert_symboltype constructors.[defsymb.ds_index].cons_type)
getconstrs constructors dcli (SynType at) = [] // FIXME: Make sure synonym types are handled correctly elsewhere
getconstrs constructors dcli (RecordType rt) = [(SuclUser (SK_Constructor (mkglobal dcli rt.rt_constructor.ds_index)),convert_symboltype constructors.[rt.rt_constructor.ds_index].cons_type)]
getconstrs constructors dcli (AbstractType bitvect) = [] // FIXME: Make sure synonym types are handled correctly elsewhere
getconstrs constructors dcli (UnknownType) = mstub "getconstrs" "UnknownType constructor not handled"

mkglobal gmod gob = {glob_module = gmod, glob_object = gob}


/******************************************************************************
*  EXPRESSION CONVERSION                                                      *
******************************************************************************/

convert_functionbody :: Int SuclSymbol FunctionBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_functionbody main_dcl_module_n funsym (TransformedBody t) fundefs0 = convert_transformedbody main_dcl_module_n funsym t fundefs0
convert_functionbody main_dcl_module_n funsym _ fundefs0
 = [(funsym,norule):fundefs0]
   where norule = error "convert: convert_functionbody: unexpected FunctionBody constructor"

convert_transformedbody :: Int SuclSymbol TransformedBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_transformedbody main_dcl_module_n funsym {tb_args=args,tb_rhs=expression} fundefs0
   // Sanity check
 | not (isEmpty globals1) ---> ("convert.convert_transformedbody: arguments: "+++listToString (map fst bindings))
   = abort ("convert: convert_transformedbody: function rhs contains free variables: "+++listToString globals0)
 = [(funsym,(length args,[mkrule (map snd bindings) (hd rest) (compilegraph nodes0)])):fundefs1]
   where globals1 = filter (not o flip isMember (map snd bindings)) globals0
         (_,(nodes0,fundefs1,globals0,rest))
          = (convert_expression--->"convert.convert_expression begins from convert.convert_transformedbody") main_dcl_module_n bindings expression (heap0,([],fundefs0,[],[]))
         heap0 = heap
         bindings = map mkseen args
         mkseen fv = (fv.fv_info_ptr,SuclNamed fv.fv_info_ptr)

heap = map SuclAnonymous [0..]

:: NodeBinding sym var :== (var,Node sym var)
:: FunBinding sym var :== (sym,(Int,[Rule sym var]))    // Arity and rules for lifted functions

:: Econv_state
   :== ( [SuclVariable]                         // Heap of node-ids
       , ( [NodeBinding SuclSymbol SuclVariable]// Nodes of Sucl expression being built
         , [FunBinding SuclSymbol SuclVariable] // Lifted functions for case/lambda expressions
         , [SuclVariable]                       // Free Sucl variables in expression being built
         , [SuclVariable]                       // List of variables to which root of expression is prepended (accumulator)
         )
       )

convert_expressions main_dcl_module_n bounds exprs lrinfo
 = (foldlr ((convert_expression--->"convert.convert_expression begins from convert_expressions") main_dcl_module_n bounds) (heap0,(nodes0,fundefs0,globals0,[])) exprs <--- "convert.convert_expressions ends") ---> "convert.convert_expressions begins"
   where (heap0,(nodes0,fundefs0,globals0)) = lrinfo

convert_expression ::
    Int                                         // Index of current DCL module
    [(VarInfoPtr,SuclVariable)]                 // Variables bound in the environment
    Expression                                  // Expression to convert
    Econv_state                                 // Input expression conversion state
 -> Econv_state                                 // Resulting expression conversion state

convert_expression main_dcl_module_n bindings (Var varinfo) lrinfo
= (heap0,(nodes0,fundefs0,globals1,rest`))
  where (globals1,rest`) = foldmap bound free bindings vip
        bound node = ([node:globals0],[node:rest])
        free
        = (globals0,[nonode:rest])
          where nonode = abort ("convert.convert_expression.Var: expression contains free variable: "+++toString varinfo.var_info_ptr)
        vip = varinfo.var_info_ptr
        (heap0,(nodes0,fundefs0,globals0,rest)) = lrinfo

convert_expression main_dcl_module_n bindings (App appinfo) lrinfo
= (heap2,(nodes2,fundefs1,globals1,[root:rest])) <--- "convert.convert_expression ends (for App expression)"
  where [root:heap1] = heap0
        (heap2,(nodes1,fundefs1,globals1,args0))
        = convert_expressions main_dcl_module_n bindings appinfo.app_args (heap1,(nodes0,fundefs0,globals0))
        nodes2 = [(root,(SuclUser appinfo.app_symb.symb_kind,args0)):nodes1]
        (heap0,(nodes0,fundefs0,globals0,rest)) = lrinfo

convert_expression main_dcl_module_n bounds (expr @ exprs) lrinfo
= (heap2,(nodes2,fundefs1,globals1,[root:rest])) <--- "convert.convert_expression ends (for (@) expression)"
  where [root:heap1] = heap0
        (heap2,(nodes1,fundefs1,globals1,args0))
         = convert_expressions main_dcl_module_n bounds [expr:exprs] (heap1,(nodes0,fundefs0,globals0))
        nodes2 = [(root,(SuclApply (length exprs),args0)):nodes1]
        (heap0,(nodes0,fundefs0,globals0,rest)) = lrinfo

convert_expression main_dcl_module_n bindings0 (Let letinfo) lrinfo
= (heap2,(nodes2,fundefs2,globals3,rest`)) <--- "convert.convert_expression ends (for Let expression)"
  where globals3 = filter (not o flip isMember (map snd bindings1)) globals2
        (heap2,(nodes2,fundefs2,globals2,rest`)) = convert_expression main_dcl_module_n bindings1 letinfo.let_expr (heap1,(nodes1,fundefs1,globals1,rest))
        (heap1,(nodes1,fundefs1,globals1,_)) = convert_expressions main_dcl_module_n bindings1 [lb.lb_src \\ lb<-letinfo.let_lazy_binds] (heap0,(nodes0,fundefs0,globals0))
        bindings1 = map (pairwith SuclNamed) boundvars++bindings0
        boundvars = [lb.lb_dst.fv_info_ptr \\ lb<-letinfo.let_lazy_binds]
        (heap0,(nodes0,fundefs0,globals0,rest)) = lrinfo

convert_expression main_dcl_module_n bindings (Case caseinfo) lrinfo
= (heap4,(nodes9,fundefs9,globals9,[root:rest])) <--- "convert.convert_expression ends (for Case expression)"
  where // Plan: (0.5) convert selector
        //       (1) convert branches
        //       (1.5) convert default if present
        //       (2) build rules/fundef from branches
        //       (4) build closure node
        // (4) Build closure node
        closureargs = ((selectorroots++innerglobals1++defaultroots) <--- ("convert.convert_expression.Case.closureargs ends with "+++toString (length innerglobals1)+++" inner global(s), "+++toString (length defaultroots)+++" default root(s), and "+++toString (length selectorroots)+++" selector root")) ---> "convert.convert_expression.Case.closureargs begins"
        nodes9 = [(root,(SuclCase caseinfo.case_info_ptr,closureargs)):nodes8]
        // (2) build rules/fundef from branches
        fundefs9
        = [(SuclCase caseinfo.case_info_ptr,(length closureargs,map mkalt alternatives++map mkdefaultalt defaultroots)):fundefs8]
           where mkalt (patroot,reproot,nodes)
                  = mkrule ([patroot:innerglobals1++defaultroots]) reproot (compilegraph nodes)
                 mkdefaultalt defaultroot
                  = mkrule (selectorroots++innerglobals1++defaultroots) defaultroot emptygraph
        // (1.5) convert default if necessary
        (heap4,(nodes7,fundefs6,globals7,defaultroots))
         = foldoptional id ((convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case default)") main_dcl_module_n bindings) caseinfo.case_default (heap3,(nodes6,fundefs5,globals6,[]))
        // (1) convert branches
        globals8 = innerglobals1++globals7
        innerglobals1 = removeDup innerglobals0
        (heap3,(innerglobals0,fundefs7,alternatives))
         = case caseinfo.case_guards
           of AlgebraicPatterns _ branches
               -> foldlr (convert_algebraic_branch main_dcl_module_n bindings) (heap2,([],fundefs6,[])) branches
              BasicPatterns _ branches
               -> foldlr (convert_basic_branch main_dcl_module_n bindings) (heap2,([],fundefs6,[])) branches
              _
               -> (heap2,([],fundefs6,error "convert: convert_expression: unhandled CasePatterns constructor"))
        // (0.5) Convert selector
        (heap2,(nodes8,fundefs8,globals9,selectorroots))
         = (convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case selector)") main_dcl_module_n bindings caseinfo.case_expr (heap1,(nodes7,fundefs7,globals8,[]))
        // (0) Claim root node
        [root:heap1] = heap0
        (heap0,(nodes6,fundefs5,globals6,rest)) = lrinfo

convert_expression main_dcl_module_n bindings (BasicExpr bv bt) lrinfo
= (heap1,(nodes1,fundefs0,globals0,[root:rest])) <--- "convert.convert_expression ends (for BasicExpr expression)"
  where [root:heap1] = heap0
        nodes1 = [(root,(convert_bvalue bv,[])):nodes0]
        (heap0,(nodes0,fundefs0,globals0,rest)) = lrinfo

convert_expression _ _ (Selection _ _ _)      _ = mstub "convert_expression" "Selection constructor not handled"
convert_expression _ _ (Update _ _ _)         _ = mstub "convert_expression" "Update not handled"
convert_expression _ _ (RecordUpdate _ _ _)   _ = mstub "convert_expression" "RecordUpdate constructor not handled"
convert_expression _ _ (TupleSelect _ _ _)    _ = mstub "convert_expression" "TupleSelect constructor not handled"
convert_expression _ _ (WildCard)             _ = mstub "convert_expression" "WildCard constructor not handled"
convert_expression _ _ (AnyCodeExpr _ _ _)    _ = mstub "convert_expression" "AnyCodeExpr constructor not handled"
convert_expression _ _ (ABCCodeExpr _ _)      _ = mstub "convert_expression" "ABCCodeExpr constructor not handled"
convert_expression _ _ (MatchExpr _ _ _)      _ = mstub "convert_expression" "MatchExpr constructor not handled"
convert_expression _ _ (FreeVar _)            _ = mstub "convert_expression" "FreeVar constructor not handled"
convert_expression _ _ (Constant _ _ _ _)     _ = mstub "convert_expression" "Constant constructor not handled"
convert_expression _ _ (ClassVariable _)      _ = mstub "convert_expression" "ClassVariable constructor not handled"
convert_expression _ _ (DynamicExpr _)        _ = mstub "convert_expression" "DynamicExpr constructor not handled"
convert_expression _ _ (TypeCodeExpression _) _ = mstub "convert_expression" "TypeCodeExpression constructor not handled"
convert_expression _ _ (EE)                   _ = mstub "convert_expression" "EE constructor not handled"
convert_expression _ _ (NoBind _)             _ = mstub "convert_expression" "NoBind constructor not handled"

convert_algebraic_branch ::
    Int
    [(VarInfoPtr,SuclVariable)]     // Locally bound variables, with the expressions they're bound to
    AlgebraicPattern
    ( [SuclVariable]
    , ( [SuclVariable]
      , [FunBinding SuclSymbol SuclVariable]
      , [(SuclVariable,SuclVariable,[(SuclVariable,Node SuclSymbol SuclVariable)])]
      )
    )
 -> ( [SuclVariable]
    , ( [SuclVariable]
      , [FunBinding SuclSymbol SuclVariable]
      , [(SuclVariable,SuclVariable,[(SuclVariable,Node SuclSymbol SuclVariable)])]
      )
    )

convert_algebraic_branch main_dcl_module_n bindings0 branch lrinfo
= (heap2,(globals2,fundefs1,alternatives1)) ---> ("convert.convert_algebraic_branch: binding variables: "+++listToString (map fst argmap))
  where // Unpack conversion state
        (heap0,(globals0,fundefs0,alternatives0)) = lrinfo
        // Claim root node of pattern
        [root:heap1] = heap0
        // Determine constructor symbol
        conssym = SuclUser (SK_Constructor {glob_module=main_dcl_module_n,glob_object=branch.ap_symbol.glob_object.ds_index})
        // Determine constructor argument variables
        consargs = [fv.fv_info_ptr \\ fv <- branch.ap_vars]
        // Map pattern's arguments to nodes
        argmap = map (pairwith SuclNamed) consargs
        // Create pattern's root node definition
        nodes1 = [(root,(conssym,map snd argmap)):nodes0]
        // Record pattern's arguments in environment
        bindings1 = argmap++bindings0
        // Convert branch expression
        (heap2,(nodes0,fundefs1,globals1,rest)) = (convert_expression--->"convert.convert_expression begins from convert_algebraic_branch") main_dcl_module_n bindings1 branch.ap_expr (heap1,([],fundefs0,globals0,[]))
        // Mask pattern's arguments from globals
        globals2 = filter (not o flip isMember (map snd argmap)) globals1
        // Create root of pattern,root of replacement, defined node of alternative
        alternatives1 = [(root,hd rest,nodes1):alternatives0]

convert_basic_branch ::
    Int
    [(VarInfoPtr,SuclVariable)]     // Locally bound variables, with the expressions they're bound to
    BasicPattern
    ( [SuclVariable]
    , ( [SuclVariable]
      , [FunBinding SuclSymbol SuclVariable]
      , [(SuclVariable,SuclVariable,[(SuclVariable,Node SuclSymbol SuclVariable)])]
      )
    )
 -> ( [SuclVariable]
    , ( [SuclVariable]
      , [FunBinding SuclSymbol SuclVariable]
      , [(SuclVariable,SuclVariable,[(SuclVariable,Node SuclSymbol SuclVariable)])]
      )
    )

convert_basic_branch main_dcl_module_n bindings branch lrinfo
= (heap2,(globals1,fundefs1,alternatives1))
  where // Unpack conversion state
        (heap0,(globals0,fundefs0,alternatives0)) = lrinfo
        // Claim root node of pattern
        [root:heap1] = heap0
        // Create pattern's root node definition
        nodes1 = [(root,(convert_bvalue branch.bp_value,[])):nodes0]
        // Convert branch expression
        (heap2,(nodes0,fundefs1,globals1,rest)) = (convert_expression--->"convert.convert_expression begins from convert.convert_basic_branch") main_dcl_module_n [] branch.bp_expr (heap1,([],fundefs0,globals0,[]))
        alternatives1 = [(root,hd rest,nodes1):alternatives0]

convert_bvalue :: BasicValue -> SuclSymbol
convert_bvalue (BVI intrepr) = SuclInt (toInt intrepr)
//convert_bvalue (BVC charrepr) = SuclChar (fromString charrepr)
convert_bvalue (BVC charrepr) = mstub "convert_bvalue" "BVC constructor not handled"
convert_bvalue (BVB bool) = SuclBool bool
convert_bvalue (BVR realrepr) = SuclReal (toReal realrepr)
convert_bvalue (BVS stringrepr) = SuclString (fromString stringrepr)
convert_bvalue _ = mstub "convert_bvalue" "unhandled BasicValue constructor"

convert_kind :: DefOrImpFunKind -> SuclSymbolKind
convert_kind (FK_DefFunction b) = SuclPrimitive // Function from a definition module
convert_kind (FK_ImpFunction b) = SuclFunction  // Function from a (the) implementation module
convert_kind  FK_DefMacro       = SuclFunction  // Macro from a definition module
convert_kind  FK_ImpMacro       = SuclFunction  // Macro from an implementation module
convert_kind _ = error "convert: convert_kind: unhandled DefOrImpFunKind constructor"


/****************************************************************
**  Conversion of exported function symbols from cocl to sucl  **
****************************************************************/

cts_exports :: {#DclModule} *PredefinedSymbols Int -> (.PredefinedSymbols,[SuclSymbol])
// cts_exports dcl_mods predefs main_dcl_module_n = block "cts_exports"
cts_exports dcl_mods predefs main_dcl_module_n
= add_start main_dcl_module_n (predefs,map (mk_symbol main_dcl_module_n) (getconversion cFunctionDefs dcl_mods.[main_dcl_module_n]))

add_start main_dcl_module_n (predefs0,exports)
= (predefs1,extended_exports)
  where extended_exports
        = if (pds_module==main_dcl_module_n && pds_def<>NoIndex)
             [mk_symbol main_dcl_module_n pds_def:exports]
             exports
        ({pds_module,pds_def},predefs1) = predefs0![PD_Start]

mk_symbol :: Int Index -> SuclSymbol
mk_symbol main_dcl_module_n fundef_index = SuclUser (SK_Function {glob_module=main_dcl_module_n,glob_object=fundef_index})

getconversion whichtable dcl=:{dcl_conversions=(Yes conversions)}
= [i\\i<-:conversions.[whichtable]]
getconversion whichtable dcl=:{dcl_conversions=No}
= [0..dcl.dcl_sizes.[whichtable]-1]


/*********************************************************************
**  Conversion of generated function definitions form sucl to cocl  **
*********************************************************************/

/* Necessary global state:
   - Variables.
     Variables from original program not reused.
     Unless maybe for CAFs, forget those for now.
   - Expressions.
     For each expression construction.
     All newly created.
   - Function symbols.
     Reuse function symbols where applicable.
*/

:: VarAlloc = {va_heap :: .Heap VarInfo, va_id :: Int}

newvar :: {#.Char} *VarAlloc -> ((Ident, .Ptr VarInfo), .VarAlloc)
newvar prefix va
= ((ident,viptr),{va_heap=newheap,va_id=nextid})
  where ident
        = { id_name = prefix+++toString va.va_id
          , id_info = nilPtr
          }
        (viptr,newheap) = newPtr VI_Empty va.va_heap
        nextid = va.va_id+1

//Sucl to Cocl for function bodies
//1.3
stc_funcdefs ::
    PredefinedSymbol    // Compiler-predefined String symbol
    {#.DclModule}       // DCL for looking up constructor types
    Int                 // Index of current module
    CommonDefs          // Common defs in icl module (excluding FunDefs)
    Int                 // Index of first new generated function
    *ExpressionHeap     // Fresh expression space
    *(Heap VarInfo)     // Fresh variable space
    [Symredresult .SuclSymbol .SuclVariable SuclTypeSymbol SuclTypeVariable]
                        // Function definitions to convert
    *{#FunDef}          // Old function definitions
 -> ( .ExpressionHeap   // Remaining expression space
    , .(Heap VarInfo)   // Remaining variable space
    , .{#FunDef}        // Converted function definitions
    )
//3.1
/*2.0
stc_funcdefs ::
    PredefinedSymbol
    {#.DclModule}
    Int
    CommonDefs          // Common defs in icl module (excluding FunDefs)
    Int
    *ExpressionHeap
    *(Heap VarInfo)
    [Symredresult SuclSymbol .SuclVariable a b]
    *(c FunDef)
 -> ( .ExpressionHeap
    , .(Heap VarInfo)
    , .{#FunDef}
    )
 |  Array c FunDef
0.2*/

// stc_funcdefs stringtype dcl_mods main_dcl_module_n icl_common firstnewindex exprheap0 varheap0 srrs oldfundefs0 = block "stc_funcdefs"
stc_funcdefs stringtype dcl_mods main_dcl_module_n icl_common firstnewindex exprheap0 varheap0 srrs oldfundefs0
= ((exprheap1,varheap1,new_fundefs)<---"convert.stc_funcdefs ends")--->"convert.stc_funcdefs begins"
  where new_fundef_limit = foldr max n_oldfundefs [gi.glob_object+1\\{srr_assigned_symbol = SuclUser (SK_Function gi)}<-srrs | gi.glob_module==main_dcl_module_n]
        {va_heap=varheap1} = varalloc1
        (exprheap1,varalloc1,new_fundefs)
        = (store_newfuns--->"convert.store_newfuns begins from stc_funcdefs") stringtype (getconsdef dcl_mods main_dcl_module_n icl_common) main_dcl_module_n firstnewindex exprheap0 varalloc0 srrs (copy_oldfuns oldfundefs1 initialarray)
        varalloc0 = {va_heap=varheap0,va_id=0}
        initialarray = {nofundef i\\i<-[0..new_fundef_limit-1]}
        nofundef funindex
        = { fun_symb     = noident
          , fun_arity    = 0            // Can't do undef because it's strict
          , fun_priority = NoPrio
          , fun_body     = NoBody
          , fun_type     = No
          , fun_pos      = NoPos
          , fun_index    = funindex
          , fun_kind     = FK_DefOrImpUnknown
          , fun_lifted   = 0            // FIXME: what's this supposed to be?
          , fun_info     = nofuninfo    // Bah. Give me undef any time.
          }
        noident
        = { id_name = "_anonymous_sucl_generated_function_placeholder"
          , id_info = nilPtr
          }
        nofuninfo
        = { fi_calls       = []         // This is a lie. Undef would be better.
          , fi_group_index = 0
          , fi_def_level   = NotALevel
          , fi_free_vars   = []
          , fi_local_vars  = []
          , fi_dynamics    = []
          , fi_properties  = 0
          }
        (n_oldfundefs,oldfundefs1) = usize oldfundefs0

getconsdef dcl_mods main_dcl_module_n icl_common {glob_module,glob_object}
= commondefs.com_cons_defs.[glob_object]
  where commondefs
        = if (glob_module==main_dcl_module_n)
             icl_common
             dcl_mods.[glob_module].dcl_common

copy_oldfuns srcfundefs0 dstfundefs0
= (foldlArrayStWithIndex copyone srcfundefs1 dstfundefs1<---"convert.copy_oldfuns ends")--->sizes
  where copyone i srcfundef dstfundefs
        = ({dstfundefs & [i]=srcfundef} <--- ("convert.copy_oldfuns.copyone "+++toString i+++" ends")) ---> ("convert.copy_oldfuns.copyone "+++toString i+++" begins")
        (srcsize,srcfundefs1) = usize srcfundefs0
        (dstsize,dstfundefs1) = usize dstfundefs0
        sizes = "convert.copy_oldfuns begins (#srcfundefs="+++toString srcsize+++" #dstfundefs="+++toString dstsize+++")"

store_newfuns stringtype getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 [] fundefs0
= (exprheap0,varalloc0,fundefs0)<---"convert.store_newfuns ends (no more srrs)"
store_newfuns stringtype getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 [srr:srrs] fundefs0
= case srr.srr_assigned_symbol
  of (SuclUser (SK_Function {glob_module=modi,glob_object=funindex}))
      | modi == main_dcl_module_n
        -> (store_newfuns--->"convert.store_newfuns begins from store_newfuns") stringtype getconsdef main_dcl_module_n firstnewindex exprheap1 varalloc1 srrs fundefs1<---"convert.store_newfuns ends (srr in main module)"
           where (exprheap1,varalloc1,funbody,freevars,localvars,eips)
                 = stc_funcdef stringtype getconsdef exprheap0 varalloc0 srr.srr_function_def
                 funinfo
                 = { fi_calls       = collect_calls main_dcl_module_n funbody
                   , fi_group_index = 0
                   , fi_def_level   = NotALevel
                   , fi_free_vars   = freevars
                   , fi_local_vars  = localvars
                   , fi_dynamics    = [] // eips
                   , fi_properties  = 0
                   }
                 fundefs1 = create_or_update_fundefs funindex funbody funinfo fundefs0
                 create_or_update_fundefs
                 = if (funindex>=firstnewindex)
                      (create_fundef srr.srr_arity)
                      update_fundef
     _
      -> (store_newfuns--->"convert.store_newfuns begins from store_newfuns") stringtype getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 srrs fundefs0 <--- "convert.store_newfuns ends (srr in other module)"

create_fundef :: .Int Int FunctionBody FunInfo *{#FunDef} -> .{#FunDef}
create_fundef arity funindex funbody funinfo fundefs
= ({fundefs & [funindex] = fundef} <--- ("convert.create_fundef "+++toString funindex+++" ends")) ---> ("convert.create_fundef "+++toString funindex+++" begins")
  where fundef
        = { fun_symb     = ident
          , fun_arity    = arity
          , fun_priority = NoPrio
          , fun_body     = funbody
          , fun_type     = No
          , fun_pos      = NoPos
          , fun_index    = funindex
          , fun_kind     = FK_ImpFunction False
          , fun_lifted   = 0   // FIXME: what's this supposed to be?
          , fun_info     = funinfo
          }
        ident
        = { id_name = "_anonymous_sucl_generated_function"
          , id_info = nilPtr
          }

update_fundef :: .Int FunctionBody FunInfo *{#FunDef} -> .{#FunDef}
update_fundef index newbody newinfo oldfundefs
= ({tmpfundefs & [index] = newfundef} <--- ("convert.update_fundef "+++toString index+++" ends")) ---> ("convert.update_fundef "+++toString index+++" begins")
  where (oldfundef,tmpfundefs) = oldfundefs![index]
        newfundef = {oldfundef & fun_body = newbody, fun_info = newinfo}

stc_funcdef ::
    PredefinedSymbol                    // Compiler-predefined String symbol
    ((Global Index) -> ConsDef)         // Get constructor definition from environment
    *ExpressionHeap                     // Fresh expression space
    *VarAlloc                           // Fresh variable space
    (FuncDef SuclSymbol SuclVariable)   // Function definition to convert
 -> ( *ExpressionHeap                   // Remaining expression space
    , *VarAlloc                         // Remaining variable space
    , FunctionBody                      // Converted function body
    , [FreeVar]                         // List of free variables in the function body (from function arguments and case pattern arguments)
    , [FreeVar]                         // List of local variables in the function body (from lets)
    , [ExprInfoPtr]                     // List of expression pointers from the function body
    )

// stc_funcdef stringtype getconsdef exprheap0 varalloc0 (args,body) = block "stc_funcdef"
stc_funcdef stringtype getconsdef exprheap0 varalloc0 (args,body)
= (exprheap1,varalloc2,TransformedBody tb,tb.tb_args++freevars,localvars,eips)
  where tb
        = { tb_args = map (mkfreevar 0 o varenv) args
          , tb_rhs  = expr
          }
        (exprheap1,varalloc2,expr,freevars,localvars,eips)
        = convert_funcbody stringtype getconsdef 1 args varenv exprheap0 varalloc1 [] [] [] body
        (varenv,varalloc1)
        = allocate_freevars "_farg" noexpr varalloc0 args
        noexpr = mstub "std_funcdef" "open variable in rhs but not lhs"

mkfreevar :: Level (Ident,VarInfoPtr) -> FreeVar
mkfreevar level identvarinfoptr
= freevar
  where freevar
        = { fv_def_level = level
          , fv_name      = ident
          , fv_info_ptr  = varinfoptr
          , fv_count     = 1 // FIXME: reference counting for case pattern argument not yet implemented
          }
        (ident,varinfoptr) = identvarinfoptr

mkboundvar :: ExprInfoPtr (Ident,VarInfoPtr) -> BoundVar
mkboundvar exprinfoptr identvarinfoptr
= boundvar
  where boundvar
        = { var_name      = ident
          , var_info_ptr  = varinfoptr
          , var_expr_ptr  = exprinfoptr
          }
        (ident,varinfoptr) = identvarinfoptr

/*

Converting a function body:

 Take a heap of ExprInfo (for some expression forms)
 Return reduced heap of ExprInfo
 Take a level for fresh free variables for case patterns

 For the leaf graphs:
     Take a list of encountered variables with usage counts
     Return extended list of encountered variables with their usage counts
     Take a sharing indication function
     Take list of let-bindings for shared variables
     Return extended list of let-bindings for shared variables
     Take complete list of let-bindings
     Take mapping from free variables to freevars
     Take a heap of ExprInfo (for some expression forms)
     Return reduced heap of ExprInfo
     Return main expression

*/

convert_funcbody ::
    PredefinedSymbol                        // Compiler-predefined String symbol
    ((Global Index) -> ConsDef)             // Get constructor definition from environment
    Level                                   // (Lexical?) level for new variables
    [SuclVariable]                          // Nodes from case variables in the environment
    (SuclVariable -> (Ident,VarInfoPtr))    // Mapping from free nodes to variables
    *ExpressionHeap                         // Fresh expression space
    *VarAlloc                               // Fresh variable space
    [FreeVar]                               // Accumulator for list of free variables in the function body (from function arguments and case pattern arguments)
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    !(FuncBody SuclSymbol SuclVariable)     // Function body to convert
 -> ( *ExpressionHeap                       // Modified expression space
    , *VarAlloc                             // Modified variable space
    , Expression                            // Resulting expression
    , [FreeVar]                             // List of free variables in the function body (from function arguments and case pattern arguments)
    , [FreeVar]                             // List of local variables in the function body (from lets)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_funcbody stringtype getconsdef level patnodes varenv exprheap0 varalloc0 freevars0 localvars0 eips0 (MatchPattern pattern yesbody nobody)
= (exprheap4,varalloc3,match_expression,freevars2,[default_freevar:localvars2],[letinfoptr,default_expr_ptr:eips2])
  where (exprheap3,varalloc1,case_expression,default_refcount,freevars2,localvars2,eips2)
        = convert_matchpatterns getconsdef build_casebranch patnodes varenv exprheap2 varalloc0 default_expression pgraph level freevars1 localvars1 eips1 [proot]
        pgraph = rgraphgraph pattern
        proot = rgraphroot pattern
        default_boundvar
        = { var_name = default_ident
          , var_info_ptr = default_info_ptr
          , var_expr_ptr = default_expr_ptr
          }
        ((default_ident,default_info_ptr),varalloc2) = newvar "_defaultvar" varalloc1
        (letinfoptr,exprheap1) = newPtr EI_Empty exprheap0
        (default_expr_ptr,exprheap2) = newPtr EI_Empty exprheap1
        li
        = { let_strict_binds = []
          , let_lazy_binds = [{lb_dst=default_freevar,lb_src=match_failure_expression,lb_position=NoPos}]
          , let_expr = case_expression
          , let_info_ptr = letinfoptr
          , let_expr_position = NoPos
          }
        default_freevar
        = { fv_def_level=level
          , fv_name=default_ident
          , fv_info_ptr=default_info_ptr
          , fv_count=default_refcount
          }
        build_casebranch level` patnodes` varenv` freevars0` localvars0` eips0` exprheap0` varalloc0`
        = (exprheap1`,varalloc1`,expr`,0,freevars1`,localvars1`,eips1`)
          where (exprheap1`,varalloc1`,expr`,freevars1`,localvars1`,eips1`)
                = convert_funcbody stringtype getconsdef level` patnodes` varenv` exprheap0` varalloc0` freevars0` localvars0` eips0` yesbody
        (exprheap4,varalloc3,match_failure_expression,freevars1,localvars1,eips1)
        = convert_funcbody stringtype getconsdef (level+1) patnodes varenv exprheap3 varalloc2 freevars0 localvars0 eips0 nobody
        (default_expression,match_expression)
        = if (default_refcount==1)
             (match_failure_expression,case_expression)
             (match_failure_reference,let_expression)
        let_expression = Let li
        match_failure_reference = Var default_boundvar

convert_funcbody stringtype getconsdef level patnodes varenv exprheap0 varalloc0 freevars0 localvars0 eips0 (BuildGraph srgraph)
= convert_graph stringtype patnodes (FreeVar o mkfreevar level o varenv) level srgraph varalloc0 exprheap0 freevars0 localvars0 eips0

convert_matchpatterns ::
    ((Global Index) -> ConsDef)             // Get ConsDef from environment
    (  Int                                  // Level to assign to free variables
       [SuclVariable]                       // List of pattern nodes
       (SuclVariable->(Ident,VarInfoPtr))   // Assigning FreeVars to variables from the environment
       [FreeVar]                            // Accumulator for list of free variables in the function body (from function arguments and case pattern arguments)
       [FreeVar]                            // Accumulator for list of local variables in the function body (from lets)
       [ExprInfoPtr]                        // Accumulator for list of expression pointers from the function body
       *ExpressionHeap                      // Initial expression heap for case branch
    ->*(  *VarAlloc                         // Initial variable heap for case branch
       -> ( *ExpressionHeap                 // Modified expression heap from case branch
          , *VarAlloc                       // Modified variable heap from case branch
          , Expression                      // Resulting branch expression
          , Int                             // Reference count to default expression
          , [FreeVar]                       // List of free variables in the function body (from function arguments and case pattern arguments)
          , [FreeVar]                       // List of local variables in the function body (from lets)
          , [ExprInfoPtr]                   // List of expression pointers from the function body
          )
       )
    )
    [SuclVariable]                          // List of pattern nodes
    (SuclVariable->(Ident,VarInfoPtr))      // Assigning FreeVars to variables from the environment
    *ExpressionHeap                         // Initial expression heap
    *VarAlloc                               // Initial variable heap
    Expression                              // Default expression
    (Graph SuclSymbol SuclVariable)         // Case pattern to convert
    Level                                   // Level to assign to fresh free variables
    [FreeVar]                               // Accumulator for list of free variables in the function body (from function arguments and case pattern arguments)
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    [SuclVariable]                          // Subsequent variables in pattern to match
 -> ( *ExpressionHeap                       // Modified expression heap
    , *VarAlloc                             // Modified variable heap
    , Expression                            // Resulting (case) expression
    , Int                                   // Modified reference count to default expression
    , [FreeVar]                             // List of free variables in the function body (from function arguments and case pattern arguments)
    , [FreeVar]                             // List of local variables in the function body (from lets)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_matchpatterns getconsdef build_casebranch patnodes varenv exprheap0 varalloc0 default_expression pgraph level freevars0 localvars0 eips0 []
= (exprheap1,varalloc1,case_expression,refcount,freevars1,localvars1,eips1)
  where (exprheap1,varalloc1,case_expression,refcount,freevars1,localvars1,eips1)
        = build_casebranch level patnodes varenv freevars0 localvars0 eips0 exprheap0 varalloc0

convert_matchpatterns getconsdef build_casebranch0 patnodes0 varenv0 exprheap0 varalloc0 default_expression pgraph level freevars0 localvars0 eips0 [pnode:pnodes]
| pdef
  = convert_matchpattern getconsdef build_remaining_matcher patnodes0 varenv0 exprheap0 varalloc0 default_expression pgraph level pnode psym freevars0 localvars0 eips0 pargs
= build_remaining_matcher level patnodes0 varenv0 freevars0 localvars0 eips0 exprheap0 varalloc0
  where (pdef,(psym,pargs)) = varcontents pgraph pnode
        build_remaining_matcher level` patnodes` varenv` freevars` localvars` eips` exprheap` varalloc`
        = convert_matchpatterns getconsdef build_casebranch0 patnodes` varenv` exprheap` varalloc` default_expression pgraph level` freevars` localvars` eips` pnodes

convert_matchpattern ::
    ((Global Index) -> ConsDef)             // Get ConsDef from environment
    (  Level                                // Level to assign to free variables
       [SuclVariable]                       // List of pattern nodes
       (SuclVariable->(Ident,VarInfoPtr))   // Assigning FreeVars to variables from the environment
       [FreeVar]                            // Accumulator for list of free variables in the function body (from function arguments and case pattern arguments)
       [FreeVar]                            // Accumulator for list of local variables in the function body (from lets)
       [ExprInfoPtr]                        // Accumulator for list of expression pointers from the function body
       *ExpressionHeap                      // Initial expression heap for case branch
    ->*(  *VarAlloc                         // Initial variable heap for case branch
       -> ( *ExpressionHeap                 // Modified expression heap from case branch
          , *VarAlloc                       // Modified variable heap from case branch
          , Expression                      // Resulting branch expression
          , Int                             // Reference count to default expression
          , [FreeVar]                       // List of free variables in the function body (from function arguments and case pattern arguments)
          , [FreeVar]                       // List of local variables in the function body (from lets)
          , [ExprInfoPtr]                   // List of expression pointers from the function body
          )
       )
    )
    [SuclVariable]                          // List of pattern nodes
    (SuclVariable->(Ident,VarInfoPtr))      // Assigning FreeVars to variables from the environment
    *ExpressionHeap                         // Initial expression heap
    *VarAlloc                               // Initial variable heap
    Expression                              // Default expression
    (Graph SuclSymbol SuclVariable)         // Case pattern to convert
    Level                                   // Level to assign to fresh free variables
    SuclVariable
    SuclSymbol
    [FreeVar]                               // Accumulator for list of free variables in the function body (from function arguments and case pattern arguments)
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    [SuclVariable]                          // Subsequent variables in pattern to match
 -> ( *ExpressionHeap                       // Modified expression heap
    , *VarAlloc                             // Modified variable heap
    , Expression                            // Resulting (case) expression
    , Int                                   // Modified reference count to default expression
    , [FreeVar]                             // List of free variables in the function body (from function arguments and case pattern arguments)
    , [FreeVar]                             // List of local variables in the function body (from lets)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_matchpattern getconsdef build_casebranch patnodes0 varenv0 exprheap0 varalloc0 default_expression pgraph level pnode psym freevars0 localvars0 eips0 pargs
= (exprheap3,varalloc2,case_expression,1+refcount,freevars++freevars1,localvars1,[cip,bvip:eips1])
  where (exprheap3,varalloc2,branch_expression,refcount,freevars1,localvars1,eips1)
        = convert_matchpatterns getconsdef build_casebranch patnodes1 varenv1 exprheap2 varalloc1 default_expression pgraph (level+1) freevars0 localvars0 eips0 pargs
        (cip,exprheap1) = newPtr EI_Empty exprheap0
        (bvip,exprheap2) = newPtr EI_Empty exprheap1
        case_expression = Case ci
        ci
        = { case_expr = Var (mkboundvar bvip (varenv0 pnode))
          , case_guards = cps
          , case_default = Yes default_expression
          , case_ident = No
          , case_info_ptr = cip
          , case_default_pos = NoPos
          }
        cps = convert_constructor getconsdef psym freevars branch_expression
        (varenv1,varalloc1)
        = allocate_freevars "_parg" varenv0 varalloc0 pargs
        patnodes1 = pargs++patnodes0
        freevars = map (mkfreevar level o varenv1) pargs

allocate_freevars ::
    {#.Char}
    (SuclVariable->(Ident,VarInfoPtr))
    *VarAlloc
    .[SuclVariable]
 -> ( (SuclVariable->(Ident,VarInfoPtr))
    , .VarAlloc
    )

allocate_freevars prefix varenv0 varalloc0 []
= (varenv0,varalloc0)
allocate_freevars prefix varenv0 varalloc0 [pnode:pnodes]
= (varenv2,varalloc2)
  where ((ident,varinfoptr),varalloc1) = newvar prefix varalloc0
        (varenv1,varalloc2)
        = allocate_freevars prefix varenv0 varalloc1 pnodes
        varenv2 = adjust pnode (ident,varinfoptr) varenv1

convert_constructor :: ((Global Index) -> ConsDef) SuclSymbol [FreeVar] Expression -> CasePatterns
convert_constructor getconsdef (SuclInt    i) [] expr = mkbps BT_Int    (BVI (toString i)) expr
convert_constructor getconsdef (SuclChar   c) [] expr = mkbps BT_Char   (BVC (toString c)) expr
convert_constructor getconsdef (SuclReal   r) [] expr = mkbps BT_Real   (BVR (toString r)) expr
convert_constructor getconsdef (SuclBool   b) [] expr = mkbps BT_Bool   (BVB           b ) expr
convert_constructor getconsdef (SuclString s) [] expr = mkbps (BT_String notype) (BVS s) expr where notype = mstub "convert_constructor" "no argument for basic string type"
convert_constructor getconsdef (SuclUser (SK_Constructor consindex)) freevars expr
= AlgebraicPatterns typedefindex [ap]
    ---> ("convert.convert_constructor",typedefindex,ap)
  where typedefindex = {glob_module=consmodule,glob_object=consdef.cons_type_index ---> "want consdef.cons_type_index"}
        consmodule = consindex.glob_module ---> "want consmodule"
        consdef = getconsdef consindex ---> ("convert.convert_constructor.getconsdef",consindex)
        defsymb
        = { ds_ident = consdef.cons_symb ---> ("convert.convert_constructor.consdef.cons_symb",consdef)
          , ds_arity = consdef.cons_type.st_arity ---> ("convert.convert_constructor.consdef.cons_type.st_arity",consdef)
          , ds_index = consindex.glob_object ---> (">>>convert.convert_constructor.consdef.cons_index",consindex,consdef,consdef.cons_index)
          }
        globdefsymb
        = { glob_module = consmodule ---> "want globdefsymb.glob_module"
          , glob_object = defsymb
          }
        ap
        = { ap_symbol   = globdefsymb ---> ("convert.convert_constructor.SK_Constructor.globdefsymb",globdefsymb)
          , ap_vars     = freevars ---> "want ap.ap_vars"
          , ap_expr     = expr ---> "want ap.ap_expr"
          , ap_position = NoPos ---> "want ap.ap_position"
          }
convert_constructor _ _ _ _
= mstub "convert_constructor" "unexpected SUCL pattern form"

mkbps bt bv expr
= BasicPatterns bt [bp]
  where bp
        = { bp_value = bv
          , bp_expr  = expr
          , bp_position = NoPos
          }

/*

Converting a function body:

 Take a heap of ExprInfo (for some expression forms)
 Return reduced heap of ExprInfo
 Take a level for fresh free variables for case patterns

 For the leaf graphs:
     Take a list of encountered variables with usage counts
     Return extended list of encountered variables with their usage counts
     Take a sharing indication function
     Take list of let-bindings for shared variables
     Return extended list of let-bindings for shared variables
     Take complete list of let-bindings
     Take mapping from free variables to freevars
     Take a heap of ExprInfo (for some expression forms)
     Return reduced heap of ExprInfo
     Return main expression

*/

:: ReferenceMaker :== (SuclVariable,*ExpressionHeap) -> (Expression,.ExpressionHeap)
:: ExpressionMaker :== SuclVariable -> Expression

convert_graph stringtype patnodes mkexpr0 level srgraph varalloc0 exprheap0 freevars0 localvars0 eips0
= (exprheap3,varalloc1,expression,freevars0,localvars1,eips3)
  where (exprheap2,eips1,refcount,closeds,_,mkexpr1)
        = (convert_graph_node--->"convert.convert_graph_node begins from convert.convert_graph") stringtype mkexpr (sgraph--->srgraph) exprheap1 eips0 patnodes (const 0) [] mkexpr0 sroot
        sgraph = rgraphgraph srgraph; sroot = rgraphroot srgraph
        shareds = [(closed,n) \\ closed<-closeds, n<-[refcount closed] | n>1]
        (mkexpr,letbinds,varalloc1,exprheap3,localvars1,eips2)
        = foldr (allocate_shared_variable level) (mkexpr1,[],varalloc0,exprheap2,localvars0,eips1) shareds
        root_expression = mkexpr sroot
        (expression,exprheap1,eips3) = mkletexpr letbinds root_expression exprheap0 eips2

mkletexpr letbinds letbody exprheap0 eips0
| isEmpty letbinds
  = (letbody,exprheap0,eips0)
= (letexpr,exprheap1,[letinfoptr:eips0])
  where letexpr
        = Let letinfo
        letinfo
        = { let_strict_binds = []
          , let_lazy_binds = letbinds
          , let_expr = letbody
          , let_info_ptr = letinfoptr
          , let_expr_position = NoPos
          }
        (letinfoptr,exprheap1) = newPtr EI_Empty exprheap0

allocate_shared_variable level (pnode,refcount) (mkexpr,letbinds,varalloc0,exprheap0,localvars0,eips0)
= (adjust pnode (Var boundvar) mkexpr,[letbind:letbinds],varalloc1,exprheap1,[freevar:localvars0],[exprinfoptr:eips0])
  where boundvar
        = { var_name = ident
          , var_info_ptr = varinfoptr
          , var_expr_ptr = exprinfoptr
          }
        letbind
        = { lb_dst = freevar
          , lb_src = mkexpr pnode
          , lb_position = NoPos
          }
        freevar
        = { fv_def_level = level
          , fv_name = ident
          , fv_info_ptr = varinfoptr
          , fv_count = refcount
          }
        ((ident,varinfoptr),varalloc1) = newvar "_share" varalloc0
        (exprinfoptr,exprheap1) = newPtr EI_Empty exprheap0

convert_graph_nodes ::
    PredefinedSymbol                // Compiler-predefined String symbol
    ExpressionMaker                 // Final expression maker
    (Graph SuclSymbol SuclVariable) // Subject graph to transform
    *ExpressionHeap                 // Input expression heap for generated expressions
    [ExprInfoPtr]                   // List of generated expression info's (accumulator input)
    u:[SuclVariable]                // Input list of seen nodes
    (SuclVariable->Int)             // Input reference count
    v:[SuclVariable]                // Input defined nodes
    ExpressionMaker                 // Input expression maker
    [SuclVariable]                  // Nodes to examine
 -> ( *ExpressionHeap               // Resulting expression heap
    , [ExprInfoPtr]                 // List of generated expression info's
    , SuclVariable->Int             // Output reference count
    , v:[SuclVariable]              // Output defined nodes
    , u:[SuclVariable]              // Output list of seen nodes
    , ExpressionMaker               // Output expression maker
    )

convert_graph_nodes stringtype mkexpr sgraph exprheap0 eips0 seen0 refcount0 closeds0 mkexpr0 []
= (exprheap0,eips0,refcount0,closeds0,seen0,mkexpr0) <--- "convert.convert_graph_nodes ends ([])"
convert_graph_nodes stringtype mkexpr sgraph exprheap0 eips0 seen0 refcount0 closeds0 mkexpr0 [snode:snodes]
= (exprheap2,eips2,refcount3,closeds2,seen2,mkexpr2) <--- "convert.convert_graph_nodes ends ([_:_])"
  where (exprheap2,eips2,refcount1,closeds1,seen2,mkexpr1)
        = (convert_graph_nodes--->"convert.convert_graph_nodes begins from convert.convert_graph_nodes") stringtype mkexpr sgraph exprheap1 eips1 seen1 refcount0 closeds0 mkexpr0 snodes
        (exprheap1,eips1,refcount2,closeds2,seen1,mkexpr2)
        = (convert_graph_node--->"convert.convert_graph_node begins from convert.convert_graph_nodes") stringtype mkexpr sgraph exprheap0 eips0 seen0 refcount1 closeds1 mkexpr1 snode
        refcount3 = inccounter snode refcount2

convert_graph_node ::
    PredefinedSymbol                // Compiler-predefined String symbol
    ExpressionMaker                 // Final expression builder
    (Graph SuclSymbol SuclVariable) // Graph to convert
    *ExpressionHeap                 // Heap from which to allocate new expression info
    [ExprInfoPtr]                   // List of generated expression info's (accumulator input)
    u:[SuclVariable]                // Already encountered nodes
    (SuclVariable->Int)             // Input reference count
    v:[SuclVariable]                // Input closed variables
    ExpressionMaker                 // Input expression builder
    SuclVariable                    // Node in graph to convert
 -> ( *ExpressionHeap               // Modified expression heap
    , [ExprInfoPtr]                 // List of generated expression info's
    , SuclVariable -> Int           // Output reference count
    , v:[SuclVariable]              // Output closed variables
    , u:[SuclVariable]              // Output seen variables
    , ExpressionMaker               // Output expression builder
    )

convert_graph_node stringtype mkexpr sgraph exprheap0 eips0 seen0 refcount0 closeds0 mkexpr0 snode
| isMember snode seen0
  = (exprheap0,eips0,refcount0,closeds0,seen0,mkexpr0) <--- "convert.convert_graph_node ends (already seen)"
= (exprheap2,eips2,refcount1,closeds2,seen2,mkexpr2) <--- "convert.convert_graph_node ends (new node)"
  where seen1 = [snode:seen0]
        (_,(ssym,sargs)) = dnc toString sgraph snode  // Must be closed; open nodes already initially in "seen"
        (expr,exprheap1,eips1)
        = convert_graph_symbol stringtype ((ssym<---"convert.convert_graph_node.ssym ends")--->"convert.convert_graph_node.ssym begins from convert.convert_graph_node") (map mkexpr ((sargs<---"convert.convert_graph_node.sargs ends")--->"convert.convert_graph_node.sargs begins from convert.convert_graph_node (convert_graph_symbol)")) exprheap0 eips0
        (exprheap2,eips2,refcount1,closeds1,seen2,mkexpr1)
        = (convert_graph_nodes--->"convert.convert_graph_nodes begins from convert.convert_graph_node") stringtype mkexpr sgraph exprheap1 eips1 seen1 refcount0 closeds0 mkexpr0 ((sargs<---"convert.convert_graph_node.sargs ends")--->"convert.convert_graph_node.sargs begins from convert.convert_graph_node (convert_graph_nodes)")
        mkexpr2 = adjust snode expr mkexpr1
        closeds2 = [snode:closeds1]

convert_graph_symbol ::
    PredefinedSymbol
    !SuclSymbol
    [Expression]
    *ExpressionHeap
    [ExprInfoPtr]
 -> ( Expression
    , *ExpressionHeap
    , [ExprInfoPtr]
    )

convert_graph_symbol stringtype (SuclInt    i) [] exprheap eips = (BasicExpr (BVI (toString i)) BT_Int   ,exprheap,eips)
convert_graph_symbol stringtype (SuclChar   c) [] exprheap eips = (BasicExpr (BVC (toString c)) BT_Char  ,exprheap,eips)
convert_graph_symbol stringtype (SuclReal   r) [] exprheap eips = (BasicExpr (BVR (toString r)) BT_Real  ,exprheap,eips)
convert_graph_symbol stringtype (SuclBool   b) [] exprheap eips = (BasicExpr (BVB           b ) BT_Bool  ,exprheap,eips)
convert_graph_symbol stringtype (SuclString s) [] exprheap eips = (makeStringExpr stringtype s           ,exprheap,eips)
convert_graph_symbol stringtype (SuclApply arity) [argexpr:argexprs] exprheap eips = (argexpr @ argexprs,exprheap,eips)
convert_graph_symbol stringtype (SuclUser symbkind) argexprs exprheap0 eips0
= (App app,exprheap1,[appinfoptr:eips0])
  where app
        = { app_symb = symbident
          , app_args = argexprs
          , app_info_ptr = appinfoptr
          }
        symbident
        = { symb_name = ident
          , symb_kind = symbkind
          , symb_arity = length argexprs    // FIXME: Can this be different from the actual number of function arguments?
          }
        ident
        = { id_name = "_anonymous_sucl_generated_function"
          , id_info = nilPtr
          }
        (appinfoptr,exprheap1) = newPtr EI_Empty exprheap0
convert_graph_symbol _ _ _ exprheap eips = (mstub "convert_graph_symbol" "unexpected application form in graph node",exprheap,eips)

// Magic from Artem
makeStringExpr :: !PredefinedSymbol String -> Expression
makeStringExpr stringtype str
= BasicExpr (BVS str) (BT_String (TA type_symb []))
  where {pds_ident, pds_module, pds_def} = stringtype
        type_symb = MakeTypeSymbIdent { glob_module = pds_module, glob_object = pds_def } pds_ident 0

mkbe bv bt = BasicExpr bv bt

//collect_calls :: Int FunctionBody -> [FunCall]
collect_calls main_dcl_module_n (TransformedBody tb)
= foldr (addfuncall main_dcl_module_n) [] symbidents
  where symbidents = collect_expr_calls tb.tb_rhs []
collect_calls _ _ = mstub "collect_calls" "unexpected FunctionBody form"

addfuncall main_dcl_module_n {symb_kind=SK_Function {glob_module=modindex,glob_object=funindex}} rest
| modindex == main_dcl_module_n
  = [{fc_level=NotALevel,fc_index=funindex}:rest]
addfuncall _ _ rest
= rest

//collect_expr_calls :: Expression [SymbIdent] -> [SymbIdent]
collect_expr_calls (App app) rest = [app.app_symb:foldr collect_expr_calls rest app.app_args]
collect_expr_calls (expr@exprs) rest = collect_expr_calls expr (foldr collect_expr_calls rest exprs)
collect_expr_calls (Let li) rest = collect_expr_calls li.let_expr (foldr collect_letbind_calls (foldr collect_letbind_calls rest li.let_lazy_binds) li.let_strict_binds)
collect_expr_calls (Case ci) rest = collect_expr_calls ci.case_expr (collect_casepatterns_calls ci.case_guards (foldoptional id collect_expr_calls ci.case_default rest))
collect_expr_calls (Selection optgd expr sels) rest = collect_expr_calls expr (foldr collect_sel_calls rest sels)
collect_expr_calls (Update expr1 sels expr2) rest = collect_expr_calls expr1 (foldr collect_sel_calls (collect_expr_calls expr2 rest) sels)
collect_expr_calls (RecordUpdate gds expr binds) rest = collect_expr_calls expr (foldr collect_bind_calls rest binds)
collect_expr_calls (TupleSelect ds i expr) rest = collect_expr_calls expr rest
//collect_expr_calls (Lambda fvs expr) rest = collect_expr_calls expr rest
collect_expr_calls (Conditional cond) rest = collect_expr_calls cond.if_cond (collect_expr_calls cond.if_then (foldoptional id collect_expr_calls cond.if_else rest))
collect_expr_calls (MatchExpr ogds gds expr) rest = collect_expr_calls expr rest
collect_expr_calls (DynamicExpr dyn) rest = collect_expr_calls dyn.dyn_expr (collect_tce_calls dyn.dyn_type_code rest)
//collect_expr_calls (TypeCase tc) rest = collect_expr_calls tc.type_case_dynamic (foldr collect_dp_calls (foldoptional id collect_expr_calls rest) tc.type_case_patterns)
collect_expr_calls (TypeCodeExpression tce) rest = collect_tce_calls tce rest
collect_expr_calls _ rest = rest

collect_letbind_calls lb rest = collect_expr_calls lb.lb_src rest

collect_casepatterns_calls (AlgebraicPatterns gi aps) rest = foldr collect_ap_calls rest aps
collect_casepatterns_calls (BasicPatterns gi bps) rest = foldr collect_bp_calls rest bps
collect_casepatterns_calls (DynamicPatterns dps) rest = foldr collect_dp_calls rest dps
collect_casepatterns_calls NoPattern rest = rest

collect_ap_calls ap rest = collect_expr_calls ap.ap_expr rest
collect_bp_calls bp rest = collect_expr_calls bp.bp_expr rest
collect_dp_calls dp rest = collect_tce_calls dp.dp_type_code (collect_expr_calls dp.dp_rhs rest)

collect_sel_calls (RecordSelection gds i) rest = rest
collect_sel_calls (ArraySelection gds eip expr) rest = collect_expr_calls expr rest
collect_sel_calls (DictionarySelection bv sels sip expr) rest = foldr collect_sel_calls (collect_expr_calls expr rest) sels

collect_bind_calls b rest = collect_expr_calls b.bind_src rest

collect_tce_calls (TCE_Constructor i tces) rest = foldr collect_tce_calls rest tces
collect_tce_calls (TCE_Selector sels vip) rest = foldr collect_sel_calls rest sels
collect_tce_calls _ rest = rest

fold_funcbody ::
    ((Rgraph sym var) .result .result -> .result)
    ((Rgraph sym var) -> .result)
    !.(FuncBody sym var)
 -> .result

fold_funcbody matchpattern buildgraph funcbody
= fold funcbody
  where fold (MatchPattern pattern yesbody nobody) = matchpattern pattern (fold yesbody) (fold nobody)
        fold (BuildGraph expression) = buildgraph expression

showfundefs :: (*File,*{#FunDef}) -> (.File,.{#FunDef})
showfundefs filefundefs
= foldlarrayindex f filefundefs
  where f file index fundef
        = file <<< "Function #" <<< toString index <<< nl
               <<< fundef <<< nl

instance <<< DefinedSymbol
where (<<<) file {ds_ident,ds_arity,ds_index}
      = file <<< "{ds_ident=" <<< ds_ident <<< ",ds_arity=" <<< ds_arity <<< ",ds_index=" <<< ds_index <<< "}"

instance <<< AlgebraicPattern
where (<<<) file {ap_symbol,ap_vars,ap_expr,ap_position}
      = file <<< "{ap_symbol=" <<< ap_symbol <<< ",ap_vars=" <<< ap_vars <<< ",ap_expr=" <<< ap_expr <<< ",ap_position=" <<< ap_position <<< "}"
