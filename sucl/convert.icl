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
 = fundefs2
   where globals1 = filter (not o flip isMember (map snd bindings)) globals0
         fundefs2
         = if usedfunsym
              fundefs1
              [(funsym,(length args,[mkrule (map snd bindings) (hd rest) (compilegraph nodes0)])):fundefs1]
         (_,(nodes0,fundefs1,globals0,rest,usedfunsym))
          = (convert_expression--->"convert.convert_expression begins from convert.convert_transformedbody") main_dcl_module_n (Yes (funsym,args)) bindings expression (heap0,([],fundefs0,[],[],False))
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
         , Bool                                 // Whether top level info was reused (ignored on input)
         )
       )

convert_expressions main_dcl_module_n bounds exprs lrinfo
 = (foldlr ((convert_expression--->"convert.convert_expression begins from convert_expressions") main_dcl_module_n No bounds) (heap0,(nodes0,fundefs0,globals0,[],False)) exprs <--- "convert.convert_expressions ends") ---> "convert.convert_expressions begins"
   where (heap0,(nodes0,fundefs0,globals0)) = lrinfo

convert_expression ::
    Int                                         // Index of current DCL module
    (Optional (SuclSymbol,[FreeVar]))           // Arguments and function symbol to use (to prevent lifted top-level cases)
    [(VarInfoPtr,SuclVariable)]                 // Variables bound in the environment
    Expression                                  // Expression to convert
    Econv_state                                 // Input expression conversion state
 -> Econv_state                                 // Resulting expression conversion state

convert_expression main_dcl_module_n topinfo bindings (Var varinfo) lrinfo
= (heap0,(nodes0,fundefs0,globals1,rest`,False))
  where (globals1,rest`) = foldmap bound free bindings vip
        bound node = ([node:globals0],[node:rest])
        free
        = (globals0,[nonode:rest])
          where nonode = abort ("convert.convert_expression.Var: expression contains free variable: "+++toString varinfo.var_info_ptr)
        vip = varinfo.var_info_ptr
        (heap0,(nodes0,fundefs0,globals0,rest,_)) = lrinfo

convert_expression main_dcl_module_n topinfo bindings (App appinfo) lrinfo
= (heap2,(nodes2,fundefs1,globals1,[root:rest],False)) <--- "convert.convert_expression ends (for App expression)"
  where [root:heap1] = heap0
        (heap2,(nodes1,fundefs1,globals1,args0,_))
        = convert_expressions main_dcl_module_n bindings appinfo.app_args (heap1,(nodes0,fundefs0,globals0))
        nodes2 = [(root,(SuclUser appinfo.app_symb.symb_kind,args0)):nodes1]
        (heap0,(nodes0,fundefs0,globals0,rest,_)) = lrinfo

convert_expression main_dcl_module_n topinfo bounds (expr @ exprs) lrinfo
= (heap2,(nodes2,fundefs1,globals1,[root:rest],False)) <--- "convert.convert_expression ends (for (@) expression)"
  where [root:heap1] = heap0
        (heap2,(nodes1,fundefs1,globals1,args0,_))
         = convert_expressions main_dcl_module_n bounds [expr:exprs] (heap1,(nodes0,fundefs0,globals0))
        nodes2 = [(root,(SuclApply (length exprs),args0)):nodes1]
        (heap0,(nodes0,fundefs0,globals0,rest,_)) = lrinfo

convert_expression main_dcl_module_n topinfo bindings0 (Let letinfo) lrinfo
| not (isEmpty (letinfo.let_strict_binds))
  = mstub "convert_expression/Let" "cannot handle strict lets"
= (heap2,(nodes2,fundefs2,globals3,rest`,False)) <--- "convert.convert_expression ends (for Let expression)"
  where globals3 = filter (not o flip isMember (map snd bindings1)) globals2
        (heap2,(nodes2,fundefs2,globals2,rest`,_)) = convert_expression main_dcl_module_n No bindings1 letinfo.let_expr (heap1,(nodes1,fundefs1,globals1,rest,False))
        (heap1,(nodes1,fundefs1,globals1,suclbounds,_)) = convert_expressions main_dcl_module_n bindings1 [lb.lb_src \\ lb<-letinfo.let_lazy_binds] (heap0,(nodes0,fundefs0,globals0))
        bindings1 = zip2 boundvars suclbounds++bindings0
        boundvars = [lb.lb_dst.fv_info_ptr \\ lb<-letinfo.let_lazy_binds]
        (heap0,(nodes0,fundefs0,globals0,rest,_)) = lrinfo

convert_expression main_dcl_module_n (Yes (introduced_function_symbol,funargs)) bindings (Case caseinfo=:{case_expr=Var selvar}) lrinfo
= (heap4,(nodes9,fundefs9,globals9,[root:rest],True)) <--- "convert.convert_expression ends (for Case expression/Yes)"
  where // Plan: (0.5) convert selector
        //       (1) convert branches
        //       (1.5) convert default if present
        //       (2) build rules/fundef from branches
        //       (4) build closure node
        // (4) Build closure node
        closureargs = (map fv2sucl funargs <--- ("convert.convert_expression.Case.closureargs ends with "+++toString (length innerglobals1)+++" inner global(s), "+++toString (length defaultroots)+++" default root(s), and "+++toString (length selectorroots)+++" selector root")) ---> "convert.convert_expression.Case.closureargs begins"
        fv2sucl fv = lookup bindings fv.fv_info_ptr
        nodes9 = [(root,(introduced_function_symbol,closureargs)):nodes8]
        // (2) build rules/fundef from branches
        fundefs9
        = [(introduced_function_symbol,(length closureargs,map mkalt alternatives++map mkdefaultalt defaultroots)):fundefs8]
           where mkalt (patroot,reproot,nodes)
                  = mkrule closureargs reproot (compilegraph nodes)
                 mkdefaultalt defaultroot
                  = mkrule closureargs defaultroot emptygraph
        // (1.5) convert default if necessary
        (heap4,(nodes7,fundefs6,globals7,defaultroots,_))
         = foldoptional id ((convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case default)") main_dcl_module_n No bindings) caseinfo.case_default (heap3,(nodes6,fundefs5,globals6,[],False))
        // (1) convert branches
        globals8 = innerglobals1++globals7
        innerglobals1 = removeDup innerglobals0
        (heap3,(innerglobals0,fundefs7,alternatives))
         = case caseinfo.case_guards
           of AlgebraicPatterns _ branches
               -> foldlr (convert_algebraic_branch main_dcl_module_n patroot bindings) (heap2,([],fundefs6,[])) branches
              BasicPatterns _ branches
               -> foldlr (convert_basic_branch main_dcl_module_n patroot bindings) (heap2,([],fundefs6,[])) branches
              _
               -> (heap2,([],fundefs6,error "convert: convert_expression: unhandled CasePatterns constructor"))
        patroot = lookup bindings selvar.var_info_ptr
        // (0.5) Convert selector
        (heap2,(nodes8,fundefs8,globals9,selectorroots,_))
         = (convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case selector)") main_dcl_module_n No bindings caseinfo.case_expr (heap1,(nodes7,fundefs7,globals8,[],False))
        // (0) Claim root node
        [root:heap1] = heap0
        (heap0,(nodes6,fundefs5,globals6,rest,_)) = lrinfo

convert_expression main_dcl_module_n No bindings (Case caseinfo) lrinfo
= (heap4,(nodes9,fundefs9,globals9,[root:rest],False)) <--- "convert.convert_expression ends (for Case expression/No)"
  where // Plan: (0.5) convert selector
        //       (1) convert branches
        //       (1.5) convert default if present
        //       (2) build rules/fundef from branches
        //       (4) build closure node
        // (4) Build closure node
        closureargs = ((selectorroots++innerglobals1++defaultroots) <--- ("convert.convert_expression.Case.closureargs ends with "+++toString (length innerglobals1)+++" inner global(s), "+++toString (length defaultroots)+++" default root(s), and "+++toString (length selectorroots)+++" selector root")) ---> "convert.convert_expression.Case.closureargs begins"
        nodes9 = [(root,(introduced_function_symbol,closureargs)):nodes8]
        // (2) build rules/fundef from branches
        fundefs9
        = [(introduced_function_symbol,(length closureargs,map mkalt alternatives++map mkdefaultalt defaultroots)):fundefs8]
           where mkalt (patroot,reproot,nodes)
                  = mkrule ([patroot:innerglobals1++defaultroots]) reproot (compilegraph nodes)
                 mkdefaultalt defaultroot
                  = mkrule (selectorroots++innerglobals1++defaultroots) defaultroot emptygraph
        introduced_function_symbol = SuclCase caseinfo.case_info_ptr
        // (1.5) convert default if necessary
        (heap4,(nodes7,fundefs6,globals7,defaultroots,_))
         = foldoptional id ((convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case default)") main_dcl_module_n No bindings) caseinfo.case_default (heap3,(nodes6,fundefs5,globals6,[],False))
        // (1) convert branches
        globals8 = innerglobals1++globals7
        innerglobals1 = removeDup innerglobals0
        (heap3,(innerglobals0,fundefs7,alternatives))
         = case caseinfo.case_guards
           of AlgebraicPatterns _ branches
               -> foldlr (convert_algebraic_branch main_dcl_module_n patroot bindings) (heap25,([],fundefs6,[])) branches
              BasicPatterns _ branches
               -> foldlr (convert_basic_branch main_dcl_module_n patroot bindings) (heap25,([],fundefs6,[])) branches
              _
               -> (heap25,([],fundefs6,error "convert: convert_expression: unhandled CasePatterns constructor"))
        [patroot:heap25] = heap2
        // (0.5) Convert selector
        (heap2,(nodes8,fundefs8,globals9,selectorroots,_))
         = (convert_expression--->"convert.convert_expression begins from convert.convert_expression (Case selector)") main_dcl_module_n No bindings caseinfo.case_expr (heap1,(nodes7,fundefs7,globals8,[],False))
        // (0) Claim root node
        [root:heap1] = heap0
        (heap0,(nodes6,fundefs5,globals6,rest,_)) = lrinfo

convert_expression main_dcl_module_n topinfo bindings (BasicExpr bv bt) lrinfo
= (heap1,(nodes1,fundefs0,globals0,[root:rest],False)) <--- "convert.convert_expression ends (for BasicExpr expression)"
  where [root:heap1] = heap0
        nodes1 = [(root,(convert_bvalue bv,[])):nodes0]
        (heap0,(nodes0,fundefs0,globals0,rest,_)) = lrinfo

convert_expression _ _ _ (Selection _ _ _)      _ = mstub "convert_expression" "Selection constructor not handled"
convert_expression _ _ _ (Update _ _ _)         _ = mstub "convert_expression" "Update not handled"
convert_expression _ _ _ (RecordUpdate _ _ _)   _ = mstub "convert_expression" "RecordUpdate constructor not handled"
convert_expression _ _ _ (TupleSelect _ _ _)    _ = mstub "convert_expression" "TupleSelect constructor not handled"
convert_expression _ _ _ (WildCard)             _ = mstub "convert_expression" "WildCard constructor not handled"
convert_expression _ _ _ (AnyCodeExpr _ _ _)    _ = mstub "convert_expression" "AnyCodeExpr constructor not handled"
convert_expression _ _ _ (ABCCodeExpr _ _)      _ = mstub "convert_expression" "ABCCodeExpr constructor not handled"
convert_expression _ _ _ (MatchExpr _ _ _)      _ = mstub "convert_expression" "MatchExpr constructor not handled"
convert_expression _ _ _ (FreeVar _)            _ = mstub "convert_expression" "FreeVar constructor not handled"
convert_expression _ _ _ (Constant _ _ _ _)     _ = mstub "convert_expression" "Constant constructor not handled"
convert_expression _ _ _ (ClassVariable _)      _ = mstub "convert_expression" "ClassVariable constructor not handled"
convert_expression _ _ _ (DynamicExpr _)        _ = mstub "convert_expression" "DynamicExpr constructor not handled"
convert_expression _ _ _ (TypeCodeExpression _) _ = mstub "convert_expression" "TypeCodeExpression constructor not handled"
convert_expression _ _ _ (EE)                   _ = mstub "convert_expression" "EE constructor not handled"
convert_expression _ _ _ (NoBind _)             _ = mstub "convert_expression" "NoBind constructor not handled"

convert_algebraic_branch ::
    Int
    SuclVariable                    // Root of pattern
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

convert_algebraic_branch main_dcl_module_n root bindings0 branch lrinfo
= (heap2,(globals2,fundefs1,alternatives1)) ---> ("convert.convert_algebraic_branch: binding variables: "+++listToString (map fst argmap))
  where // Unpack conversion state
        (heap0,(globals0,fundefs0,alternatives0)) = lrinfo
        // DON'T Claim root node of pattern
        heap1 = heap0
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
        (heap2,(nodes0,fundefs1,globals1,rest,_)) = (convert_expression--->"convert.convert_expression begins from convert_algebraic_branch") main_dcl_module_n No bindings1 branch.ap_expr (heap1,([],fundefs0,globals0,[],False))
        // Mask pattern's arguments from globals
        globals2 = filter (not o flip isMember (map snd argmap)) globals1
        // Create root of pattern,root of replacement, defined node of alternative
        alternatives1 = [(root,hd rest,nodes1):alternatives0]

convert_basic_branch ::
    Int
    SuclVariable                    // Root of pattern
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

convert_basic_branch main_dcl_module_n root bindings branch lrinfo
= (heap2,(globals1,fundefs1,alternatives1))
  where // Unpack conversion state
        (heap0,(globals0,fundefs0,alternatives0)) = lrinfo
        // DON'T Claim root node of pattern
        heap1 = heap0
        // Create pattern's root node definition
        nodes1 = [(root,(convert_bvalue branch.bp_value,[])):nodes0]
        // Convert branch expression
        (heap2,(nodes0,fundefs1,globals1,rest,_)) = (convert_expression--->"convert.convert_expression begins from convert.convert_basic_branch") main_dcl_module_n No bindings branch.bp_expr (heap1,([],fundefs0,globals0,[],False))
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
//  (SuclSymbol->(Ident,Int))   // Identifier and formal arity of symbol
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
        (exprheap1,varalloc1,suclinfo1,new_fundefs)
        = (store_newfuns--->"convert.store_newfuns begins from stc_funcdefs") stringtype suclinfo1 (getconsdef dcl_mods main_dcl_module_n icl_common) main_dcl_module_n firstnewindex exprheap0 varalloc0 srrs suclinfo0 (copy_oldfuns oldfundefs2 initialarray)
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
          , fi_free_vars   = []         // Variables bound outside function's scope (such functions must be lifted)
          , fi_local_vars  = []         // Variables bound in Case's and Let's
          , fi_dynamics    = []         // Expressions used in dynamics (?)
          , fi_properties  = 0
          }
        (n_oldfundefs,oldfundefs1) = usize oldfundefs0
        suclinfo0 = get_formal_name_and_arity {env_dcls=dcl_mods,env_main=main_dcl_module_n,env_getcommon=getcommon,env_infos=oldinfos}
        getcommon modindex = if (modindex==main_dcl_module_n) icl_common dcl_mods.[modindex].dcl_common
        (oldinfos,oldfundefs2) = get_infos oldfundefs1

get_infos :: u:{#FunDef} -> ({(Ident,Int)},v:{#FunDef}), [u<=v]
get_infos fundefs0
= copy_infos 0 ((createArray nfundefs (undef,undef)),fundefs1)
  where (nfundefs,fundefs1) = usize fundefs0

copy_infos n (infos,fundefs0)
| n<nfundefs
  = copy_infos (n+1) ({infos & [n]=(fun_symb,fun_arity)},fundefs2)
= (infos,fundefs1)
  where ({fun_symb,fun_arity},fundefs2) = fundefs1![n]
        (nfundefs,fundefs1) = usize fundefs0

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

store_newfuns stringtype suclinfo getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 [] suclinfo0 fundefs0
= (exprheap0,varalloc0,suclinfo0,fundefs0)<---"convert.store_newfuns ends (no more srrs)"
store_newfuns stringtype suclinfo getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 [srr:srrs] suclinfo0 fundefs0
= case srr.srr_assigned_symbol
  of (SuclUser newsk=:(SK_Function {glob_module=modi,glob_object=funindex}))
      | modi == main_dcl_module_n
        -> (store_newfuns--->"convert.store_newfuns begins from store_newfuns") stringtype suclinfo getconsdef main_dcl_module_n firstnewindex exprheap1 varalloc1 srrs suclinfo1 fundefs1<---"convert.store_newfuns ends (srr in main module)"
           where (exprheap1,varalloc1,funbody,localvars,_)
                 = stc_funcdef stringtype suclinfo getconsdef exprheap0 varalloc0 srr.srr_function_def
                 funinfo
                 = { fi_calls       = collect_calls main_dcl_module_n funbody ---> "convert.store_newfuns.SuclUser.funinfo requires fi_calls"
                   , fi_group_index = 0         ---> "convert.store_newfuns.SuclUser.funinfo requires fi_group_index"
                   , fi_def_level   = NotALevel ---> "convert.store_newfuns.SuclUser.funinfo requires fi_def_level"
                   , fi_free_vars   = []        ---> "convert.store_newfuns.SuclUser.funinfo requires fi_free_vars"
                   , fi_local_vars  = localvars ---> "convert.store_newfuns.SuclUser.funinfo requires fi_local_vars"
                   , fi_dynamics    = []        ---> "convert.store_newfuns.SuclUser.funinfo requires fi_dynamics"
                   , fi_properties  = 0         ---> "convert.store_newfuns.SuclUser.funinfo requires fi_properties"
                   }
                 fundefs1
                 = create_or_update_fundefs
                    (funindex--->("convert.create_or_update_fundefs requires funindex for "+++toString newsk))
                    (funbody--->("convert.create_or_update_fundefs requires funbody for "+++toString newsk))
                    (funinfo--->("convert.create_or_update_fundefs requires funinfo for "+++toString newsk))
                    (fundefs0--->("convert.create_or_update_fundefs requires fundefs0 for "+++toString newsk))
                 (create_or_update_fundefs,suclinfo1)
                 = if (funindex>=firstnewindex)
                      (create_fundef ident srr.srr_arity,adjust newsk (ident,srr.srr_arity) suclinfo0)
                      (update_fundef,suclinfo0)
                 ident
                 = { id_name = "_f"+++toString funindex
                   , id_info = nilPtr
                   }
     _
      -> (store_newfuns--->"convert.store_newfuns begins from store_newfuns") stringtype suclinfo getconsdef main_dcl_module_n firstnewindex exprheap0 varalloc0 srrs suclinfo0 fundefs0 <--- "convert.store_newfuns ends (srr in other module)"

create_fundef :: Ident .Int Int FunctionBody FunInfo *{#FunDef} -> .{#FunDef}
create_fundef ident arity funindex funbody funinfo fundefs
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

update_fundef :: .Int FunctionBody FunInfo *{#FunDef} -> .{#FunDef}
update_fundef index newbody newinfo oldfundefs
= ({tmpfundefs & [index] = newfundef} <--- ("convert.update_fundef "+++toString index+++" ends")) ---> ("convert.update_fundef "+++toString index+++" begins")
  where (oldfundef,tmpfundefs) = oldfundefs![index]
        newfundef = {oldfundef & fun_body = newbody, fun_info = newinfo}

stc_funcdef ::
    PredefinedSymbol                    // Compiler-predefined String symbol
    (SymbKind -> (Ident,Int))           // Identifer and formal arity of symbols
    ((Global Index) -> ConsDef)         // Get constructor definition from environment
    *ExpressionHeap                     // Fresh expression space
    *VarAlloc                           // Fresh variable space
    (FuncDef SuclSymbol SuclVariable)   // Function definition to convert
 -> ( *ExpressionHeap                   // Remaining expression space
    , *VarAlloc                         // Remaining variable space
    , FunctionBody                      // Converted function body
    , [FreeVar]                         // List of local variables in the function body (from lets and cases)
    , [ExprInfoPtr]                     // List of expression pointers from the function body
    )

// stc_funcdef stringtype getconsdef exprheap0 varalloc0 (args,body) = block "stc_funcdef"
stc_funcdef stringtype suclinfo getconsdef exprheap0 varalloc0 (args,body)
= (exprheap1,varalloc2,TransformedBody tb,/*tb.tb_args++*/(localvars--->"convert.stc_funcdef.localvars used"),eips)
    ---> "convert.stc_funcdef"
  where tb
        = { tb_args = map (mkfreevar 0 o varenv) args
          , tb_rhs  = expr
          }
        (exprheap1,varalloc2,expr,localvars,eips)
        = convert_funcbody stringtype suclinfo getconsdef 1 args varenv exprheap0 varalloc1 [] [] body
        (varenv,varalloc1)
        = allocate_vars "_farg" noexpr varalloc0 args
        noexpr = mstub "std_funcdef" "open variable in rhs but not lhs"

mkfreevar :: Level (Ident,VarInfoPtr) -> FreeVar
mkfreevar level identvarinfoptr
= freevar
    ---> ("convert.mkfreevar.freevar used",freevar)
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
    (SymbKind -> (Ident,Int))               // Identifer and formal arity of symbols
    ((Global Index) -> ConsDef)             // Get constructor definition from environment
    Level                                   // (Lexical?) level for new variables
    [SuclVariable]                          // Nodes from case variables in the environment
    (SuclVariable -> (Ident,VarInfoPtr))    // Mapping from free nodes to variables
    *ExpressionHeap                         // Fresh expression space
    *VarAlloc                               // Fresh variable space
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets and cases)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    !(FuncBody SuclSymbol SuclVariable)     // Function body to convert
 -> ( *ExpressionHeap                       // Modified expression space
    , *VarAlloc                             // Modified variable space
    , Expression                            // Resulting expression
    , [FreeVar]                             // List of local variables in the function body (from lets and cases)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_funcbody stringtype suclinfo getconsdef level patnodes varenv exprheap0 varalloc0 localvars0 eips0 (MatchPattern pattern yesbody nobody)
= (exprheap3,varalloc3,match_expression,localvars3,eips3)
    ---> ("convert.convert_funcbody localvars",default_freevar)
  where (exprheap3,([match_expression:_],eips1))
        = mk_match_expression (exprheap2,([],eips0))
        (exprheap2,varalloc3,match_failure_expression,localvars1,eips2)
        = convert_funcbody stringtype suclinfo getconsdef (level+1) patnodes varenv exprheap1 varalloc2 localvars0 eips1 nobody
        (exprheap1,varalloc1,case_expression,default_refcount,localvars2,eips3)
        = convert_matchpatterns getconsdef suclinfo build_casebranch patnodes varenv exprheap0 varalloc0 mk_default_expression pgraph level localvars1 eips2 [proot]

        pgraph = rgraphgraph pattern
        proot = rgraphroot pattern

        ((default_ident,default_info_ptr),varalloc2) = newvar "_default" varalloc1
        default_freevar
        = { fv_def_level=level
          , fv_name=default_ident
          , fv_info_ptr=default_info_ptr
          , fv_count=default_refcount
          }

        build_casebranch level` patnodes` varenv` localvars0` eips0` exprheap0` varalloc0`
        = (exprheap1`,varalloc1`,expr`,0--->("convert.convert_funcbody.build_casebranch.refcount=0"),localvars1`,eips1`)
          where (exprheap1`,varalloc1`,expr`,localvars1`,eips1`)
                = convert_funcbody stringtype suclinfo getconsdef level` patnodes` varenv` exprheap0` varalloc0` localvars0` eips0` yesbody

        (mk_default_expression,mk_match_expression,localvars3)
        = if (default_refcount==1)
             (mk_match_failure_expression,mk_case_expression,localvars2)
             (mk_match_failure_reference,mk_let_expression,[default_freevar:localvars2])

        mk_match_failure_expression (exprheap`0,(rest,eips`0))
        = (exprheap`0,([match_failure_expression:rest],eips`0))
        mk_case_expression (exprheap`0,(rest,eips`0))
        = (exprheap`0,([case_expression:rest],eips`0))

        mk_match_failure_reference (exprheap`0,(rest,eips`0))
        = (exprheap`1,([match_failure_reference:rest],eips`1))
          where match_failure_reference = Var default_boundvar
                default_boundvar
                = { var_name = default_ident
                  , var_info_ptr = default_info_ptr
                  , var_expr_ptr = default_expr_ptr
                  }
                (default_expr_ptr,exprheap`1) = newPtr EI_Empty exprheap`0
                eips`1 = [default_expr_ptr:eips`0]
        mk_let_expression (exprheap`0,(rest,eips`0))
        = (exprheap`1,([let_expression:rest],eips`1))
          where let_expression = Let li
                li
                = { let_strict_binds = []
                  , let_lazy_binds = [{lb_dst=default_freevar,lb_src=match_failure_expression,lb_position=NoPos}]
                  , let_expr = case_expression
                  , let_info_ptr = letinfoptr
                  , let_expr_position = NoPos
                  }
                (letinfoptr,exprheap`1) = newPtr EI_Empty exprheap`0
                eips`1 = [letinfoptr:eips`0]

convert_funcbody stringtype suclinfo getconsdef level patnodes varenv exprheap0 varalloc0 localvars0 eips0 (BuildGraph srgraph)
= new_convert_graph stringtype suclinfo patnodes varenv level srgraph varalloc0 exprheap0 localvars0 eips0

convert_matchpatterns ::
    ((Global Index) -> ConsDef)             // Get ConsDef from environment
    (SymbKind -> (Ident,Int))               // Identifer and formal arity of symbols
    (  Int                                  // Level to assign to free variables
       [SuclVariable]                       // List of pattern nodes
       (SuclVariable->(Ident,VarInfoPtr))   // Assigning FreeVars to variables from the environment
       [FreeVar]                            // Accumulator for list of local variables in the function body (from lets and cases)
       [ExprInfoPtr]                        // Accumulator for list of expression pointers from the function body
       *ExpressionHeap                      // Initial expression heap for case branch
    ->*(  *VarAlloc                         // Initial variable heap for case branch
       -> ( *ExpressionHeap                 // Modified expression heap from case branch
          , *VarAlloc                       // Modified variable heap from case branch
          , Expression                      // Resulting branch expression
          , Int                             // Reference count to default expression
          , [FreeVar]                       // List of local variables in the function body (from lets and cases)
          , [ExprInfoPtr]                   // List of expression pointers from the function body
          )
       )
    )
    [SuclVariable]                          // List of pattern nodes
    (SuclVariable->(Ident,VarInfoPtr))      // Assigning FreeVars to variables from the environment
    *ExpressionHeap                         // Initial expression heap
    *VarAlloc                               // Initial variable heap
    (  (*ExpressionHeap,([Expression],[ExprInfoPtr]))
    -> (*ExpressionHeap,([Expression],[ExprInfoPtr]))
    )                                       // Default expression builder
    (Graph SuclSymbol SuclVariable)         // Case pattern to convert
    Level                                   // Level to assign to fresh free variables
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets and cases)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    [SuclVariable]                          // Subsequent variables in pattern to match
 -> ( *ExpressionHeap                       // Modified expression heap
    , *VarAlloc                             // Modified variable heap
    , Expression                            // Resulting (case) expression
    , Int                                   // Modified reference count to default expression
    , [FreeVar]                             // List of local variables in the function body (from lets and cases)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_matchpatterns getconsdef suclinfo build_casebranch patnodes varenv exprheap0 varalloc0 mk_default_expression pgraph level localvars0 eips0 []
= (exprheap1,varalloc1,case_expression,refcount,localvars1,eips1)
  where (exprheap1,varalloc1,case_expression,refcount,localvars1,eips1)
        = build_casebranch level patnodes varenv localvars0 eips0 exprheap0 varalloc0

convert_matchpatterns getconsdef suclinfo build_casebranch0 patnodes0 varenv0 exprheap0 varalloc0 mk_default_expression pgraph level localvars0 eips0 [pnode:pnodes]
| pdef
  = convert_matchpattern getconsdef suclinfo build_remaining_matcher patnodes0 varenv0 exprheap0 varalloc0 mk_default_expression pgraph level pnode psym localvars0 eips0 pargs
= build_remaining_matcher level patnodes0 varenv0 localvars0 eips0 exprheap0 varalloc0
  where (pdef,(psym,pargs)) = varcontents pgraph pnode
        build_remaining_matcher level` patnodes` varenv` localvars` eips` exprheap` varalloc`
        = convert_matchpatterns getconsdef suclinfo build_casebranch0 patnodes` varenv` exprheap` varalloc` mk_default_expression pgraph level` localvars` eips` pnodes

convert_matchpattern ::
    ((Global Index) -> ConsDef)             // Get ConsDef from environment
    (SymbKind -> (Ident,Int))               // Identifer and formal arity of symbols
    (  Level                                // Level to assign to free variables
       [SuclVariable]                       // List of pattern nodes
       (SuclVariable->(Ident,VarInfoPtr))   // Assigning FreeVars to variables from the environment
       [FreeVar]                            // Accumulator for list of local variables in the function body (from lets and cases)
       [ExprInfoPtr]                        // Accumulator for list of expression pointers from the function body
       *ExpressionHeap                      // Initial expression heap for case branch
    ->*(  *VarAlloc                         // Initial variable heap for case branch
       -> ( *ExpressionHeap                 // Modified expression heap from case branch
          , *VarAlloc                       // Modified variable heap from case branch
          , Expression                      // Resulting branch expression
          , Int                             // Reference count to default expression
          , [FreeVar]                       // List of local variables in the function body (from lets and cases)
          , [ExprInfoPtr]                   // List of expression pointers from the function body
          )
       )
    )
    [SuclVariable]                          // List of pattern nodes
    (SuclVariable->(Ident,VarInfoPtr))      // Assigning FreeVars to variables from the environment
    *ExpressionHeap                         // Initial expression heap
    *VarAlloc                               // Initial variable heap
    (  (*ExpressionHeap,([Expression],[ExprInfoPtr]))
    -> (*ExpressionHeap,([Expression],[ExprInfoPtr]))
    )                                       // Default expression builder
    (Graph SuclSymbol SuclVariable)         // Case pattern to convert
    Level                                   // Level to assign to fresh free variables
    SuclVariable
    SuclSymbol
    [FreeVar]                               // Accumulator for list of local variables in the function body (from lets and cases)
    [ExprInfoPtr]                           // Accumulator for list of expression pointers from the function body
    [SuclVariable]                          // Subsequent variables in pattern to match
 -> ( *ExpressionHeap                       // Modified expression heap
    , *VarAlloc                             // Modified variable heap
    , Expression                            // Resulting (case) expression
    , Int                                   // Modified reference count to default expression
    , [FreeVar]                             // List of local variables in the function body (from lets and cases)
    , [ExprInfoPtr]                         // List of expression pointers from the function body
    )

convert_matchpattern getconsdef suclinfo build_casebranch patnodes0 varenv0 exprheap0 varalloc0 mk_default_expression pgraph level pnode psym localvars0 eips0 pargs
= (exprheap4,varalloc2,case_expression,1+refcount,(freevars--->("convert.convert_matchpattern.freevars used",freevars))++localvars1,[cip,bvip:eips2])
    ---> (("convert.convert_matchpattern localvars",freevars),("refcount",refcount,"->",1+refcount))
  where (exprheap3,varalloc2,branch_expression,refcount,localvars1,eips2)
        = convert_matchpatterns getconsdef suclinfo build_casebranch patnodes1 varenv1 exprheap2 varalloc1 mk_default_expression pgraph (level+1) localvars0 eips1 pargs
        (cip,exprheap1) = newPtr EI_Empty exprheap0
        (bvip,exprheap2) = newPtr EI_Empty exprheap1
        case_expression
        = Case ci
        ci
        = { case_expr = Var (mkboundvar bvip (varenv0 pnode))
          , case_guards = cps
          , case_default = Yes default_expression
          , case_ident = No
          , case_info_ptr = cip
          , case_default_pos = NoPos
          }
        (exprheap4,([default_expression:_],eips1))
        = mk_default_expression (exprheap3,([],eips0))
        cps = convert_constructor getconsdef psym freevars branch_expression
        (varenv1,varalloc1)
        = allocate_vars "_parg" varenv0 varalloc0 pargs
        patnodes1 = pargs++patnodes0
        freevars = map (flip (--->) "convert.convert_matchpattern.freevars.<freevar> used from freevars" o mkfreevar level o varenv1) pargs

allocate_vars ::
    {#.Char}
    (SuclVariable->(Ident,VarInfoPtr))
    *VarAlloc
    .[SuclVariable]
 -> ( (SuclVariable->(Ident,VarInfoPtr))
    , .VarAlloc
    )

allocate_vars prefix varenv0 varalloc0 []
= (varenv0,varalloc0)
allocate_vars prefix varenv0 varalloc0 [pnode:pnodes]
= (varenv2,varalloc2)
  where ((ident,varinfoptr),varalloc1) = newvar prefix varalloc0
        (varenv1,varalloc2)
        = allocate_vars prefix varenv0 varalloc1 pnodes
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

:: ExpressionMaker :== SuclVariable -> Expression

new_convert_graph ::
    .PredefinedSymbol                       // Predefined type of string representations
    (SymbKind -> (Ident,Int))               // Identifer and formal arity of symbols
    [.SuclVariable]                         // Variables in the patterns of the surrounding cases
    (SuclVariable -> .(Ident,VarInfoPtr))   // Get information on variables bound in surrounding cases
    .Level                                  // Nesting level for new variables
    (Rgraph .SuclSymbol .SuclVariable)      // Rooted graph (replacement of rule) to convert
    *VarAlloc                               // Variable allocation information (heap)
    *ExpressionHeap                         // Expression allocation information (heap)
    u:[FreeVar]                             // Heap-allocated bound variables (from lets) (accumulator argument)
    .[ExprInfoPtr]                          // Heap-allocated expressions (accumulator argument)
 -> ( .ExpressionHeap                       // Reduced expression heap
    , .VarAlloc                             // Reduced variable allocation info
    , Expression                            // Resulting expression
    , v:[FreeVar]                           // Heap-allocated bound variables (from lets)
    , [ExprInfoPtr]                         // Heap-allocated expressions
    )
 ,  [u <= v]

new_convert_graph stringtype suclinfo patnodes varenv level srgraph varalloc0 exprheap0 localvars0 eips0
= ((exprheap4,varalloc1,expression,localvars1,eips4) <--- "convert.new_convert_graph ends") ---> ("convert.new_convert_graph begins with patnodes "+++listToString patnodes)
  where (closeds,_) = graphvars sgraph [sroot]
        sgraph = rgraphgraph srgraph; sroot = rgraphroot srgraph
        refcounter = refcount sgraph [sroot]
        shareds = [var \\ var <- closeds | refcounter var>1] -- patnodes
        mksubexpr = foldr (mkfreevarref varenv) tmpmksubexpr patnodes
        (varalloc1,(tmpmksubexpr,letbinds,localvars1))
        = foldlr (bind_a_variable refcounter level lookup_unshared) (varalloc0,(mkunsharedsubexpr,[],localvars0)) shareds
        mkunsharedsubexpr uvar (uexprheap,(urest,ueips))
        = (uexprheap,([lookup_unshared uvar:urest],ueips))
        (exprheap4,(exprs,eips1))
        = foldlr (new_convert_graph_node stringtype suclinfo sgraph mksubexpr) (exprheap3,([],eips0)) closeds
        exprmap = zip2 closeds exprs
        lookup_unshared = plookup toString exprmap
        (exprheap3,([rootexpression:_],eips2))
        = mksubexpr sroot (exprheap2,([],eips1))
        (exprheap2,(expression,eips4))
        = (if (isEmpty shareds) id (buildletexpr letbinds)) (exprheap0,(rootexpression,eips2))

mkfreevarref varenv patvar defaultmksubexpr
= mksubexpr
  where mksubexpr var (exprheap0,(rest,eips0))
        = if (var==patvar)
             (exprheap1,([Var boundvar:rest],eips1))
             (defaultmksubexpr var (exprheap0,(rest,eips0)))
          where boundvar
                = { var_name = ident
                  , var_info_ptr = varinfoptr
                  , var_expr_ptr = varexprptr
                  }
                (varexprptr,exprheap1) = newPtr EI_Empty exprheap0
                eips1 = [varexprptr:eips0]
                (ident,varinfoptr) = varenv patvar

buildletexpr letbinds (exprheap0,(rootexpression,eips0))
= ((exprheap1,(Let letinfo,eips1)) <--- "convert.buildletexpr ends") ---> "convert.buildletexpr begins"
  where letinfo
        = { let_strict_binds = []
          , let_lazy_binds = letbinds
          , let_expr = rootexpression
          , let_info_ptr = letinfoptr
          , let_expr_position = NoPos
          }
        (letinfoptr,exprheap1) = newPtr EI_Empty exprheap0
        eips1 = [letinfoptr:eips0]

bind_a_variable refcounter level lookup_unshared var (varalloc0,(defaultmksubexpr,rest,localvars0))
= (((varalloc1,(mksubexpr,[lb:rest],localvars1)) <--- "convert.bind_a_variable ends") ---> "convert.bind_a_variable begins")
    ---> ("convert.bind_a_variable localvars",freevar)
  where lb
        = { lb_dst = freevar
          , lb_src = lookup_unshared var
          , lb_position = NoPos
          }
        freevar
        = { fv_def_level = level
          , fv_name = ident
          , fv_info_ptr = varinfoptr
          , fv_count = refcounter var
          }
        mksubexpr var` (exprheap0,(rest,eips0))
        = if (var`==var)
             (exprheap1,([Var boundvar:rest],eips1))
             (defaultmksubexpr var` (exprheap0,(rest,eips0)))
          where boundvar
                = { var_name = ident
                  , var_info_ptr = varinfoptr
                  , var_expr_ptr = varexprptr
                  }
                (varexprptr,exprheap1) = newPtr EI_Empty exprheap0
                eips1 = [varexprptr:eips0]
        ((ident,varinfoptr),varalloc1) = newvar "_share" varalloc0
        localvars1 = [(freevar--->"convert.bind_a_variable.freevar used from localvars1"):localvars0]

new_convert_graph_node ::
    .PredefinedSymbol
    (SymbKind -> (Ident,Int))           // Identifer and formal arity of symbols
    (Graph .SuclSymbol SuclVariable)
    (  SuclVariable
       ( eh1:ExpressionHeap
       , ( [Expression]
         , ip2:[ExprInfoPtr]
         )
       )
    -> ( eh0:ExpressionHeap
       , ( [Expression]
         , ip0:[ExprInfoPtr]
         )
       )
    )
    SuclVariable
    ( *ExpressionHeap
    , ( [Expression]
      , ip1:[ExprInfoPtr]
      )
    )
 -> ( eh2:ExpressionHeap
    , ( [Expression]
      , [ExprInfoPtr]
      )
    )
 ,  [eh0<=eh1,eh0<=eh2,ip0 ip1<=ip2]

new_convert_graph_node stringtype suclinfo graph mksubexpr var (exprheap0,(rest,eips0))
= ((exprheap2,([expr:rest],eips2)) <--- "convert.new_convert_graph_node ends") ---> "convert.new_convert_graph_node begins"
  where (expr,exprheap1,eips2)
        = convert_graph_symbol stringtype suclinfo sym subexprs exprheap0 eips1
        (exprheap2,(subexprs,eips1))
        = foldlr mksubexpr (exprheap1,([],eips0)) args
        (_,(sym,args)) = varcontents graph var

convert_graph_symbol ::
    PredefinedSymbol
    (SymbKind -> (Ident,Int))           // Identifer and formal arity of symbols
    !SuclSymbol
    [Expression]
    *ExpressionHeap
    [ExprInfoPtr]
 -> ( Expression
    , *ExpressionHeap
    , [ExprInfoPtr]
    )

convert_graph_symbol stringtype suclinfo (SuclInt    i) [] exprheap eips = (BasicExpr (BVI (toString i)) BT_Int   ,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclChar   c) [] exprheap eips = (BasicExpr (BVC (toString c)) BT_Char  ,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclReal   r) [] exprheap eips = (BasicExpr (BVR (toString r)) BT_Real  ,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclBool   b) [] exprheap eips = (BasicExpr (BVB           b ) BT_Bool  ,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclString s) [] exprheap eips = (makeStringExpr stringtype s           ,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclApply arity) [argexpr:argexprs] exprheap eips = (argexpr @ argexprs,exprheap,eips)
convert_graph_symbol stringtype suclinfo (SuclUser symbkind) argexprs exprheap0 eips0
= (App app,exprheap1,[appinfoptr:eips0])
  where app
        = { app_symb = symbident
          , app_args = argexprs
          , app_info_ptr = appinfoptr
          }
        symbident
        = { symb_name = ident
          , symb_kind = symbkind
          , symb_arity = arity
          }
        (ident,arity) = suclinfo symbkind
        (appinfoptr,exprheap1) = newPtr EI_Empty exprheap0
convert_graph_symbol _ _ _ _ exprheap eips = (mstub "convert_graph_symbol" "unexpected application form in graph node",exprheap,eips)

// Magic from Artem
makeStringExpr :: !PredefinedSymbol String -> Expression
makeStringExpr stringtype str
= BasicExpr (BVS str) (BT_String (TA type_symb []))
  where {pds_ident, pds_module, pds_def} = stringtype
        type_symb = MakeTypeSymbIdent { glob_module = pds_module, glob_object = pds_def } pds_ident 0

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

instance toString FreeVar
where toString {fv_def_level,fv_name,fv_info_ptr,fv_count}
      = "{fv_def_level=" +++ toString fv_def_level +++ ",fv_name=" +++ toString fv_name +++ ",fv_info_ptr=" +++ toString fv_info_ptr +++ ",fv_count=" +++ toString fv_count +++ "}"

:: Environment
   = { env_getcommon :: Index -> CommonDefs
     , env_main      :: Index
     , env_dcls      :: {#DclModule}
     , env_infos     :: {(Ident,Int)}
     }

get_formal_name_and_arity :: Environment SymbKind -> (Ident,Int)
get_formal_name_and_arity env (SK_Constructor {glob_module,glob_object})
# consdef = (env.env_getcommon glob_module).com_cons_defs.[glob_object]
= (consdef.cons_symb,consdef.cons_type.st_arity)
get_formal_name_and_arity env (SK_Function {glob_module,glob_object})
= if (glob_module==env.env_main)
     (get_formal_name_and_arity_from_fundef env glob_object)
     (get_formal_name_and_arity_from_funtype env glob_module glob_object)

get_formal_name_and_arity_from_fundef env funindex
= env.env_infos.[funindex]

get_formal_name_and_arity_from_funtype env modindex funindex
# funtype = env.env_dcls.[modindex].dcl_functions.[funindex]
= (funtype.ft_symb,funtype.ft_arity)

instance toString (a,b) | toString a & toString b
where toString (x,y) = "("+++toString x+++","+++toString y+++")"
