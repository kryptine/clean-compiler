implementation module convert

// $Id$

import newtest
import newfold
import coreclean
import rule
import graph
import basic
import checksupport
import syntax
import StdEnv

mstub = stub "convert"

// Cocl to Sucl for functions
cts_function
 :: Int                                                 // Index of current module
    u:{#FunDef}                                          // Function definitions (from ICL)
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    , v:{#FunDef}                                        // Consulted function definitions
    )
 ,  [u<=v]

cts_function main_dcl_module_n fundefs
= (typerules,stricts,funbodies,funkinds,fundefs`)
  where ((typerules,stricts,funbodies,funkinds),fundefs`)
        = foldrarray (convert_fundef main_dcl_module_n) ([],[],[],[]) fundefs

foldrarray :: (a .b -> .b) .b u:{#a} -> (.b,v:{#a}) | uselect_u,usize_u a, [u<=v]
foldrarray f i xs
= fold 0 (usize xs)
  where fold j (n,xs)
        | j>=n
          = (i,xs)
        = (f x i`,xs``)
          where (x,xs`) = xs![j]
                (i`,xs``) = fold (j+1) (n,xs`)

convert_fundef
 :: Int
    FunDef
    ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    )
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
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

              // Anything else will produce an error when actually used
              _
               -> (heap`,graph`,typevar)
                  where [typevar:heap`] = heap
                        graph` = updategraph typevar notimpl graph
                        notimpl = abort "convert_atype: unknown form of Type"

// Convert a basic type to a basic type symbol
convert_btype :: BasicType -> SuclTypeSymbol
convert_btype BT_Int = SuclINT
convert_btype BT_Char = SuclCHAR
convert_btype BT_Real = SuclREAL
convert_btype BT_Bool = SuclBOOL
convert_btype BT_Dynamic = SuclDYNAMIC
convert_btype BT_File = SuclFILE
convert_btype BT_World = SuclWORLD
convert_btype _ = abort "convert: convert_btype: unhandled BasicType constructor"


/******************************************************************************
*  ALGEBRAIC TYPE CONVERSION                                                  *
******************************************************************************/


cts_getconstrs ::
    {#DclModule}                    // Info from used DCL modules
 -> [(SuclTypeSymbol,[SuclSymbol])] // List of constructor symbols for each type symbol

cts_getconstrs dcl_mods
= flatten (zipwith f (a2l dcl_mods) [0..])
  where f dcl_mod dcli
        = [convert_typedef dcli typedef \\ typedef <-: dcl_mod.dcl_common.com_type_defs]

a2l a = [e \\ e<-:a]

convert_typedef :: Index (TypeDef TypeRhs) -> (SuclTypeSymbol,[SuclSymbol])
convert_typedef dcli typedef
= (SuclUSER (mkglobal dcli typedef.td_index),getconstrs dcli typedef.td_rhs)

getconstrs dcli (AlgType constrs)
= map mkalgconstr constrs
  where mkalgconstr defsymb = SuclUser (SK_Constructor (mkglobal dcli defsymb.ds_index))
getconstrs _ _
= mstub "getconstrs" "unhandled TypeRhs form"

mkglobal gmod gob = {glob_module = gmod, glob_object = gob}


/******************************************************************************
*  EXPRESSION CONVERSION                                                      *
******************************************************************************/

convert_functionbody :: Int SuclSymbol FunctionBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_functionbody main_dcl_module_n funsym (TransformedBody t) fundefs0 = convert_transformedbody main_dcl_module_n funsym t fundefs0
convert_functionbody main_dcl_module_n funsym _ fundefs0
 = [(funsym,norule):fundefs0]
   where norule = abort "convert: convert_functionbody: unexpected FunctionBody constructor"

convert_transformedbody :: Int SuclSymbol TransformedBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_transformedbody main_dcl_module_n funsym {tb_args=args,tb_rhs=expression} fundefs0
 | not (isEmpty globals0) // Sanity check, since we have it in our fingers anyway
   = abort "convert: convert_transformedbody: function rhs contains free variables!"
 = [(funsym,[mkrule (map snd seen0) (hd rest) (compilegraph nodes0)]):fundefs1]
   where (_,(nodes0,fundefs1,globals0,rest))
          = convert_expression main_dcl_module_n [] expression ((heap0,seen0),([],fundefs0,[],[]))
         heap0 = heap
         seen0 = map mkseen args
         mkseen fv = (fv.fv_info_ptr,SuclNamed fv.fv_info_ptr)

heap = map SuclAnonymous [0..]

:: NodeBinding sym var :== (var,Node sym var)
:: FunBinding sym var :== (sym,[Rule sym var])

:: Econv_state
   :== ( ( [SuclVariable]                       // Heap of node-ids
         , [(VarInfoPtr,SuclVariable)]          // Already seen CoreClean Variables for cycle breaking
         )
       , ( [NodeBinding SuclSymbol SuclVariable]// Nodes of Sucl expression being built
         , [FunBinding SuclSymbol SuclVariable] // Lifted functions for case/lambda expressions
         , [SuclVariable]                       // Free Sucl variables in expression being built
         , [SuclVariable]                       // List of variables to which root of expression is prepended (accumulator)
         )
       )

convert_expressions main_dcl_module_n bounds exprs (heapseen0,(nodes0,fundefs0,globals0))
 = foldlr (convert_expression main_dcl_module_n bounds) (heapseen0,(nodes0,fundefs0,globals0,[])) exprs

convert_expression
 :: Int                                         // Index of current DCL module
    [(VarInfoPtr,Econv_state->Econv_state)]     // Locally bound variables, with the expressions they're bound to, for resolving locally bound variables
    Expression                                  // Expression to convert
    Econv_state                                 // Input expression conversion state
 -> Econv_state                                 // Resulting expression conversion state

convert_expression main_dcl_module_n bounds (App appinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap2,seen1),(nodes2,fundefs1,globals1,[root:rest]))
   where [root:heap1] = heap0
         ((heap2,seen1),(nodes1,fundefs1,globals1,args0))
          = convert_expressions main_dcl_module_n bounds appinfo.app_args ((heap1,seen0),(nodes0,fundefs0,globals0))
         nodes2 = [(root,(SuclUser appinfo.app_symb.symb_kind,args0)):nodes1]

convert_expression main_dcl_module_n bounds (expr @ exprs) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap2,seen1),(nodes2,fundefs1,globals1,[root:rest]))
   where [root:heap1] = heap0
         ((heap2,seen1),(nodes1,fundefs1,globals1,args0))
          = convert_expressions main_dcl_module_n bounds [expr:exprs] ((heap1,seen0),(nodes0,fundefs0,globals0))
         nodes2 = [(root,(SuclApply (length exprs),args0)):nodes1]

convert_expression main_dcl_module_n bounds (Var varinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = foldmap oldvip newvip seen0 vip
   where // oldvip: We've already seen this Var, reuse it and don't do anything else
         oldvip root = ((heap0,seen0),(nodes0,fundefs0,globals0,[root:rest]))
         // newvip: We haven't seen this Var yet, figure out what to do
         newvip = foldmap local newglobal bounds vip
         // local: this Var is bound locally to an expression, use the associated expression evaluator
         local convert_local
          = ((heap1,seen2),(nodes1,fundefs1,globals1,[root:rest]))
            where seen1 = [(vip,root):seen0]
                  ((heap1,seen2),(nodes1,fundefs1,globals1,[root:_]))
                   = convert_local ((heap0,seen1),(nodes0,fundefs0,globals0,[]))
         // newglobal: this Var wasn't seen before and it's not bound locally, it must be a global reference
         newglobal
          = ((heap1,seen1),(nodes0,fundefs0,globals1,[root:rest]))
            where [root:heap1] = heap0
                  seen1 = [(vip,root):seen0]
                  globals1 = [root:globals0]
         vip = varinfo.var_info_ptr

convert_expression main_dcl_module_n bounds0 (Let letinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = convert_expression main_dcl_module_n bounds1 letinfo.let_expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
   where newbounds = [(lb.lb_dst.fv_info_ptr,convert_bound_expr main_dcl_module_n bounds1 lb.lb_src) \\ lb<-letinfo.let_lazy_binds]
         bounds1 = newbounds++bounds0

convert_expression main_dcl_module_n bounds (Case caseinfo) ((heap0,seen0),(nodes6,fundefs5,globals6,rest))
 = ((heap4,seen3),(nodes9,fundefs9,globals9,[root:rest]))
   where // Plan: (0.5) convert selector
         //       (1) convert branches
         //       (1.5) convert default if present
         //       (2) build rules/fundef from branches
         //       (4) build closure node
         // (4) Build closure node
         nodes9 = [(root,(SuclCase caseinfo.case_info_ptr,innerglobals++defaultroots++selectorroots)):nodes8]
         // (2) build rules/fundef from branches
         fundefs9 = [(SuclCase caseinfo.case_info_ptr,map mkalt alternatives++map mkdefaultalt defaultroots):fundefs8]
            where mkalt (patroot,reproot,nodes)
                   = mkrule (innerglobals++defaultroots++[patroot]) reproot (compilegraph nodes)
                  mkdefaultalt defaultroot
                   = mkrule (innerglobals++defaultroots++selectorroots) defaultroot emptygraph
         // (1.5) convert default if necessary
         ((heap4,seen3),(nodes7,fundefs6,globals7,defaultroots))
          = foldoptional id (convert_expression main_dcl_module_n bounds) caseinfo.case_default ((heap3,seen2),(nodes6,fundefs5,globals6,[]))
         // (1) convert branches
         globals8 = removeDup (innerglobals++globals7)
         ((heap3,seen2),(innerglobals,fundefs7,alternatives))
          = case caseinfo.case_guards
            of AlgebraicPatterns _ branches
                -> foldlr (convert_algebraic_branch main_dcl_module_n) ((heap2,seen1),([],fundefs6,[])) branches
               BasicPatterns _ branches
                -> foldlr (convert_basic_branch main_dcl_module_n) ((heap2,seen1),([],fundefs6,[])) branches
               _
                -> ((heap2,seen1),([],fundefs6,abort "convert: convert_expression: unhandled CasePatterns constructor"))
         // (0.5) Convert selector
         ((heap2,seen1),(nodes8,fundefs8,globals9,selectorroots))
          = convert_expression main_dcl_module_n bounds caseinfo.case_expr ((heap1,seen0),(nodes7,fundefs7,globals8,[]))
         // (0) Claim root node
         [root:heap1] = heap0

convert_algebraic_branch main_dcl_module_n branch ((heap0,seen0),(globals0,fundefs0,alternatives0))
 = ((heap2,seen2),(globals1,fundefs1,alternatives1))
   where ((heap1,seen1),(nodes0,patrest))
          = convert_algebraic_pattern main_dcl_module_n branch ((heap0,seen0),([],[]))
         ((heap2,seen2),(nodes1,fundefs1,globals1,rest))
          = convert_expression main_dcl_module_n [] branch.ap_expr ((heap1,seen1),(nodes0,fundefs0,globals0,[]))
         alternatives1 = [(hd patrest,hd rest,nodes1):alternatives0]

convert_algebraic_pattern main_dcl_module_n ap ((heap0,seen0),(nodes0,rest))
 = ((heap1,seen1),(nodes1,[root:rest]))
   where [root:heap1] = heap0
         argmap = [(fv.fv_info_ptr,SuclNamed fv.fv_info_ptr) \\ fv <- ap.ap_vars]
         seen1 = argmap++seen0
         args0 = map snd argmap
         nodes1 = [(root,(SuclUser (SK_Constructor {glob_module=main_dcl_module_n,glob_object=ap.ap_symbol.glob_object.ds_index}),args0)):nodes0]

convert_basic_branch main_dcl_module_n branch ((heap0,seen0),(globals0,fundefs0,alternatives0))
 = ((heap2,seen2),(globals1,fundefs1,alternatives1))
   where ((heap1,seen1),(nodes0,patrest))
          = convert_basic_pattern branch ((heap0,seen0),([],[]))
         ((heap2,seen2),(nodes1,fundefs1,globals1,rest))
          = convert_expression main_dcl_module_n [] branch.bp_expr ((heap1,seen1),(nodes0,fundefs0,globals0,[]))
         alternatives1 = [(hd patrest,hd rest,nodes1):alternatives0]

convert_basic_pattern bp ((heap0,seen0),(nodes0,rest))
 = ((heap1,seen0),(nodes1,[root:rest]))
   where [root:heap1] = heap0
         nodes1 = [(root,(convert_bvalue bp.bp_value,[])):nodes0]

convert_bound_expr main_dcl_module_n bounds expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap1,seen1),(nodes1,fundefs1,globals1,rest`))
   where ((heap1,seen1),(nodes1,fundefs1,globals1,rest`))
          = convert_expression main_dcl_module_n bounds expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))

convert_bvalue :: BasicValue -> SuclSymbol
convert_bvalue (BVI intrepr) = SuclInt (toInt intrepr)
//convert_bvalue (BVC charrepr) = SuclChar (fromString charrepr)
convert_bvalue (BVB bool) = SuclBool bool
convert_bvalue (BVR realrepr) = SuclReal (toReal realrepr)
//convert_bvalue (BVS stringrepr) = SuclString (fromString stringrepr)
convert_bvalue _ = abort "convert: convert_bvalue: unhandled BasicValue constructor"

convert_kind :: DefOrImpFunKind -> SuclSymbolKind
convert_kind (FK_DefFunction b) = SuclPrimitive // Function from a definition module
convert_kind (FK_ImpFunction b) = SuclFunction  // Function from a (the) implementation module
convert_kind  FK_DefMacro       = SuclFunction  // Macro from a definition module
convert_kind  FK_ImpMacro       = SuclFunction  // Macro from an implementation module
convert_kind _ = abort "convert: convert_kind: unhandled DefOrImpFunKind constructor"


/****************************************************************
**  Conversion of exported function symbols from cocl to sucl  **
****************************************************************/

cts_exports :: {#DclModule} Int -> [SuclSymbol]
cts_exports dcl_mods main_dcl_module_n
= map (mk_symbol main_dcl_module_n) (getconversion cFunctionDefs dcl_mods.[main_dcl_module_n])

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

//Sucl to Cocl for function bodies
stc_funcdefs ::
    {#.DclModule}       // DCL for looking up constructor types
    Int                 // Index of current module
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

stc_funcdefs dcl_mods main_dcl_module_n firstnewindex exprheap0 varheap0 srrs oldfundefs
= (exprheap1,varheap1,new_fundefs)
  where new_fundef_limit = foldr max 0 [gi.glob_object+1\\{srr_assigned_symbol = SuclUser (SK_Function gi)}<-srrs | gi.glob_module==main_dcl_module_n]
        (exprheap1,varheap1,new_fundefs)
        = store_newfuns dcl_mods main_dcl_module_n firstnewindex exprheap0 varheap0 srrs (copy_oldfuns oldfundefs (createArray new_fundef_limit nofundef))
        nofundef
        = mstub "stc_funcdefs" "introduced function symbol without an actual body"

copy_oldfuns oldfundefs newfundefs
= foldlArrayStWithIndex copyone newfundefs oldfundefs
  where copyone i fundef fundefs
        = {fundefs & [i]=fundef}

store_newfuns dcl_mods main_dcl_module_n firstnewindex exprheap0 varheap0 [] fundefs0
= (exprheap0,varheap0,fundefs0)
store_newfuns dcl_mods main_dcl_module_n firstnewindex exprheap0 varheap0 [srr:srrs] fundefs0
= case srr.srr_assigned_symbol
  of (SuclUser (SK_Function {glob_module=modi,glob_object=funindex}))
      | modi == main_dcl_module_n
        -> store_newfuns dcl_mods main_dcl_module_n firstnewindex exprheap1 varheap1 srrs fundefs1
           where (exprheap1,varheap1,funbody)
                 = stc_funcdef dcl_mods exprheap0 varheap0 srr.srr_function_def
                 funinfo
                 = { fi_calls       = collect_calls main_dcl_module_n funbody
                   , fi_group_index = 0
                   , fi_def_level   = NotALevel
                   , fi_free_vars   = []
                   , fi_local_vars  = []
                   , fi_dynamics    = []
                   , fi_properties  = 0
                   }
                 fundefs1 = create_or_update_fundefs funindex funbody funinfo fundefs0
                 create_or_update_fundefs
                 = if (funindex>=firstnewindex)
                      (create_fundef (length (arguments srr.srr_typerule)))
                      update_fundef
     _
      -> store_newfuns dcl_mods main_dcl_module_n firstnewindex exprheap0 varheap0 srrs fundefs0

create_fundef :: .Int Int FunctionBody FunInfo *{#FunDef} -> .{#FunDef}
create_fundef funindex arity funbody funinfo fundefs
= {fundefs & [funindex] = fundef}
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
= {tmpfundefs & [index] = newfundef}
  where (oldfundef,tmpfundefs) = oldfundefs![index]
        newfundef = {oldfundef & fun_body = newbody, fun_info = newinfo}

stc_funcdef ::
    {#DclModule}                        // DCL for looking up constructor types
    *ExpressionHeap                     // Fresh expression space
    *(Heap VarInfo)                     // Fresh variable space
    (FuncDef SuclSymbol SuclVariable)   // Function definition to convert
 -> ( *ExpressionHeap                   // Remaining expression space
    , *(Heap VarInfo)                   // Remaining variable space
    , FunctionBody                      // Converted function body
    )

stc_funcdef dcl_mods exprheap0 varheap0 (args,body)
= (exprheap1,varheap2,TransformedBody tb)
  where tb
        = { tb_args = map freevarenv args
          , tb_rhs  = expr
          }
        (exprheap1,varheap2,expr)
        = convert_funcbody dcl_mods 1 args freevarenv exprheap0 varheap1 body
        (freevarenv,varheap1,patnodes)
        = allocate_freevars 0 noexpr varheap0 args
        noexpr = mstub "std_funcdef" "open variable in rhs but not lhs"

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
    {#DclModule}                        // Dcl modules for looking up constructor types
    Level                               // (Lexical?) level for new variables
    [SuclVariable]                      // Nodes from case variables in the environment
    (SuclVariable -> FreeVar)           // Mapping from free nodes to expressions
    *ExpressionHeap                     // Fresh expression space
    *(Heap VarInfo)                     // Fresh variable space
    !(FuncBody SuclSymbol SuclVariable) // Function body to convert
 -> ( *ExpressionHeap                   // Modified expression space
    , *(Heap VarInfo)                   // Modified variable space
    , Expression                        // Resulting expression
    )

convert_funcbody dcl_mods level patnodes freevarenv exprheap0 varheap0 (MatchPattern pattern yesbody nobody)
= (exprheap4,varheap3,match_expression)
  where (exprheap1,varheap1,case_expression,default_refcount)
        = convert_matchpatterns dcl_mods build_casebranch patnodes freevarenv exprheap0 varheap0 default_expression pgraph level [proot]
        pgraph = rgraphgraph pattern
        proot = rgraphroot pattern
        default_boundvar
        = { var_name = default_ident
          , var_info_ptr = default_info_ptr
          , var_expr_ptr = default_expr_ptr
          }
        (default_info_ptr,varheap2) = newPtr VI_Empty varheap1
        (letinfoptr,exprheap2) = newPtr EI_Empty exprheap1
        (default_expr_ptr,exprheap3) = newPtr EI_Empty exprheap2
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
        default_ident
        = { id_name="_anonymous_shared_case_default"
          , id_info=nilPtr
          }
        build_casebranch level` patnodes` freevarenv` exprheap0` varheap0`
        = (exprheap1`,varheap1`,expr`,0)
          where (exprheap1`,varheap1`,expr`)
                = convert_funcbody dcl_mods level` patnodes` freevarenv` exprheap0` varheap0` yesbody
        (exprheap4,varheap3,match_failure_expression)
        = convert_funcbody dcl_mods (level+1) patnodes freevarenv exprheap3 varheap2 nobody
        (default_expression,match_expression)
        = if (default_refcount==1)
             (match_failure_expression,case_expression)
             (match_failure_reference,let_expression)
        let_expression = Let li
        match_failure_reference = Var default_boundvar

convert_funcbody dcl_mods level patnodes freevarenv exprheap0 varheap0 (BuildGraph srgraph)
= convert_graph patnodes (FreeVar o freevarenv) level srgraph varheap0 exprheap0

convert_matchpatterns ::
    {#DclModule}                    // DCL modules
    (  Int                          // Level to assign to free variables
       [SuclVariable]               // List of pattern nodes
       (SuclVariable->FreeVar)      // Assigning FreeVars to variables from the environment
       *ExpressionHeap              // Initial expression heap for case branch
    ->*(  *(Heap VarInfo)           // Initial variable heap for case branch
       -> ( *ExpressionHeap         // Modified expression heap from case branch
          , *(Heap VarInfo)         // Modified variable heap from case branch
          , Expression              // Resulting branch expression
          , Int                     // Reference count to default expression
          )
       )
    )
    [SuclVariable]                  // List of pattern nodes
    (SuclVariable->FreeVar)         // Assigning FreeVars to variables from the environment
    *ExpressionHeap                 // Initial expression heap
    *(Heap VarInfo)                 // Initial variable heap
    Expression                      // Default expression
    (Graph SuclSymbol SuclVariable) // Case pattern to convert
    Level                           // Level to assign to fresh free variables
    [SuclVariable]                  // Subsequent variables in pattern to match
 -> ( *ExpressionHeap               // Modified expression heap
    , *(Heap VarInfo)               // Modified variable heap
    , Expression                    // Resulting (case) expression
    , Int                           // Modified reference count to default expression
    )

convert_matchpatterns dcl_mods build_casebranch patnodes freevarenv exprheap0 varheap0 default_expression pgraph level []
= (exprheap1,varheap1,case_expression,refcount)
  where (exprheap1,varheap1,case_expression,refcount)
        = build_casebranch level patnodes freevarenv exprheap0 varheap0

convert_matchpatterns dcl_mods build_casebranch0 patnodes0 freevarenv0 exprheap0 varheap0 default_expression pgraph level [pnode:pnodes]
| pdef
  = convert_matchpattern dcl_mods build_remaining_matcher patnodes0 freevarenv0 exprheap0 varheap0 default_expression pgraph level pnode psym pargs
= build_remaining_matcher level patnodes0 freevarenv0 exprheap0 varheap0
  where (pdef,(psym,pargs)) = varcontents pgraph pnode
        build_remaining_matcher level` patnodes` freevarenv` exprheap` varheap`
        = convert_matchpatterns dcl_mods build_casebranch0 patnodes` freevarenv` exprheap` varheap` default_expression pgraph level` pnodes

convert_matchpattern ::
    {#DclModule}                    // DCL modules
    (  Level                        // Level to assign to free variables
       [SuclVariable]               // List of pattern nodes
       (SuclVariable->FreeVar)      // Assigning FreeVars to variables from the environment
       *ExpressionHeap              // Initial expression heap for case branch
    ->*(  *(Heap VarInfo)           // Initial variable heap for case branch
       -> ( *ExpressionHeap         // Modified expression heap from case branch
          , *(Heap VarInfo)         // Modified variable heap from case branch
          , Expression              // Resulting branch expression
          , Int                     // Reference count to default expression
          )
       )
    )
    [SuclVariable]                  // List of pattern nodes
    (SuclVariable->FreeVar)         // Assigning FreeVars to variables from the environment
    *ExpressionHeap                 // Initial expression heap
    *(Heap VarInfo)                 // Initial variable heap
    Expression                      // Default expression
    (Graph SuclSymbol SuclVariable) // Case pattern to convert
    Level                           // Level to assign to fresh free variables
    SuclVariable
    SuclSymbol
    [SuclVariable]                  // Subsequent variables in pattern to match
 -> ( *ExpressionHeap               // Modified expression heap
    , *(Heap VarInfo)               // Modified variable heap
    , Expression                    // Resulting (case) expression
    , Int                           // Modified reference count to default expression
    )

convert_matchpattern dcl_mods build_casebranch patnodes0 freevarenv0 exprheap0 varheap0 default_expression pgraph level pnode psym pargs
= (exprheap2,varheap2,case_expression,1+refcount)
  where (exprheap2,varheap2,branch_expression,refcount)
        = convert_matchpatterns dcl_mods build_casebranch patnodes1 freevarenv1 exprheap1 varheap1 default_expression pgraph (level+1) pargs
        (cip,exprheap1) = newPtr EI_Empty exprheap0
        case_expression = Case ci
        ci
        = { case_expr = FreeVar (freevarenv0 pnode)
          , case_guards = cps
          , case_default = Yes default_expression
          , case_ident = No
          , case_info_ptr = cip
          , case_default_pos = NoPos
          }
        cps = convert_constructor dcl_mods psym freevars branch_expression
        (freevarenv1,varheap1,freevars)
        = allocate_freevars level freevarenv0 varheap0 pargs
        patnodes1 = pargs++patnodes0

allocate_freevars ::
    Level
    (SuclVariable->FreeVar)
    *(Heap VarInfo)
    .[SuclVariable]
 -> ( (SuclVariable->FreeVar)
    , .Heap VarInfo
    , .[FreeVar]
    )

allocate_freevars level freevarenv0 varheap0 []
= (freevarenv0,varheap0,[])
allocate_freevars level freevarenv0 varheap0 [pnode:pnodes]
= (freevarenv2,varheap2,[freevar:freevars])
  where freevar
        = { fv_def_level = level
          , fv_name      = ident
          , fv_info_ptr  = varinfoptr
          , fv_count     = mstub "allocate_freevars" "reference counting for case pattern argument not yet implemented"
          }
        ident
        = { id_name = "_anonymous_case_pattern_argument_variable"
          , id_info = nilPtr
          }
        (varinfoptr,varheap1) = newPtr VI_Empty varheap0
        (freevarenv1,varheap2,freevars)
         = allocate_freevars level freevarenv0 varheap1 pnodes
        freevarenv2 = adjust pnode freevar freevarenv1

convert_constructor :: {#DclModule} SuclSymbol [FreeVar] Expression -> CasePatterns
convert_constructor dcl_mods (SuclInt  i) [] expr = mkbps BT_Int  (BVI (toString i)) expr
convert_constructor dcl_mods (SuclChar c) [] expr = mkbps BT_Char (BVC (toString c)) expr
convert_constructor dcl_mods (SuclReal r) [] expr = mkbps BT_Real (BVR (toString r)) expr
convert_constructor dcl_mods (SuclBool b) [] expr = mkbps BT_Bool (BVB           b ) expr
convert_constructor dcl_mods (SuclUser (SK_Constructor consindex)) freevars expr
= AlgebraicPatterns typedefindex [ap]
  where typedefindex = {glob_module=consmodule,glob_object=consdef.cons_type_index}
        consmodule = consindex.glob_module
        consdef = dcl_mods.[consmodule].dcl_common.com_cons_defs.[consindex.glob_object]
        defsymb
        = { ds_ident = consdef.cons_symb
          , ds_arity = consdef.cons_type.st_arity
          , ds_index = consdef.cons_index
          }
        globdefsymb
        = { glob_module = consmodule
          , glob_object = defsymb
          }
        ap
        = { ap_symbol   = globdefsymb
          , ap_vars     = freevars
          , ap_expr     = expr
          , ap_position = NoPos
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

convert_graph patnodes mkexpr0 level srgraph varheap0 exprheap0
= (exprheap4,varheap1,expression)
  where (exprheap4,refcount,closeds,_,mkexpr1)
        = convert_graph_node mkexpr sgraph exprheap3 patnodes (const 0) [] mkexpr0 sroot
        sgraph = rgraphgraph srgraph; sroot = rgraphroot srgraph
        shareds = [(closed,n) \\ closed<-closeds, n<-[refcount closed] | n>1]
        (mkexpr,letbinds,varheap1,exprheap3)
        = foldr (allocate_shared_variable level) (mkexpr1,[],varheap0,exprheap2) shareds
        root_expression = mkexpr sroot
        (expression,exprheap2) = mkletexpr letbinds root_expression exprheap0

mkletexpr letbinds letbody exprheap0
| isEmpty letbinds
  = (letbody,exprheap0)
= (letexpr,exprheap1)
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

allocate_shared_variable level (pnode,refcount) (mkexpr,letbinds,varheap0,exprheap0)
= (adjust pnode (Var boundvar) mkexpr,[letbind:letbinds],varheap1,exprheap1)
  where boundvar
        = { var_name = ident
          , var_info_ptr = varinfoptr
          , var_expr_ptr = exprinfoptr
          }
        ident
        = { id_name = "_anonymous_share_breaking_variable"
          , id_info = nilPtr
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
        (varinfoptr,varheap1) = newPtr VI_Empty varheap0
        (exprinfoptr,exprheap1) = newPtr EI_Empty exprheap0

convert_graph_nodes ::
    ExpressionMaker                 // Final expression maker
    (Graph SuclSymbol SuclVariable) // Subject graph to transform
    *ExpressionHeap                 // Input expression heap for generated expressions
    u:[SuclVariable]                // Input list of seen nodes
    (SuclVariable->Int)             // Input reference count
    v:[SuclVariable]                // Input defined nodes
    ExpressionMaker                 // Input expression maker
    [SuclVariable]                  // Nodes to examine
 -> ( *ExpressionHeap               // Resulting expression heap
    , SuclVariable->Int             // Output reference count
    , v:[SuclVariable]              // Output defined nodes
    , u:[SuclVariable]              // Output list of seen nodes
    , ExpressionMaker               // Output expression maker
    )

convert_graph_nodes mkexpr sgraph exprheap0 seen0 refcount0 closeds0 mkexpr0 []
= (exprheap0,refcount0,closeds0,seen0,mkexpr0)
convert_graph_nodes mkexpr sgraph exprheap0 seen0 refcount0 closeds0 mkexpr0 [snode:snodes]
= (exprheap2,refcount3,closeds2,seen2,mkexpr2)
  where (exprheap2,refcount1,closeds1,seen2,mkexpr1)
        = convert_graph_nodes mkexpr sgraph exprheap1 seen1 refcount0 closeds0 mkexpr0 snodes
        (exprheap1,refcount2,closeds2,seen1,mkexpr2)
        = convert_graph_node mkexpr sgraph exprheap0 seen0 refcount1 closeds1 mkexpr1 snode
        refcount3 = inccounter snode refcount2

convert_graph_node ::
    ExpressionMaker                 // Final expression builder
    (Graph SuclSymbol SuclVariable) // Graph to convert
    *ExpressionHeap                 // Heap from which to allocate new expression info
    u:[SuclVariable]                // Already encountered nodes
    (SuclVariable->Int)             // Input reference count
    v:[SuclVariable]                // Input closed variables
    ExpressionMaker                 // Input expression builder
    SuclVariable                    // Node in graph to convert
 -> ( *ExpressionHeap               // Modified expression heap
    , SuclVariable -> Int           // Output reference count
    , v:[SuclVariable]              // Output closed variables
    , u:[SuclVariable]              // Output seen variables
    , ExpressionMaker               // Output expression builder
    )

convert_graph_node mkexpr sgraph exprheap0 seen0 refcount0 closeds0 mkexpr0 snode
| isMember snode seen0
  = (exprheap0,refcount0,closeds0,seen0,mkexpr0)
= (exprheap2,refcount1,closeds2,seen2,mkexpr2)
  where seen1 = [snode:seen0]
        (_,(ssym,sargs)) = varcontents sgraph snode  // Must be closed; open nodes already initially in "seen"
        (expr,exprheap1)
        = convert_graph_symbol ssym (map mkexpr sargs) exprheap0
        (exprheap2,refcount1,closeds1,seen2,mkexpr1)
        = convert_graph_nodes mkexpr sgraph exprheap1 seen1 refcount0 closeds0 mkexpr0 sargs
        mkexpr2 = adjust snode expr mkexpr1
        closeds2 = [snode:closeds1]

convert_graph_symbol ::
    !SuclSymbol
    [Expression]
    *ExpressionHeap
 -> ( Expression
    , *ExpressionHeap
    )

convert_graph_symbol (SuclInt  i) [] exprheap = (BasicExpr (BVI (toString i)) BT_Int ,exprheap)
convert_graph_symbol (SuclChar c) [] exprheap = (BasicExpr (BVC (toString c)) BT_Char,exprheap)
convert_graph_symbol (SuclReal r) [] exprheap = (BasicExpr (BVR (toString r)) BT_Real,exprheap)
convert_graph_symbol (SuclBool b) [] exprheap = (BasicExpr (BVB           b ) BT_Bool,exprheap)
convert_graph_symbol (SuclApply arity) [argexpr:argexprs] exprheap = (argexpr @ argexprs,exprheap)
convert_graph_symbol (SuclUser symbkind) argexprs exprheap0
= (App app,exprheap1)
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
convert_graph_symbol _ _ _ = mstub "convert_graph_symbol" "unexpected application form in graph node"

mkbe bv bt = BasicExpr bv bt

//collect_calls :: Int FunctionBody -> [FunCall]
collect_calls main_dcl_module_n (TransformedBody tb)
= foldr (addfuncall main_dcl_module_n) [] symbidents
  where symbidents = collect_expr_calls tb.tb_rhs []
collect_calls _ _ = mstub "collect_calls" "unexpected FunctionBody form"

addfuncall main_dcl_module_n {symb_kind=SK_Function {glob_module=modindex,glob_object=funindex}} rest
| modindex == main_dcl_module_n
  = [{fc_level=NotALevel,fc_index=funindex}:rest]
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
    (FuncBody sym var)
 -> .result

fold_funcbody matchpattern buildgraph funcbody
= fold funcbody
  where fold (MatchPattern pattern yesbody nobody) = matchpattern pattern (fold yesbody) (fold nobody)
        fold (BuildGraph expression) = buildgraph expression
