implementation module convert

// $Id$

import newfold
import coreclean
import rule
import graph
import basic
import checksupport
import syntax
import StdEnv

// Cocl to Sucl for functions
cts_function
 :: Int                                                 // Index of current module
    {#FunDef}                                           // Function definitions (from ICL)
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    )

cts_function main_dcl_module_n fundefs
 = foldr (convert_fundef main_dcl_module_n) ([],[],[],[]) [fundef\\fundef<-:fundefs]

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
                        typesym = SuclUSER typename

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

cts_exports :: {#FunDef} {#DclModule} Int -> [SuclSymbol]
cts_exports fun_defs dcl_mods main_dcl_module_n
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

/*
stc_funcdef ::
    {#DclModule}
    (FuncDef SuclSymbol SuclVariable)
 -> FunctionBody

stc_funcdef dcl_mods (args,body)
= TransformedBody tb
  where tb
        = { tb_args = map convert_symbol args
          , tb_rhs  = convert_funcbody dcl_mods body
          }

convert_symbol :: SuclSymbol -> FreeVar

*/

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

/*
convert_funcbody ::
    {#DclModule}                        // DCL modules
    Level                               // Level for newly introduced freevars (cases)
    (SuclVariable -> FreeVar)           // Mapping variables to freevars
    u:ExpressionHeap                    // Supply of ExprInfoPtrs
    (v:Heap VarInfo)                    // Supply of FreeVars and BoundVars
    (FuncBody SuclSymbol SuclVariable)  // Function body to convert
 -> ( u:ExpressionHeap
    , v:Heap VarInfo
    , Expression
    )
*/

convert_funcbody dcl_mods level freevarenv exprheap0 varheap0 (MatchPattern pattern yesbody nobody)
= (exprheap2,varheap2,Let li)
  where (exprheap1,varheap1,case_expression,default_refcount)
        = convert_matchpatterns dcl_mods build_casebranch freevarenv exprheap0 varheap0 (Var default_boundvar) pgraph level [proot]
        pgraph = rgraphgraph pattern
        proot = rgraphroot pattern
        default_boundvar
        = { var_name = default_ident
          , var_info_ptr = default_info_ptr
          , var_expr_ptr = default_expression
          }
        (default_info_ptr,varheap2) = newPtr VI_Empty varheap1
        (letinfoptr,exprheap2) = newPtr EI_Empty exprheap1
        li
        = { let_strict_binds = []
          , let_lazy_binds = [{lb_dst=default_freevar,lb_src=default_expression,lb_position=NoPos}]
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
        build_casebranch level` freevarenv` exprheap0` varheap0`
        = (exprheap1`,varheap1`,expr`,0)
          where (exprheap1`,varheap1`,expr`)
                = convert_funcbody dcl_mods level` freevarenv` exprheap0` varheap0` yesbody

default_expression = undef

convert_matchpatterns ::
    {#DclModule}                    // DCL modules
    (  Int                          // Level to assign to free variables
       (SuclVariable->FreeVar)      // Assigning FreeVars to variables from the environment
       *ExpressionHeap              // Initial expression heap for case branch
    ->*(  (*Heap VarInfo)           // Initial variable heap for case branch
       -> ( *ExpressionHeap         // Modified expression heap from case branch
          , *Heap VarInfo           // Modified variable heap from case branch
          , Expression              // Resulting branch expression
          , Int                     // Reference count to default expression
          )
       )
    )
    (SuclVariable->FreeVar)         // Assigning FreeVars to variables from the environment
    *ExpressionHeap                 // Initial expression heap
    (*Heap VarInfo)                 // Initial variable heap
    Expression                      // Default expression
    (Graph SuclSymbol SuclVariable) // Case pattern to convert
    Level                           // Level to assign to fresh free variables
    [SuclVariable]                  // Subsequent variables in pattern to match
 -> ( *ExpressionHeap               // Modified expression heap
    , *Heap VarInfo                 // Modified variable heap
    , Expression                    // Resulting (case) expression
    , Int                           // Modified reference count to default expression
    )

convert_matchpatterns dcl_mods build_casebranch freevarenv exprheap0 varheap0 default_expression pgraph level []
= (exprheap1,varheap1,case_expression,refcount)
  where (exprheap1,varheap1,case_expression,refcount)
        = build_casebranch level freevarenv exprheap0 varheap0

convert_matchpatterns dcl_mods build_casebranch0 freevarenv0 exprheap0 varheap0 default_expression pgraph level [pnode:pnodes]
| pdef
  = convert_matchpattern dcl_mods build_remaining_matcher freevarenv0 exprheap0 varheap0 default_expression pgraph level pnode psym pargs
= build_remaining_matcher level freevarenv0 exprheap0 varheap0
  where (pdef,(psym,pargs)) = varcontents pgraph pnode
        build_remaining_matcher level` freevarenv` exprheap` varheap`
        = convert_matchpatterns dcl_mods build_casebranch0 freevarenv` exprheap` varheap` default_expression pgraph level` pnodes

convert_matchpattern ::
    {#DclModule}                    // DCL modules
    (  Level                        // Level to assign to free variables
       (SuclVariable->FreeVar)      // Assigning FreeVars to variables from the environment
       *ExpressionHeap              // Initial expression heap for case branch
    ->*(  (*Heap VarInfo)           // Initial variable heap for case branch
       -> ( *ExpressionHeap         // Modified expression heap from case branch
          , *Heap VarInfo           // Modified variable heap from case branch
          , Expression              // Resulting branch expression
          , Int                     // Reference count to default expression
          )
       )
    )
    (SuclVariable->FreeVar)         // Assigning FreeVars to variables from the environment
    *ExpressionHeap                 // Initial expression heap
    (*Heap VarInfo)                 // Initial variable heap
    Expression                      // Default expression
    (Graph SuclSymbol SuclVariable) // Case pattern to convert
    Level                           // Level to assign to fresh free variables
    SuclVariable
    SuclSymbol
    [SuclVariable]                  // Subsequent variables in pattern to match
 -> ( *ExpressionHeap               // Modified expression heap
    , *Heap VarInfo                 // Modified variable heap
    , Expression                    // Resulting (case) expression
    , Int                           // Modified reference count to default expression
    )

convert_matchpattern dcl_mods build_casebranch freevarenv0 exprheap0 varheap0 default_expression pgraph level pnode psym pargs
= (exprheap2,varheap1,case_expression,1+refcount)
  where (exprheap2,varheap1,branch_expression,refcount)
        = convert_matchpatterns dcl_mods build_casebranch freevarenv1 exprheap1 varheap0 default_expression pgraph (level+1) pargs
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
        cps = convert_constructor dcl_mods psym pargs branch_expression

default_refcount1 = undef
freevarenv1 = undef

convert_constructor :: {#DclModule} SuclSymbol [SuclVariable] Expression -> CasePatterns
convert_constructor dcl_mods (SuclUser (SK_Constructor consindex)) pargs expr
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
		  , ap_vars     = abort "allocate fresh freevars"
		  , ap_expr	    = expr
		  , ap_position = NoPos
		  }

fold_funcbody ::
    ((Rgraph sym var) .result .result -> .result)
    ((Rgraph sym var) -> .result)
    (FuncBody sym var)
 -> .result

fold_funcbody matchpattern buildgraph funcbody
= fold funcbody
  where fold (MatchPattern pattern yesbody nobody) = matchpattern pattern (fold yesbody) (fold nobody)
        fold (BuildGraph expression) = buildgraph expression
