implementation module convert

// $Id$

import coreclean
import rule
import graph
import basic
import syntax
import StdEnv

// Cocl to Sucl for functions
cts_function
 :: {#FunDef}
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    )

cts_function fundefs
 = foldr convert_fundef ([],[],[],[]) [fundef\\fundef<-:fundefs]

convert_fundef
 :: FunDef
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

convert_fundef fundef (typerulemap,strictsmap,fundefs0,kindmap)
 = ( [(funsym,typerule):typerulemap]
   , [(funsym,stricts):strictsmap]
   , fundefs1
   , [(funsym,kind):kindmap]
   )
   where {fun_symb,fun_body,fun_type,fun_kind} = fundef
         funsym = SuclUser fun_symb.id_info
         (typerule,stricts) = foldoptional notyperule convert_symboltype fun_type
         notyperule = abort "convert: convert_fundef: fun_type is absent"
         fundefs1 = convert_functionbody funsym fun_body fundefs0
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

convert_functionbody :: SuclSymbol FunctionBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_functionbody funsym (TransformedBody t) fundefs0 = convert_transformedbody funsym t fundefs0
convert_functionbody funsym _ fundefs0
 = [(funsym,norule):fundefs0]
   where norule = abort "convert: convert_functionbody: unexpected FunctionBody constructor"

convert_transformedbody :: SuclSymbol TransformedBody [FunBinding SuclSymbol SuclVariable] -> [FunBinding SuclSymbol SuclVariable]
convert_transformedbody funsym {tb_args=args,tb_rhs=expression} fundefs0
 | not (isEmpty globals0) // Sanity check, since we have it in our fingers anyway
   = abort "convert: convert_transformedbody: function rhs contains free variables!"
 = [(funsym,[mkrule (map snd seen0) (hd rest) (compilegraph nodes0)]):fundefs1]
   where (_,(nodes0,fundefs1,globals0,rest))
          = convert_expression [] expression ((heap0,seen0),([],fundefs0,[],[]))
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

convert_expressions bounds exprs (heapseen0,(nodes0,fundefs0,globals0))
 = foldlr (convert_expression bounds) (heapseen0,(nodes0,fundefs0,globals0,[])) exprs

convert_expression
 :: [(VarInfoPtr,Econv_state->Econv_state)]     // Locally bound variables, with the expressions they're bound to, for resolving locally bound variables
    Expression                                  // Expression to convert
    Econv_state                                 // Input expression conversion state
 -> Econv_state                                 // Resulting expression conversion state

convert_expression bounds (App appinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap2,seen1),(nodes2,fundefs1,globals1,[root:rest]))
   where [root:heap1] = heap0
         ((heap2,seen1),(nodes1,fundefs1,globals1,args0))
          = convert_expressions bounds appinfo.app_args ((heap1,seen0),(nodes0,fundefs0,globals0))
         nodes2 = [(root,(SuclUser appinfo.app_symb.symb_name.id_info,args0)):nodes1]

convert_expression bounds (expr @ exprs) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap2,seen1),(nodes2,fundefs1,globals1,[root:rest]))
   where [root:heap1] = heap0
         ((heap2,seen1),(nodes1,fundefs1,globals1,args0))
          = convert_expressions bounds [expr:exprs] ((heap1,seen0),(nodes0,fundefs0,globals0))
         nodes2 = [(root,(SuclApply (length exprs),args0)):nodes1]

convert_expression bounds (Var varinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
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

convert_expression bounds0 (Let letinfo) ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = convert_expression bounds1 letinfo.let_expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
   where newbounds = [(lb.lb_dst.fv_info_ptr,convert_bound_expr bounds1 lb.lb_src) \\ lb<-letinfo.let_lazy_binds]
         bounds1 = newbounds++bounds0

convert_expression bounds (Case caseinfo) ((heap0,seen0),(nodes6,fundefs5,globals6,rest))
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
          = foldoptional id (convert_expression bounds) caseinfo.case_default ((heap3,seen2),(nodes6,fundefs5,globals6,[]))
         // (1) convert branches
         globals8 = removeDup (innerglobals++globals7)
         ((heap3,seen2),(innerglobals,fundefs7,alternatives))
          = case caseinfo.case_guards
            of AlgebraicPatterns _ branches
                -> foldlr convert_algebraic_branch ((heap2,seen1),([],fundefs6,[])) branches
               BasicPatterns _ branches
                -> foldlr convert_basic_branch ((heap2,seen1),([],fundefs6,[])) branches
               _
                -> ((heap2,seen1),([],fundefs6,abort "convert: convert_expression: unhandled CasePatterns constructor"))
         // (0.5) Convert selector
         ((heap2,seen1),(nodes8,fundefs8,globals9,selectorroots))
          = convert_expression bounds caseinfo.case_expr ((heap1,seen0),(nodes7,fundefs7,globals8,[]))
         // (0) Claim root node
         [root:heap1] = heap0

convert_algebraic_branch branch ((heap0,seen0),(globals0,fundefs0,alternatives0))
 = ((heap2,seen2),(globals1,fundefs1,alternatives1))
   where ((heap1,seen1),(nodes0,patrest))
          = convert_algebraic_pattern branch ((heap0,seen0),([],[]))
         ((heap2,seen2),(nodes1,fundefs1,globals1,rest))
          = convert_expression [] branch.ap_expr ((heap1,seen1),(nodes0,fundefs0,globals0,[]))
         alternatives1 = [(hd patrest,hd rest,nodes1):alternatives0]

convert_algebraic_pattern ap ((heap0,seen0),(nodes0,rest))
 = ((heap1,seen1),(nodes1,[root:rest]))
   where [root:heap1] = heap0
         argmap = [(fv.fv_info_ptr,SuclNamed fv.fv_info_ptr) \\ fv <- ap.ap_vars]
         seen1 = argmap++seen0
         args0 = map snd argmap
         nodes1 = [(root,(SuclUser ap.ap_symbol.glob_object.ds_ident.id_info,args0)):nodes0]

convert_basic_branch branch ((heap0,seen0),(globals0,fundefs0,alternatives0))
 = ((heap2,seen2),(globals1,fundefs1,alternatives1))
   where ((heap1,seen1),(nodes0,patrest))
          = convert_basic_pattern branch ((heap0,seen0),([],[]))
         ((heap2,seen2),(nodes1,fundefs1,globals1,rest))
          = convert_expression [] branch.bp_expr ((heap1,seen1),(nodes0,fundefs0,globals0,[]))
         alternatives1 = [(hd patrest,hd rest,nodes1):alternatives0]

convert_basic_pattern bp ((heap0,seen0),(nodes0,rest))
 = ((heap1,seen0),(nodes1,[root:rest]))
   where [root:heap1] = heap0
         nodes1 = [(root,(convert_bvalue bp.bp_value,[])):nodes0]

convert_bound_expr bounds expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))
 = ((heap1,seen1),(nodes1,fundefs1,globals1,rest`))
   where ((heap1,seen1),(nodes1,fundefs1,globals1,rest`))
          = convert_expression bounds expr ((heap0,seen0),(nodes0,fundefs0,globals0,rest))

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

cts_exports :: {#FunType} -> [SuclSymbol]
cts_exports funtypes = [convert_funtype funtype\\funtype<-:funtypes]

convert_funtype :: FunType -> SuclSymbol
convert_funtype funtype = SuclUser funtype.ft_symb.id_info
