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

convert_fundef fundef (typerulemap,strictsmap,rulesmap,kindmap)
 = ( [(funsym,typerule):typerulemap]
   , [(funsym,stricts):strictsmap]
   , [(funsym,rules):rulesmap]
   , [(funsym,kind):kindmap]
   )
   where {fun_symb,fun_body,fun_type,fun_kind} = fundef
         funsym = SuclUser fun_symb
         (typerule,stricts) = foldoptional notyperule convert_symboltype fun_type
         notyperule = abort "convert: convert_fundef: fun_type is absent"
         rules = convert_functionbody fun_body
         kind = convert_kind fun_kind

/* Convert the SymbolType data structure
   This type describes the types of (function) symbols
   We use the principal type
   Strictness annotations are to be done yet
*/
convert_symboltype :: SymbolType -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])
convert_symboltype {st_vars,st_args,st_arity,st_result,st_context,st_attr_vars,st_attr_env}
 = (mkrule typeargs typeroot graph``,nostricts)
   where (heap`,(graph``,typeargs)) = convert_atypes (sucltypeheap,graph`) st_args
         (_,(graph`,[typeroot:_])) = convert_atype st_result (heap`,(emptygraph,[]))
         nostricts = abort "convert_symboltype: strictness info not implemented"

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
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable])
    )
convert_atypes (heap,graph) atypes
 = foldlr convert_atype (heap,(graph,[])) atypes

convert_atype
 :: AType
    ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable])
    )
 -> ( ([SuclTypeVariable])
    , (Graph SuclTypeSymbol SuclTypeVariable,[SuclTypeVariable])
    )
convert_atype atype (heap,(graph,rest))
 = case atype.at_type
   of

      // An ordinary type application
      TA typename atypes
       -> (heap``,(updategraph typevar (typesym,typeargs) graph`,[typevar:rest]))
          where (heap``,(graph`,typeargs)) = convert_atypes (heap`,graph) atypes
                [typevar:heap`] = heap
                typesym = SuclUSER typename

      // A function type (a->b)
      functype --> argtype
       -> (heap```,(graph```,[suclrestype:rest]))
          where (heap``,(graph``,fnargs)) = convert_atype functype (heap`,(graph`,suclargtype))
                (heap```,(graph`,suclargtype)) = convert_atype argtype (heap``,(graph,[]))
                [suclrestype:heap`] = heap
                graph``` = updategraph suclrestype (SuclFN,fnargs) graph``

      // A basic type, which is translated to an application of a basic type symbol to the empty list of arguments
      TB basictype
       -> (heap`,(graph`,[suclbasictype:rest]))
          where [suclbasictype:heap`] = heap
                graph` = updategraph suclbasictype (convert_btype basictype,[]) graph

      // A type variable, used in polymorphism
      TV tvname
       -> (heap,(graph,[sucltypevar:rest]))
          where sucltypevar = SuclNAMED tvname

      // Anything else will produce an error when actually used
      _
       -> (heap`,(graph`,[typevar:rest]))
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
convert_btype _ = abort "convert: convert_btype: unhandled basic type"

convert_functionbody :: FunctionBody -> [Rule SuclSymbol SuclVariable]
convert_functionbody _ = abort "convert: convert_functionbody: not implemented"

convert_kind :: DefOrImpFunKind -> SuclSymbolKind
convert_kind _ = abort "convert: convert_kind: not implemented"
