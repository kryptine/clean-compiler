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

convert_symboltype :: SymbolType -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])
convert_symboltype {st_vars,st_args,st_arity,st_result,st_context,st_attr_vars,st_attr_env}
 = (mkrule typeargs typeroot graph``,nostricts)
   where (heap`,(graph``,typeargs)) = convert_atypes (sucltypeheap,graph`) st_args
         (_,(graph`,[typeroot:_])) = convert_atype st_result (heap`,(emptygraph,[]))
         nostricts = abort "convert_symboltype: strictness info not implemented"

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
   of TA typename atypes
       -> (heap``,(updategraph typevar (typesym,typeargs) graph`,[typevar:rest]))
          where (heap``,(graph`,typeargs)) = convert_atypes (heap`,graph) atypes
                [typevar:heap`] = heap
                typesym = SuclUSER typename
      functype --> argtype
       -> (heap```,(graph```,[suclrestype:rest]))
          where (heap``,(graph``,fnargs)) = convert_atype functype (heap`,(graph`,suclargtype))
                (heap```,(graph`,suclargtype)) = convert_atype argtype (heap``,(graph,[]))
                [suclrestype:heap`] = heap
                graph``` = updategraph suclrestype (SuclFN,fnargs) graph``

      TB basictype
       -> (heap`,(graph`,[suclbasictype:rest]))
          where [suclbasictype:heap`] = heap
                graph` = updategraph suclbasictype (convert_btype basictype,[]) graph
      TV tvname
       -> (heap,(graph,[sucltypevar:rest]))
          where sucltypevar = SuclNAMED tvname
      _
       -> (heap`,(graph`,[typevar:rest]))
          where [typevar:heap`] = heap
                graph` = updategraph typevar notimpl graph
                notimpl = abort "convert_atype: unknown form of Type"

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
