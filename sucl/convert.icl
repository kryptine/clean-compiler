implementation module convert

// $Id$

import coreclean
import rule
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
convert_symboltype _ = abort "convert: convert_symboltype: not implemented"

convert_functionbody :: FunctionBody -> [Rule SuclSymbol SuclVariable]
convert_functionbody _ = abort "convert: convert_functionbody: not implemented"

convert_kind :: DefOrImpFunKind -> SuclSymbolKind
convert_kind _ = abort "convert: convert_kind: not implemented"

foldoptional no yes No = no
foldoptional no yes (Yes value) = yes value
