definition module check

import syntax, transform, checksupport, typesupport, predef

cPredefinedModuleIndex 		:== 1

checkModule :: !ScannedModule !IndexRange ![FunDef] !Int !Int !(Optional ScannedModule) ![ScannedModule] !{#DclModule} !{#FunDef} !*PredefinedSymbols !*SymbolTable !*File !*Heaps
	-> (!Bool, *IclModule, *{# DclModule}, *{! Group}, !(Optional {# Index}), !.{#FunDef},!Int, !*Heaps, !*PredefinedSymbols, !*SymbolTable, *File /* TD */, [String])

checkFunctions :: !Index !Level !Index !Index !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef}, !*ExpressionInfo, !*Heaps, !*CheckState)

determineTypeOfMemberInstance :: !SymbolType ![TypeVar] !InstanceType !Specials !*TypeHeaps !u:(Optional (v:{#DclModule}, w:{#CheckedTypeDef}, Index)) !(Optional *ErrorAdmin)
		-> (!SymbolType, !Specials, !*TypeHeaps, !u:Optional (v:{#DclModule}, w:{#CheckedTypeDef}), !Optional *ErrorAdmin)

arrayFunOffsetToPD_IndexTable :: !w:{# MemberDef} !v:{# PredefinedSymbol} -> (!{# Index}, !x:{#MemberDef}, !v:{#PredefinedSymbol}) , [w<=x]

makeElemTypeOfArrayFunctionStrict :: !SymbolType !Index !{# Index} -> SymbolType

initializeContextVariables :: ![TypeContext] !*VarHeap ->  (![TypeContext], !*VarHeap)
