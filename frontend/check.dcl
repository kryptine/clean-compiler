definition module check

import syntax, transform, checksupport, typesupport, predef

checkModule :: !Bool !ScannedModule !IndexRange ![FunDef] !Int !(Optional ScannedModule) ![ScannedModule] !{#DclModule} !*{#*{#FunDef}} !*PredefinedSymbols !*SymbolTable !*File !*Heaps
	-> (!Bool, *IclModule, *{# DclModule}, *{! Group}, !*{#*{#FunDef}},!Int, !*Heaps, !*PredefinedSymbols, !*SymbolTable, *File, [String])

checkFunctions :: !Index !Level !Index !Index !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
											   -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState)

checkDclMacros :: !Index !Level !Index !Index !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
										  -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState)

checkForeignExportedFunctionTypes :: !*ErrorAdmin ![ForeignExport] !*{#FunDef} -> (!*ErrorAdmin,!*{#FunDef})
										  
determineTypeOfMemberInstance :: !SymbolType ![TypeVar] !InstanceType !Specials !*TypeHeaps !u:(Optional (v:{#DclModule}, w:{#CheckedTypeDef}, Index)) !*ErrorAdmin
		-> (!SymbolType, !Specials, !*TypeHeaps, !u:Optional (v:{#DclModule}, w:{#CheckedTypeDef}), !*ErrorAdmin)

arrayFunOffsetToPD_IndexTable :: !w:{# MemberDef} !v:{# PredefinedSymbol} -> (!{# Index}, !x:{#MemberDef}, !v:{#PredefinedSymbol}) , [w<=x]

makeElemTypeOfArrayFunctionStrict :: !SymbolType !Index !{# Index} -> SymbolType

initializeContextVariables :: ![TypeContext] !*VarHeap ->  (![TypeContext], !*VarHeap)
