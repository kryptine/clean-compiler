definition module check

import syntax, transform, checksupport, typesupport, predef

//MOVE
//cIclModIndex 			:== 0
cPredefinedModuleIndex 		:== 1

checkModule :: !ScannedModule !Int ![FunDef] !ScannedModule !ScannedModule ![ScannedModule] !*PredefinedSymbols !*SymbolTable !*File
	-> (!Bool, !*IclModule, *{# DclModule}, *{! Group}, !(Optional {# Index}), !*Heaps, !*PredefinedSymbols, !*SymbolTable, *File)

retrieveGlobalDefinition :: !SymbolTableEntry !STE_Kind !Index -> (!Index, !Index)

newFreeVariable :: !FreeVar ![FreeVar] ->(!Bool, ![FreeVar])

convertIndex :: !Index !Index !(Optional ConversionTable) -> !Index

determineTypeOfMemberInstance :: !SymbolType ![TypeVar] !InstanceType !Specials !*TypeHeaps -> (!SymbolType, !Specials, !*TypeHeaps)


arrayFunOffsetToPD_IndexTable :: !{# MemberDef} !v:{# PredefinedSymbol} -> (!{# Index}, !{#MemberDef}, !v:{#PredefinedSymbol})

makeElemTypeOfArrayFunctionStrict :: !SymbolType !Index !{# Index} -> SymbolType
