definition module checktypes

import checksupport, typesupport

checkTypeDefs :: !Index !(Optional (CopiedDefinitions, Int)) !*{# CheckedTypeDef} !*{# ConsDef} !*{# SelectorDef} !*{# DclModule} !*Heaps !*CheckState
	-> (!*{# CheckedTypeDef}, !*{# ConsDef}, !*{# SelectorDef}, !*{# DclModule}, !*Heaps, !*CheckState)

checkFunctionType :: !Index !SymbolType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkMemberType :: !Index !SymbolType !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

//1.3
checkInstanceType :: !Index !(Global DefinedSymbol) !InstanceType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
//3.1
/*2.0
checkInstanceType :: !Index !(Global DefinedSymbol) !InstanceType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
0.2*/
	-> (!InstanceType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkSuperClasses :: ![TypeVar] ![TypeContext] !Index !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (![TypeVar], ![TypeContext], !u:{#CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkDynamicTypes :: !Index ![ExprInfoPtr] !(Optional SymbolType) !u:{# CheckedTypeDef} !u:{# DclModule} !*TypeHeaps !*ExpressionHeap !*CheckState
	-> (!u:{# CheckedTypeDef}, !u:{# DclModule}, !*TypeHeaps, !*ExpressionHeap, !*CheckState)

createClassDictionaries ::		  !Bool !Index !Index !Index !Index !*{#CheckedTypeDef} !*{# SelectorDef} !*{# ConsDef} !*{#ClassDef} !*{#DclModule} !*TypeVarHeap !*VarHeap !*SymbolTable
	-> (![CheckedTypeDef],![SelectorDef],![ConsDef],!DictionaryInfo,!*{#CheckedTypeDef},!*{# SelectorDef},!*{# ConsDef},!*{#ClassDef},!*{#DclModule},!*TypeVarHeap,!*VarHeap,!*SymbolTable)

removeVariablesFromSymbolTable :: !Int ![TypeVar] !*SymbolTable -> *SymbolTable
