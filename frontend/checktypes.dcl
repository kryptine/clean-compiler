definition module checktypes

import checksupport, typesupport

checkTypeDefs :: !Index !(Optional (CopiedDefinitions, Int)) !*{# CheckedTypeDef} !*{# ConsDef} !*{# SelectorDef} !*{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
	-> (!*{# CheckedTypeDef}, !*{# ConsDef}, !*{# SelectorDef}, !*{# DclModule}, !*VarHeap, !*TypeHeaps, !*CheckState)

checkFunctionType :: !Index !SymbolType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkMemberType :: !Index !SymbolType !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkInstanceType :: !Index !(Global DefinedSymbol) !InstanceType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!InstanceType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkSuperClasses :: ![TypeVar] ![TypeContext] !Index !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (![TypeVar], ![TypeContext], !u:{#CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)

checkDynamicTypes :: !Index ![ExprInfoPtr] !(Optional SymbolType) !u:{# CheckedTypeDef} !u:{# DclModule} !*TypeHeaps !*ExpressionHeap !*CheckState
	-> (!u:{# CheckedTypeDef}, !u:{# DclModule}, !*TypeHeaps, !*ExpressionHeap, !*CheckState)

createClassDictionaries ::		  !Bool !Index !Index !Index !Index !*{#CheckedTypeDef} !*{# SelectorDef} !*{# ConsDef} !*{#ClassDef} !*{#DclModule} !*TypeVarHeap !*VarHeap !*SymbolTable
	-> (![CheckedTypeDef],![SelectorDef],![ConsDef],!DictionaryInfo,!*{#CheckedTypeDef},!*{# SelectorDef},!*{# ConsDef},!*{#ClassDef},!*{#DclModule},!*TypeVarHeap,!*VarHeap,!*SymbolTable)

removeVariablesFromSymbolTable :: !Int ![TypeVar] !*SymbolTable -> *SymbolTable
