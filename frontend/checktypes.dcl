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

createClassDictionaries ::
	Index                   // Index of module being converted
	*{#ClassDef}            // Array of classes to convert
	u1:{#MemberDef}         // Array of class members of classes to convert
	u2:{#.DclModule}        // DCL modules for looking up context classes
	u3:{#CheckedTypeDef}    // Typedef array to update with dictionary type
	u4:{#SelectorDef}       // Selectordef array to update with dictionary field selectors
	u5:{#ConsDef}           // Consdef array to update with dictionary constructor
	*TypeHeaps              // Heaps to allocate fresh type and attribute variables from
	*VarHeap                // Heap to allocate fresh variable from
	*SymbolTable            // Symbol table to store dictionary types, constructors, and field selectors
 ->	( .{#ClassDef}          // Updated array of classes (class_dictionary is updated)
	, v1:{#MemberDef}       // Consulted array of class members
	, v2:{#DclModule}       // Consulted DCL modules
	, v3:{#CheckedTypeDef}  // Typedef array extended with dictionary types
	, v4:{#SelectorDef}     // Selectordef array extended with dictionary field selectors
	, v5:{#ConsDef}         // Consdef array extended with dictionary constructors
	, .TypeHeaps            // Updated and extended type heaps
	, .VarHeap              // Updated and extended heap
	, .SymbolTable          // Extended symbol table
	)
 ,	[u1<=v1, u2<=v2, u3<=v3, u4<=v4, u5<=v5]

removeVariablesFromSymbolTable :: !Int ![TypeVar] !*SymbolTable -> *SymbolTable
