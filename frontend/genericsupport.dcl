definition module genericsupport

import syntax, checksupport

lookupGenericClassInfo :: 
		!TypeKind 
		!GenericClassInfos	
	-> 	(Optional GenericClassInfo)

addGenericClassInfo :: 
		!GenericClassInfo 
		!GenericClassInfos 
	->	GenericClassInfos

getGenericClassInfo ::
	!(Global Index)
	!TypeKind
	!{#CommonDefs}		
	!*GenericHeap
	-> 		
	( Optional GenericClassInfo
	, !*GenericHeap					
	)
getGenericMember :: 
	!(Global Index) 	// generic
	!TypeKind 			// kind argument
	!{#CommonDefs} 		// modules
	!*GenericHeap
	-> 		
	( Optional (Global Index)
	, !*GenericHeap					
	)

getGenericClass :: 
	!(Global Index) 	// generic
	!TypeKind 			// kind argument
	!{#CommonDefs} 		// modules
	!*GenericHeap
	-> 		
	( Optional (Global Index)
	, !*GenericHeap					
	)


//****************************************************************************************
//	Ident Helpers
//****************************************************************************************
makeIdent 					:: !String -> Ident
postfixIdent 				:: !Ident !String -> Ident
genericIdentToClassIdent 	:: !Ident !TypeKind -> Ident
genericIdentToMemberIdent 	:: !Ident !TypeKind -> Ident
genericIdentToFunIdent 		:: !Ident !TypeCons -> Ident
