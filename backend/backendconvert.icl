implementation module backendconvert

import code from library "backend_library"

import StdEnv

import frontend
import backend
import backendsupport, backendpreprocess
import RWSDebug

// trace macro
(-*->) infixl
(-*->) value trace
	:==	value // ---> trace
/*
sfoldr op r l
	:== foldr l
	where
		foldr [] = r
		foldr [a:x] = \s -> op a (foldr x) s
*/
sfoldr op r l s
	:== foldr l s
	where
		foldr [] = r
		foldr [a:x] = op a (foldr x)

:: BEMonad a :== St !*BackEndState !a

:: BackEnder :== *BackEndState -> *BackEndState

//
:: *BackEndState = {bes_backEnd :: !BackEnd, bes_varHeap :: !*VarHeap}

appBackEnd f beState
	:== {beState & bes_backEnd = bes_backEnd}
	where
		bes_backEnd = f beState.bes_backEnd

accBackEnd f beState
	:== accBackEnd
	where
		accBackEnd
			# (result, bes_backEnd) =	f beState.bes_backEnd
			#! beState2 = {beState & bes_backEnd = bes_backEnd}
			= (result,beState2)

accVarHeap f beState
	:== (result, {beState & bes_varHeap = varHeap})
	where
		(result, varHeap) =	f beState.bes_varHeap

read_from_var_heap ptr _ beState
	= (result, {beState & bes_varHeap = varHeap})
where
		(result, varHeap) =	readPtr ptr beState.bes_varHeap

write_to_var_heap ptr v beState
	= {beState & bes_varHeap = writePtr ptr v beState.bes_varHeap}
/*
read_from_var_heap ptr heap be
	= (sreadPtr ptr heap,be)

::	*BackEndState :== BackEnd

appBackEnd f beState :== f beState
accBackEnd f beState :== f beState
accVarHeap f beState :== f beState
*/

beApFunction0 f
	:== appBackEnd f
beApFunction1 f m1
	:== m1 ==> \a1
	->	appBackEnd (f a1)
beApFunction2 f m1 m2
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	appBackEnd (f a1 a2)
beApFunction3 f m1 m2 m3
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	appBackEnd (f a1 a2 a3)
beApFunction4 f m1 m2 m3 m4
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	appBackEnd (f a1 a2 a3 a4)
beApFunction5 f m1 m2 m3 m4 m5
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	appBackEnd (f a1 a2 a3 a4 a5)
beApFunction6 f m1 m2 m3 m4 m5 m6
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	appBackEnd (f a1 a2 a3 a4 a5 a6)
beApFunction7 f m1 m2 m3 m4 m5 m6 m7
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	m7 ==> \a7
	->	appBackEnd (f a1 a2 a3 a4 a5 a6 a7)

beFunction0 f
	:== accBackEnd f
beFunction1 f m1
	:== m1 ==> \a1
	->	accBackEnd (f a1)
beFunction2 f m1 m2
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	accBackEnd (f a1 a2)
beFunction3 f m1 m2 m3
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	accBackEnd (f a1 a2 a3)
beFunction4 f m1 m2 m3 m4
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	accBackEnd (f a1 a2 a3 a4)
beFunction5 f m1 m2 m3 m4 m5
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	accBackEnd (f a1 a2 a3 a4 a5)
beFunction6 f m1 m2 m3 m4 m5 m6
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	accBackEnd (f a1 a2 a3 a4 a5 a6)
beFunction7 f m1 m2 m3 m4 m5 m6 m7
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	m7 ==> \a7
	->	accBackEnd (f a1 a2 a3 a4 a5 a6 a7)

changeArrayFunctionIndex selectIndex
	:== selectIndex

beBoolSymbol value
	:==	beFunction0 (BEBoolSymbol value)
beLiteralSymbol type value
	:==	beFunction0 (BELiteralSymbol type value)
beFunctionSymbol functionIndex moduleIndex
	:==	beFunction0 (BEFunctionSymbol functionIndex moduleIndex)
beSpecialArrayFunctionSymbol arrayFunKind functionIndex moduleIndex
	:==	beFunction0 (BESpecialArrayFunctionSymbol arrayFunKind (changeArrayFunctionIndex functionIndex) moduleIndex)
beDictionarySelectFunSymbol
	:==	beFunction0 BEDictionarySelectFunSymbol
beDictionaryUpdateFunSymbol
	:==	beFunction0 BEDictionaryUpdateFunSymbol
beConstructorSymbol moduleIndex constructorIndex
	:==	beFunction0 (BEConstructorSymbol constructorIndex moduleIndex)
beFieldSymbol fieldIndex moduleIndex
	:==	beFunction0 (BEFieldSymbol fieldIndex moduleIndex)
beTypeSymbol typeIndex moduleIndex
	:==	beFunction0 (BETypeSymbol typeIndex moduleIndex)
beBasicSymbol typeSymbolIndex
	:==	beFunction0 (BEBasicSymbol typeSymbolIndex)
beDontCareDefinitionSymbol
	:==	beFunction0 BEDontCareDefinitionSymbol
beNoArgs
	:==	beFunction0 BENoArgs
beArgs
	:==	beFunction2 BEArgs
beNoTypeArgs
	:==	beFunction0 BENoTypeArgs
beTypeArgs
	:==	beFunction2 BETypeArgs
beNormalNode
	:==	beFunction2 BENormalNode
beIfNode
	:==	beFunction3 BEIfNode
beGuardNode
	:==	beFunction7 BEGuardNode
beSelectorNode selectorKind
	:==	beFunction2 (BESelectorNode selectorKind)
beUpdateNode
	:==	beFunction1 BEUpdateNode
beNormalTypeNode
	:==	beFunction2 BENormalTypeNode
beVarTypeNode name
	:==	beFunction0 (BEVarTypeNode name)
beRuleAlt lineNumber
	:==	beFunction5 (BERuleAlt lineNumber)
beNoRuleAlts
	:==	beFunction0 BENoRuleAlts
beRuleAlts
	:==	beFunction2 BERuleAlts
beTypeAlt
	:==	beFunction2 BETypeAlt
beRule index isCaf
	:==	beFunction2 (BERule index isCaf)
beNoRules
	:==	beFunction0 BENoRules
beRules
	:==	beFunction2 BERules
beNodeDef sequenceNumber
	:==	beFunction1 (BENodeDef sequenceNumber)
beNoNodeDefs
	:==	beFunction0 BENoNodeDefs
beNodeDefs
	:==	beFunction2 BENodeDefs
beStrictNodeId
	:==	beFunction1 BEStrictNodeId
beNoStrictNodeIds
	:==	beFunction0 BENoStrictNodeIds
beStrictNodeIds
	:==	beFunction2 BEStrictNodeIds
beNodeIdNode
	:==	beFunction2 BENodeIdNode
beNodeId sequenceNumber
	:==	beFunction0 (BENodeId sequenceNumber)
beWildCardNodeId
	:==	beFunction0 BEWildCardNodeId
beConstructor
	:==	beFunction1 BEConstructor
beNoConstructors
	:==	beFunction0 BENoConstructors
beConstructors
	:==	beFunction2 BEConstructors
beNoFields
	:==	beFunction0 BENoFields
beFields
	:==	beFunction2 BEFields
beField fieldIndex moduleIndex 
	:==	beFunction1 (BEField fieldIndex moduleIndex)
beAnnotateTypeNode annotation
	:==	beFunction1 (BEAnnotateTypeNode annotation)
beAttributeTypeNode attribution
	:==	beFunction1 (BEAttributeTypeNode attribution)
beDeclareRuleType functionIndex moduleIndex name
	:==	beApFunction0 (BEDeclareRuleType functionIndex moduleIndex name)
beDefineRuleType functionIndex moduleIndex
	:==	beApFunction1 (BEDefineRuleType functionIndex moduleIndex)
beCodeAlt lineNumber
	:==	beFunction3 (BECodeAlt lineNumber)
beString string
	:==	beFunction0 (BEString string)
beStrings
	:==	beFunction2 BEStrings
beNoStrings
	:==	beFunction0 BENoStrings
beCodeParameter location
	:==	beFunction1 (BECodeParameter location)
beCodeParameters
	:==	beFunction2 BECodeParameters
beNoCodeParameters
	:==	beFunction0 BENoCodeParameters
beAbcCodeBlock inline
	:==	beFunction1 (BEAbcCodeBlock inline)
beAnyCodeBlock
	:==	beFunction3 BEAnyCodeBlock
beDeclareNodeId number lhsOrRhs name
	:==	beApFunction0 (BEDeclareNodeId number lhsOrRhs name)
beAdjustArrayFunction backendId functionIndex moduleIndex
	:==	beApFunction0 (BEAdjustArrayFunction backendId functionIndex moduleIndex)
beFlatType
	:==	beFunction2 BEFlatType
beNoTypeVars
	:==	beFunction0 BENoTypeVars
beTypeVars
	:==	beFunction2 BETypeVars
beTypeVar name
	:==	beFunction0 (BETypeVar name)
beExportType dclTypeIndex iclTypeIndex
	:==	beApFunction0 (BEExportType dclTypeIndex iclTypeIndex)
beExportConstructor dclConstructorIndex iclConstructorIndex
	:==	beApFunction0 (BEExportConstructor dclConstructorIndex iclConstructorIndex)
beExportField dclFieldIndex iclFieldIndex
	:==	beApFunction0 (BEExportField dclFieldIndex iclFieldIndex)
beExportFunction dclIndexFunctionIndex iclFunctionIndex
	:==	beApFunction0 (BEExportFunction dclIndexFunctionIndex iclFunctionIndex)
beTupleSelectNode arity index
	:==	beFunction1 (BETupleSelectNode arity index)
beMatchNode arity
	:==	beFunction2 (BEMatchNode arity)
beDefineImportedObjsAndLibs
	:== beApFunction2 BEDefineImportedObjsAndLibs
beAbsType
	:== beApFunction1 BEAbsType

notYetImplementedExpr :: Expression
notYetImplementedExpr
	=	(BasicExpr (BVS "\"error in compiler (something was not implemented by lazy Ronny)\"") BT_Int)

backEndConvertModules :: PredefinedSymbols FrontEndSyntaxTree !Int *VarHeap *BackEnd -> (!*VarHeap,!*BackEnd)
/*
backEndConvertModules p s main_dcl_module_n v be
	= (newHeap,backEndConvertModulesH p s v be)
*/
backEndConvertModules p s main_dcl_module_n var_heap be
	# {bes_varHeap,bes_backEnd} = backEndConvertModulesH p s main_dcl_module_n newHeap {bes_varHeap=var_heap,bes_backEnd=be}
	= (bes_varHeap,bes_backEnd)

backEndConvertModulesH :: PredefinedSymbols FrontEndSyntaxTree !Int VarHeap *BackEndState -> *BackEndState
backEndConvertModulesH predefs {fe_icl = fe_icl =: {icl_name, icl_functions, icl_common, icl_imported_objects,icl_used_module_numbers}, fe_components, fe_dcls, fe_arrayInstances, fe_dclIclConversions, fe_iclDclConversions,fe_globalFunctions} main_dcl_module_n varHeap backEnd
	// sanity check ...
//	| cIclModIndex <> kIclModuleIndex || cPredefinedModuleIndex <> kPredefinedModuleIndex
//		=	undef <<- "backendconvert, backEndConvertModules: module index mismatch"
	// ... sanity check
/*
	#  backEnd
		=	ruleDoesNotMatch 1 backEnd
			with
				ruleDoesNotMatch 0 backEnd
					=	backEnd
	#  backEnd
		=	abort "front end abort" backEnd
*/
	#! backEnd = appBackEnd (BESetMainDclModuleN main_dcl_module_n) backEnd
	#! backEnd
		=	appBackEnd (BEDeclareModules (size fe_dcls)) backEnd
	#! backEnd
		=	predefineSymbols fe_dcls.[cPredefinedModuleIndex] predefs backEnd

	#  currentDcl
	   	=	fe_dcls.[main_dcl_module_n]
	   typeConversions
		=	currentModuleTypeConversions icl_common.com_class_defs currentDcl.dcl_common.com_class_defs currentDcl.dcl_conversions
/*
	# 	rstypes = reshuffleTypes (size icl_common.com_type_defs) typeConversions {type.td_name.id_name \\ type <-: currentDcl.dcl_common.com_type_defs}
		types = {type.td_name.id_name \\ type <-: icl_common.com_type_defs}
	#  backEnd
		=	backEnd ->>
				(	"dcl conversions"
				,	currentDcl.dcl_conversions
				,	"dcl constructors"
				,	[constructor.cons_symb.id_name \\ constructor <-: currentDcl.dcl_common.com_cons_defs]
				,	"dcl selectors"
				,	[selector.sd_symb.id_name \\ selector <-: currentDcl.dcl_common.com_selector_defs]
				,	"dcl types"
				,	[type.td_name.id_name \\ type <-: currentDcl.dcl_common.com_type_defs]
				,	"icl selectors"
				,	[constructor.cons_symb.id_name \\ constructor <-: icl_common.com_cons_defs]
				,	"icl fields"
				,	[selector.sd_symb.id_name \\ selector <-: icl_common.com_selector_defs]
				,	"icl types"
				,	[type.td_name.id_name \\ type <-: icl_common.com_type_defs]
				,	"compare names"
				,	(rstypes, types)
				)
*/
	#! backEnd
		=	declareCurrentDclModule fe_icl fe_dcls.[main_dcl_module_n] main_dcl_module_n (backEnd -*-> "declareCurrentDclModule")
	#! backEnd
		=	declareOtherDclModules fe_dcls main_dcl_module_n icl_used_module_numbers (backEnd -*-> "declareOtherDclModules")
	#! backEnd
		=	defineDclModule varHeap main_dcl_module_n fe_dcls.[main_dcl_module_n] (backEnd -*-> "defineDclModule(cIclMoIndex)")
	#! backEnd
		=	reshuffleTypes (size icl_common.com_type_defs) typeConversions (backEnd -*-> "reshuffleTypes")
	#! backEnd
		=	defineOtherDclModules fe_dcls main_dcl_module_n icl_used_module_numbers varHeap (backEnd -*-> "defineOtherDclModules")

	#! backEnd
		=	appBackEnd (BEDeclareIclModule icl_name.id_name (size icl_functions) (size icl_common.com_type_defs) (size icl_common.com_cons_defs) (size icl_common.com_selector_defs)) (backEnd -*-> "BEDeclareIclModule")
	#! backEnd
		=	declareFunctionSymbols icl_functions (getConversions fe_iclDclConversions) functionIndices fe_globalFunctions (backEnd -*-> "declareFunctionSymbols")
		with
			getConversions :: (Optional {#Int}) -> {#Int}
			getConversions No
				=	{}
			getConversions (Yes conversions)
				=	conversions
	#! backEnd
		=	declare main_dcl_module_n varHeap icl_common (backEnd -*-> "declare (main_dcl_module_n)")
	#! backEnd
		=	declareArrayInstances fe_arrayInstances main_dcl_module_n icl_functions (backEnd -*-> "declareArrayInstances")
	#! backEnd
		=	adjustArrayFunctions predefs fe_arrayInstances main_dcl_module_n icl_functions fe_dcls icl_used_module_numbers varHeap (backEnd -*-> "adjustArrayFunctions")
	#! (rules, backEnd)
		=	convertRules [(index, icl_functions.[index]) \\ (_, index) <- functionIndices] main_dcl_module_n predefs.[PD_DummyForStrictAliasFun].pds_ident varHeap (backEnd -*-> "convertRules")
	#! backEnd
		=	appBackEnd (BEDefineRules rules) (backEnd -*-> "BEDefineRules")
	#! backEnd
		=	beDefineImportedObjsAndLibs
				(convertStrings [imported.io_name \\ imported <- icl_imported_objects | not imported.io_is_library])
				(convertStrings [imported.io_name \\ imported <- icl_imported_objects | imported.io_is_library])
				(backEnd -*-> "beDefineImportedObjsAndLibs")
	#! backEnd
		=	markExports fe_dcls.[main_dcl_module_n] dcl_common.com_class_defs dcl_common.com_type_defs icl_common.com_class_defs icl_common.com_type_defs fe_dclIclConversions (backEnd -*-> "markExports")
			with
				dcl_common
					=	currentDcl.dcl_common
	#! backEnd = removeExpandedTypesFromDclModules fe_dcls icl_used_module_numbers backEnd
	=	(backEnd -*-> "backend done")
	where
		componentCount
			=	length functionIndices
		functionIndices
			=	flatten [[(componentIndex, member) \\ member <- group.group_members] \\ group <-: fe_components & componentIndex <- [0..]]

declareOtherDclModules :: {#DclModule} Int ModuleNumberSet -> BackEnder
declareOtherDclModules dcls main_dcl_module_n used_module_numbers
	=	foldStateWithIndexA declareOtherDclModule dcls
where
	declareOtherDclModule :: ModuleIndex DclModule -> BackEnder
	declareOtherDclModule moduleIndex dclModule
		| moduleIndex == main_dcl_module_n || moduleIndex == cPredefinedModuleIndex || not (in_module_number_set moduleIndex used_module_numbers)
			=	identity
		// otherwise
			=	declareDclModule moduleIndex dclModule

defineOtherDclModules :: {#DclModule} Int ModuleNumberSet VarHeap -> BackEnder
defineOtherDclModules dcls main_dcl_module_n used_module_numbers varHeap
	=	foldStateWithIndexA (defineOtherDclModule varHeap) dcls
where
	defineOtherDclModule :: VarHeap ModuleIndex DclModule -> BackEnder
	defineOtherDclModule varHeap moduleIndex dclModule
		| moduleIndex == main_dcl_module_n || moduleIndex == cPredefinedModuleIndex || not (in_module_number_set moduleIndex used_module_numbers)
			=	identity
		// otherwise
			=	defineDclModule varHeap moduleIndex dclModule

declareCurrentDclModule :: IclModule DclModule Int -> BackEnder
declareCurrentDclModule {icl_common} {dcl_name, dcl_functions, dcl_is_system, dcl_common} main_dcl_module_n
	=	appBackEnd (BEDeclareDclModule main_dcl_module_n dcl_name.id_name dcl_is_system (size dcl_functions) (size icl_common.com_type_defs) (size dcl_common.com_cons_defs) (size dcl_common.com_selector_defs))
	
declareDclModule :: ModuleIndex DclModule -> BackEnder
declareDclModule moduleIndex {dcl_name, dcl_common, dcl_functions, dcl_is_system}
	=	appBackEnd (BEDeclareDclModule moduleIndex dcl_name.id_name dcl_is_system (size dcl_functions) (size dcl_common.com_type_defs) (size dcl_common.com_cons_defs) (size dcl_common.com_selector_defs))
/*
defineCurrentDclModule :: VarHeap IclModule DclModule {#Int} -> BackEnder
defineCurrentDclModule varHeap {icl_common} {dcl_name, dcl_common, dcl_functions, dcl_is_system, dcl_conversions} typeConversions
	=	declareCurrentDclModuleTypes icl_common.com_type_defs typeConversions varHeap
	o`	defineCurrentDclModuleTypes dcl_common.com_cons_defs dcl_common.com_selector_defs dcl_common.com_type_defs typeConversions varHeap
*/
defineDclModule :: VarHeap ModuleIndex DclModule -> BackEnder
defineDclModule varHeap moduleIndex {dcl_name, dcl_common, dcl_functions, dcl_is_system,dcl_instances}
	=	declare moduleIndex varHeap dcl_common
	o`	declareFunTypes moduleIndex dcl_functions dcl_instances.ir_from  varHeap

removeExpandedTypesFromDclModules :: {#DclModule} ModuleNumberSet -> BackEnder
removeExpandedTypesFromDclModules dcls used_module_numbers
	=	foldStateWithIndexA removeExpandedTypesFromDclModule dcls
where
	removeExpandedTypesFromDclModule :: ModuleIndex DclModule -> BackEnder
	removeExpandedTypesFromDclModule moduleIndex dclModule=:{dcl_functions}
		| moduleIndex == cPredefinedModuleIndex || not (in_module_number_set moduleIndex used_module_numbers)
			= identity
			= foldStateWithIndexA (removeExpandedTypesFromFunType moduleIndex)  dcl_functions
			where
				removeExpandedTypesFromFunType :: ModuleIndex Index FunType -> BackEnder
				removeExpandedTypesFromFunType moduleIndex functionIndex {ft_symb, ft_type_ptr}
					= \be0 ->	let (ft_type,be) = read_from_var_heap ft_type_ptr 0 be0 in
						(case ft_type of
							VI_ExpandedType expandedType
								->	write_to_var_heap ft_type_ptr VI_Empty	
							_
								->	identity) be

// move types from their dcl to icl positions

class swapTypes a :: Int Int *a -> *a

instance swapTypes BackEndState where
//instance swapTypes BackEnd where
	swapTypes i j be
		=	appBackEnd (BESwapTypes i j) be

instance swapTypes {{#Char}} where
	swapTypes i j a
		=	swap i j a

swap i j a
	#! iValue = a.[i]
	#! jValue = a.[j]
	=	{a & [i] = jValue, [j] = iValue}

reshuffleTypes :: Int {#Int} *a -> *a | swapTypes a
reshuffleTypes nIclTypes dclIclConversions be
	=	thd3 (foldStateWithIndexA (swapType nDclTypes) dclIclConversions (idP nDclTypes, idP nIclTypes, be))
	where
		nDclTypes
			=	size dclIclConversions

		idP :: Int -> .{#Int}
		idP n
			=	{i \\ i <- [0 .. n-1]}

		swapType :: Int Int Int (*{#Int}, *{#Int},  *a) -> (*{#Int}, *{#Int},  *a) | swapTypes a
		swapType nDclTypes dclIndex iclIndex state=:(p,p`,be)
			#! frm
				=	p.[dclIndex]
			#! to
				=	iclIndex
			| frm == to
				=	state
			// otherwise
				#! frm` = dclIndex
				#! to` = p`.[iclIndex]
				#! to` = if (to` >= nDclTypes) frm` to`
				=	(swap frm` to` p, swap frm to p`, swapTypes frm to be)

:: DeclVarsInput :== (!Ident, !VarHeap)

class declareVars a :: a !DeclVarsInput -> BackEnder

instance declareVars [a] | declareVars a where
	declareVars :: [a] !DeclVarsInput -> BackEnder | declareVars a
	declareVars list dvInput
		=	foldState (flip declareVars dvInput) list

instance declareVars (Ptr VarInfo) where
	declareVars varInfoPtr (_, varHeap)
		=	declareVariable BELhsNodeId varInfoPtr "_var???" varHeap	// +++ name

instance declareVars FreeVar where
	declareVars :: FreeVar !DeclVarsInput -> BackEnder
	declareVars freeVar (_, varHeap)
		=	declareVariable BELhsNodeId freeVar.fv_info_ptr freeVar.fv_name.id_name varHeap

instance declareVars (Bind Expression FreeVar) where
	declareVars :: (Bind Expression FreeVar) !DeclVarsInput -> BackEnder
	declareVars {bind_src=App {app_symb, app_args=[Var _:_]}, bind_dst=freeVar} (aliasDummyId, varHeap)
		| app_symb.symb_name==aliasDummyId
			= identity		// we have an alias. Don't declare the same variable twice
		= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_name.id_name varHeap
	declareVars {bind_dst=freeVar} (_, varHeap)
		= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_name.id_name varHeap

declareVariable :: Int (Ptr VarInfo) {#Char} VarHeap -> BackEnder
declareVariable lhsOrRhs varInfoPtr name varHeap
	= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber varInfoPtr varHeap be0 in
		beDeclareNodeId variable_sequence_number lhsOrRhs name be

instance declareVars (Optional a) | declareVars a where
	declareVars :: (Optional a) !DeclVarsInput -> BackEnder | declareVars a
	declareVars (Yes x) dvInput
		=	declareVars x dvInput
	declareVars No _
		=	identity

instance declareVars FunctionPattern where
	declareVars :: FunctionPattern !DeclVarsInput -> BackEnder
	declareVars (FP_Algebraic _ freeVars optionalVar) dvInput
		=	declareVars freeVars dvInput
		o`	declareVars optionalVar dvInput
	declareVars (FP_Variable freeVar) dvInput
		=	declareVars freeVar dvInput
	declareVars (FP_Basic _ optionalVar) dvInput
		=	declareVars optionalVar dvInput
	declareVars FP_Empty dvInput
		=	identity

instance declareVars Expression where
	declareVars :: Expression !DeclVarsInput -> BackEnder
	declareVars (Let {let_strict_binds, let_lazy_binds, let_expr}) dvInput
		=	declareVars let_strict_binds dvInput
		o`	declareVars let_lazy_binds dvInput
		o`	declareVars let_expr dvInput
	declareVars (Conditional {if_then, if_else}) dvInput
		=	declareVars if_then dvInput
		o`	declareVars if_else dvInput
	declareVars (AnyCodeExpr _ outParams _) (_, varHeap)
		=	foldState (declVar varHeap) outParams 
	  where
		declVar varHeap {bind_dst=freeVar} 
			= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_name.id_name varHeap
	declareVars _ _
		=	identity

instance declareVars TransformedBody where
	declareVars :: TransformedBody !DeclVarsInput -> BackEnder
	declareVars {tb_args, tb_rhs} dvInput
		=	declareVars tb_args dvInput
		o`	declareVars tb_rhs dvInput

instance declareVars BackendBody where
	declareVars :: BackendBody !DeclVarsInput -> BackEnder
	declareVars {bb_args, bb_rhs} dvInput
		=	declareVars bb_args dvInput
		o`	declareVars bb_rhs dvInput

:: ModuleIndex :== Index

class declare a :: ModuleIndex !VarHeap a  -> BackEnder

class declareWithIndex a :: Index ModuleIndex !VarHeap a -> BackEnder

//1.3
instance declare {#a} | declareWithIndex a & ArrayElem a where
	declare :: ModuleIndex  VarHeap {#a} -> BackEnder | declareWithIndex a & ArrayElem a 
//3.1
/*2.0
instance declare {#a} | declareWithIndex a & Array {#} a where
	declare :: ModuleIndex  VarHeap {#a} -> BackEnder | declareWithIndex a & Array {#} a 
0.2*/
	declare moduleIndex varHeap array
		=	foldStateWithIndexA (\i -> declareWithIndex i moduleIndex varHeap) array

declareFunctionSymbols :: {#FunDef} {#Int} [(Int, Int)] IndexRange *BackEndState -> *BackEndState
declareFunctionSymbols functions iclDclConversions functionIndices globalFunctions backEnd
	=	foldr (declare iclDclConversions) backEnd [(functionIndex, componentIndex, functions.[functionIndex]) \\ (componentIndex, functionIndex) <- functionIndices]
	where
		declare iclDclConversions (functionIndex, componentIndex, function) backEnd
			=	appBackEnd (BEDeclareFunction (functionName function.fun_symb.id_name functionIndex iclDclConversions globalFunctions) 
					function.fun_arity functionIndex componentIndex) backEnd
			where
				functionName :: {#Char} Int {#Int} IndexRange -> {#Char}
				functionName name functionIndex iclDclConversions {ir_from, ir_to}
					| functionIndex >= ir_to || functionIndex < ir_from
						=	(name +++ ";" +++ toString iclDclConversions.[functionIndex])
					// otherwise
						=	name

// move to backendsupport
foldStateWithIndexRangeA function frm to array
	:== foldStateWithIndexRangeA frm
	where
		foldStateWithIndexRangeA index
			| index == to
				=	identity
			// otherwise
				=	function index array.[index]
				o`	foldStateWithIndexRangeA (index+1)

declareArrayInstances :: IndexRange Int {#FunDef} -> BackEnder
declareArrayInstances {ir_from, ir_to} main_dcl_module_n functions
	=	foldStateWithIndexRangeA declareArrayInstance ir_from ir_to functions
	where
		declareArrayInstance :: Index FunDef -> BackEnder
		declareArrayInstance index {fun_symb={id_name}, fun_type=Yes type}
			=	beDeclareRuleType index main_dcl_module_n (id_name +++ ";" +++ toString index)
			o`	beDefineRuleType index main_dcl_module_n (convertTypeAlt index main_dcl_module_n type)

instance declare CommonDefs where
	declare :: ModuleIndex VarHeap CommonDefs -> BackEnder
	declare moduleIndex varHeap {com_cons_defs, com_type_defs, com_selector_defs, com_class_defs}
		=	declare moduleIndex varHeap com_type_defs
		o`	defineTypes moduleIndex com_cons_defs com_selector_defs com_type_defs varHeap

instance declareWithIndex (TypeDef a) where
	declareWithIndex :: Index ModuleIndex VarHeap (TypeDef a) -> BackEnder
	declareWithIndex typeIndex moduleIndex _ {td_name}
		=	appBackEnd (BEDeclareType typeIndex moduleIndex td_name.id_name)

declareFunTypes :: ModuleIndex {#FunType} Int VarHeap -> BackEnder
declareFunTypes moduleIndex funTypes nrOfDclFunctions varHeap
		=	foldStateWithIndexA (declareFunType moduleIndex varHeap nrOfDclFunctions) funTypes

declareFunType :: ModuleIndex VarHeap Index Int FunType -> BackEnder
declareFunType moduleIndex varHeap nrOfDclFunctions functionIndex {ft_symb, ft_type_ptr}
	= \be0 -> let (vi,be) = read_from_var_heap ft_type_ptr varHeap be0 in
					(case vi of
						VI_ExpandedType expandedType
							->	beDeclareRuleType functionIndex moduleIndex (functionName ft_symb.id_name functionIndex nrOfDclFunctions)
							o`	beDefineRuleType functionIndex moduleIndex (convertTypeAlt functionIndex moduleIndex expandedType)
						_
							->	identity) be
		where
			functionName :: {#Char} Int Int -> {#Char}
			functionName name functionIndex nrOfDclFunctions 
				| functionIndex < nrOfDclFunctions
					=	name
				// otherwise
					=	name +++ ";" +++ toString functionIndex

currentModuleTypeConversions :: {#ClassDef} {#ClassDef} (Optional ConversionTable) -> {#Int}
currentModuleTypeConversions iclClasses dclClasses (Yes conversionTable)
	// sanity check ...
	| sort [dclClass.class_dictionary.ds_index \\ dclClass <-: dclClasses]
				<> [size typeConversions .. size typeConversions + size dclClasses - 1]
		=	abort "backendconvert, currentModuleTypeConversions wrong index range for dcl dictionary types"
	// ... sanity check
	| nDclClasses == 0
		=	typeConversions
	// otherwise
		=	{createArray (nDclTypes + nDclClasses) NoIndex
				& [i] = typeConversion
					\\ typeConversion <-: typeConversions & i <- [0..]}
			:-  foldStateWithIndexA (updateDictionaryTypeIndex classConversions) classConversions
	where
		typeConversions
			=	conversionTable.[cTypeDefs]
		nDclTypes
			=	size typeConversions
		classConversions
			=	conversionTable.[cClassDefs]
		nDclClasses
			=	size classConversions

		updateDictionaryTypeIndex :: {#Int} Int Int *{#Int} -> *{#Int}
		updateDictionaryTypeIndex classConversions dclClassIndex iclClassIndex allTypeConversions
			// sanity check ...
			# (oldIndex, allTypeConversions)
				=	uselect allTypeConversions dclTypeIndex
			| oldIndex <> NoIndex
				=	abort "backendconvert, updateDictionaryTypeIndex wrong index overwritten"
			// ... sanity chechk
			=	{allTypeConversions & [dclTypeIndex] = iclTypeIndex}
			where
				dclTypeIndex
					=	dclClasses.[dclClassIndex].class_dictionary.ds_index
				iclClassIndex
					=	classConversions.[dclClassIndex]
				iclTypeIndex
					=	iclClasses.[iclClassIndex].class_dictionary.ds_index
currentModuleTypeConversions _ _ No
	=	{}

/*
declareCurrentDclModuleTypes :: {#CheckedTypeDef} {#Int} VarHeap -> BackEnder
*/
defineTypes :: ModuleIndex {#ConsDef} {#SelectorDef} {#CheckedTypeDef} VarHeap -> BackEnder
defineTypes moduleIndex constructors selectors types varHeap
	=	foldStateWithIndexA (defineType moduleIndex constructors selectors varHeap) types

convertTypeLhs :: ModuleIndex Index  [ATypeVar] -> BEMonad BEFlatTypeP
convertTypeLhs moduleIndex typeIndex args
	=	beFlatType (beTypeSymbol typeIndex moduleIndex) (convertTypeVars args)

convertTypeVars :: [ATypeVar] -> BEMonad BETypeVarListP
convertTypeVars typeVars
	=	sfoldr (beTypeVars o convertTypeVar) beNoTypeVars typeVars

convertTypeVar :: ATypeVar -> BEMonad BETypeVarP
convertTypeVar typeVar
	=	beTypeVar typeVar.atv_variable.tv_name.id_name

defineType :: ModuleIndex {#ConsDef} {#SelectorDef} VarHeap Index CheckedTypeDef *BackEndState -> *BackEndState
defineType moduleIndex constructors _ varHeap typeIndex {td_name, td_args, td_rhs=AlgType constructorSymbols} be
	# (flatType, be)
		=	convertTypeLhs moduleIndex typeIndex td_args be
	# (constructors, be)
		=	convertConstructors typeIndex td_name.id_name moduleIndex constructors constructorSymbols varHeap be
	=	appBackEnd (BEAlgebraicType flatType constructors) be
defineType moduleIndex constructors selectors varHeap typeIndex {td_args, td_rhs=RecordType {rt_constructor, rt_fields}} be
	# (flatType, be)
		=	convertTypeLhs moduleIndex typeIndex td_args be
	# (fields, be)
		=	convertSelectors moduleIndex selectors rt_fields varHeap be
	# (constructorType,be) = constructorTypeFunction be
	# (constructorTypeNode, be)
		=	beNormalTypeNode
				(beConstructorSymbol moduleIndex constructorIndex)
				(convertSymbolTypeArgs constructorType)
				be
	=	appBackEnd (BERecordType moduleIndex flatType constructorTypeNode fields) be
	where
		constructorIndex
			=	rt_constructor.ds_index
		constructorDef
			=	constructors.[constructorIndex]
		constructorTypeFunction be0
			= let (cons_type,be) = read_from_var_heap constructorDef.cons_type_ptr varHeap be0 in
					(case cons_type of
						VI_ExpandedType expandedType
							->	(expandedType,be)
						_
							->	(constructorDef.cons_type,be))
defineType moduleIndex _ _ _ typeIndex {td_args, td_rhs=AbstractType _} be
 	=	beAbsType (convertTypeLhs moduleIndex typeIndex td_args) be
defineType _ _ _ _ _ _ be
	=	be

convertConstructors :: Int {#Char} ModuleIndex {#ConsDef} [DefinedSymbol] VarHeap -> BEMonad BEConstructorListP
convertConstructors typeIndex typeName moduleIndex constructors symbols varHeap
	=	sfoldr (beConstructors o convertConstructor typeIndex typeName moduleIndex constructors varHeap) beNoConstructors symbols

convertConstructor :: Int {#Char} ModuleIndex {#ConsDef} VarHeap DefinedSymbol -> BEMonad BEConstructorListP
convertConstructor typeIndex typeName moduleIndex constructorDefs varHeap {ds_index}
	= \be0 -> let (constructorType,be) = constructorTypeFunction be0 in
		(appBackEnd (BEDeclareConstructor ds_index moduleIndex constructorDef.cons_symb.id_name) // +++ remove declare
		o`	beConstructor
			(beNormalTypeNode
				(beConstructorSymbol moduleIndex ds_index)
				(convertSymbolTypeArgs constructorType))) be
	where
		constructorDef
			=	constructorDefs.[ds_index]
		constructorTypeFunction be0
			= let (cons_type,be) = read_from_var_heap constructorDef.cons_type_ptr varHeap be0 in
					(case cons_type of
						VI_ExpandedType expandedType
							->	(expandedType,be) // ->> (typeName, typeIndex, constructorDef.cons_symb.id_name, ds_index, expandedType)
						_
							->	(constructorDef.cons_type,be)) // ->> (typeName, typeIndex, constructorDef.cons_symb.id_name, ds_index, constructorDef.cons_type)

convertSelectors :: ModuleIndex {#SelectorDef} {#FieldSymbol} VarHeap -> BEMonad BEFieldListP
convertSelectors moduleIndex selectors symbols varHeap
	=	foldrA (beFields o convertSelector moduleIndex selectors varHeap) beNoFields symbols

convertSelector :: ModuleIndex {#SelectorDef} VarHeap FieldSymbol -> BEMonad BEFieldListP
convertSelector moduleIndex selectorDefs varHeap {fs_index}
	= \be0 -> let (selectorType,be) = selectorTypeFunction be0 in
		(	appBackEnd (BEDeclareField fs_index moduleIndex selectorDef.sd_symb.id_name)
		o`	beField fs_index moduleIndex (convertAnnotTypeNode (selectorType.st_result))) be
	where
		selectorDef
			=	selectorDefs.[fs_index]
		selectorTypeFunction be0
			= let (sd_type,be) = read_from_var_heap selectorDef.sd_type_ptr varHeap be0 in
				(case sd_type of
					VI_ExpandedType expandedType
						->	(expandedType,be)
					_
						->	(selectorDef.sd_type,be))

predefineSymbols :: DclModule PredefinedSymbols -> BackEnder
predefineSymbols {dcl_common} predefs
	=	appBackEnd (BEDeclarePredefinedModule (size dcl_common.com_type_defs) (size dcl_common.com_cons_defs))
	o`	foldState predefineType types
	o`	foldState predefineConstructor constructors
	where
		predefineType (index, arity, symbolKind)
			// sanity check ...
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a type"
			// ... sanity check
			=	appBackEnd (BEPredefineTypeSymbol arity predefs.[index].pds_def cPredefinedModuleIndex symbolKind)

		predefineConstructor (index, arity, symbolKind)
			// sanity check ...
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a constructor"
			// ... sanity check
			=	appBackEnd (BEPredefineConstructorSymbol arity predefs.[index].pds_def cPredefinedModuleIndex symbolKind)

		types :: [(Int, Int, BESymbKind)]
		types
			=	[	(PD_ListType, 1, BEListType)
				,	(PD_LazyArrayType, 1, BEArrayType)
				,	(PD_StrictArrayType, 1, BEStrictArrayType)
				,	(PD_UnboxedArrayType, 1, BEUnboxedArrayType)
				:	[(index, index-PD_Arity2TupleType+2, BETupleType) \\ index <- [PD_Arity2TupleType..PD_Arity32TupleType]]
				]

		constructors :: [(Int, Int, BESymbKind)]
		constructors
			=	[	(PD_NilSymbol, 0, BENilSymb)
				,	(PD_ConsSymbol, 2, BEConsSymb)
				:	[(index, index-PD_Arity2TupleSymbol+2, BETupleSymb) \\ index <- [PD_Arity2TupleSymbol..PD_Arity32TupleSymbol]]
				]

:: AdjustStdArrayInfo =
	{	asai_moduleIndex	:: !Int
	,	asai_mapping 		:: !{#BEArrayFunKind}
	,	asai_funs			:: !{#FunType}
	,	asai_varHeap	 	:: !VarHeap
	}

adjustArrayFunctions :: PredefinedSymbols IndexRange Int {#FunDef} {#DclModule} ModuleNumberSet VarHeap -> BackEnder
adjustArrayFunctions predefs arrayInstancesRange main_dcl_module_n functions dcls used_module_numbers varHeap
	=	adjustStdArray arrayInfo predefs stdArray.dcl_common.com_instance_defs
	o`	adjustIclArrayInstances arrayInstancesRange arrayMemberMapping functions
	where
		arrayModuleIndex
			=	predefs.[PD_StdArray].pds_def
		arrayClassIndex
			=	predefs.[PD_ArrayClass].pds_def
		arrayClass
			=	stdArray.dcl_common.com_class_defs.[arrayClassIndex]
		stdArray
			=	dcls.[arrayModuleIndex]
		arrayMemberMapping
			=	getArrayMemberMapping predefs arrayClass.class_members
		arrayInfo
			=	{	asai_moduleIndex	= arrayModuleIndex
				,	asai_mapping 		= arrayMemberMapping
				,	asai_funs			= stdArray.dcl_functions
				,	asai_varHeap		= varHeap
				}

		getArrayMemberMapping :: PredefinedSymbols {#DefinedSymbol} -> {#BEArrayFunKind}
		getArrayMemberMapping predefs members
			// sanity check ...
			| size members <> length (memberIndexMapping predefs)
				=	abort "backendconvert, arrayMemberMapping: incorrect number of members"
			// ... sanity check
			=	{	createArray (size members) BENoArrayFun
				&	[i] = backEndFunKind member.ds_index (memberIndexMapping predefs) \\ member <-: members & i <- [0..]
				}				
			where
				memberIndexMapping :: PredefinedSymbols -> [(!Index, !BEArrayFunKind)]
				memberIndexMapping predefs
					=	[(predefs.[predefIndex].pds_def, backEndArrayFunKind) \\ (predefIndex, backEndArrayFunKind) <- predefMapping]
					where
						predefMapping 
							=	[	(PD_CreateArrayFun,		BECreateArrayFun)
								,	(PD_ArraySelectFun,		BEArraySelectFun)
								,	(PD_UnqArraySelectFun,	BEUnqArraySelectFun)
								,	(PD_ArrayUpdateFun,		BEArrayUpdateFun)
								,	(PD_ArrayReplaceFun,	BEArrayReplaceFun)
								,	(PD_ArraySizeFun,		BEArraySizeFun)
								,	(PD_UnqArraySizeFun,	BEUnqArraySizeFun)
								,	(PD__CreateArrayFun,	BE_CreateArrayFun)
								]

				backEndFunKind :: Index [(!Index, !BEArrayFunKind)] -> BEArrayFunKind
				backEndFunKind memberIndex predefMapping
					=	hd [back \\ (predefMemberIndex, back) <- predefMapping | predefMemberIndex == memberIndex]

		adjustStdArray :: AdjustStdArrayInfo PredefinedSymbols {#ClassInstance} -> BackEnder
		adjustStdArray arrayInfo predefs instances
			| arrayModuleIndex == NoIndex || not (in_module_number_set arrayModuleIndex used_module_numbers)
				=	identity
			// otherwise
				=	foldStateA (adjustStdArrayInstance arrayClassIndex arrayInfo) instances
			where
				adjustStdArrayInstance :: Index AdjustStdArrayInfo ClassInstance -> BackEnder
				adjustStdArrayInstance arrayClassIndex arrayInfo=:{asai_moduleIndex} instance`=:{ins_class}
					| ins_class.glob_object.ds_index == arrayClassIndex && ins_class.glob_module == asai_moduleIndex
						=	adjustArrayClassInstance arrayInfo instance`
					// otherwise
						=	identity
					where
						adjustArrayClassInstance :: AdjustStdArrayInfo ClassInstance -> BackEnder
						adjustArrayClassInstance arrayInfo {ins_members}
							=	foldStateWithIndexA (adjustMember arrayInfo) ins_members
						where
							adjustMember :: AdjustStdArrayInfo Int DefinedSymbol -> BackEnder
							adjustMember {asai_moduleIndex, asai_mapping, asai_funs, asai_varHeap} offset {ds_index}
								= \be0 ->	let (ft_type,be) = read_from_var_heap asai_funs.[ds_index].ft_type_ptr varHeap be0 in
									(case ft_type of
										VI_ExpandedType _
											->	beAdjustArrayFunction asai_mapping.[offset] ds_index asai_moduleIndex
										_
											->	identity) be

		adjustIclArrayInstances :: IndexRange {#BEArrayFunKind} {#FunDef} -> BackEnder
		adjustIclArrayInstances  {ir_from, ir_to} mapping instances
			=	foldStateWithIndexRangeA (adjustIclArrayInstance mapping) ir_from ir_to instances
			where
				adjustIclArrayInstance :: {#BEArrayFunKind} Index FunDef -> BackEnder
				// for array functions fun_index is not the index in the FunDef array,
				// but its member index in the Array class
				adjustIclArrayInstance mapping index {fun_index}
					=	beAdjustArrayFunction mapping.[fun_index] index main_dcl_module_n

/*
convertRules :: [(Int, FunDef)] VarHeap -> BEMonad BEImpRuleP
convertRules rules varHeap
//	=	foldr (beRules o flip convertRule varHeap) beNoRules rules
	=	foldl (flip beRules) beNoRules (map (flip convertRule varHeap) rules)
*/

convertRules :: [(Int, FunDef)] Int Ident VarHeap *BackEndState -> (BEImpRuleP, *BackEndState)
convertRules rules main_dcl_module_n aliasDummyId varHeap be
	# (null, be)
		=	accBackEnd BENoRules be
	=	convert rules varHeap null be
//	=	foldr (beRules o flip convertRule main_dcl_module_n varHeap) beNoRules rules
	where
		convert :: [(Int, FunDef)] VarHeap BEImpRuleP *BackEndState -> (BEImpRuleP, *BackEndState)
		convert [] _ rulesP be
			=	(rulesP, be)
		convert [h:t] varHeap rulesP be
			# (ruleP, be)
				=	convertRule aliasDummyId h main_dcl_module_n varHeap be
			# (rulesP, be)
				=	accBackEnd (BERules ruleP rulesP) be
			=	convert t varHeap rulesP be

convertRule :: Ident (Int,FunDef) Int VarHeap -> BEMonad BEImpRuleP
convertRule aliasDummyId (index, {fun_type=Yes type, fun_body=body, fun_pos, fun_kind, fun_symb}) main_dcl_module_n varHeap
	=	beRule index (cafness fun_kind)
			(convertTypeAlt index main_dcl_module_n (type /* ->> ("convertRule", fun_symb.id_name, index, type) */))
			(convertFunctionBody index (positionToLineNumber fun_pos) aliasDummyId body main_dcl_module_n varHeap)
	where
		cafness :: FunKind -> Int
		cafness (FK_Function _)
			=	BEIsNotACaf
		cafness FK_Macro
			=	BEIsNotACaf
		cafness FK_Caf
			=	BEIsACaf
		cafness funKind
			=	BEIsNotACaf <<- ("backendconvert, cafness: unknown fun kind", funKind)

		positionToLineNumber :: Position -> Int
		positionToLineNumber (FunPos  _ lineNumber _)
			=	lineNumber
		positionToLineNumber (LinePos _ lineNumber)
			=	lineNumber
		positionToLineNumber _
			=	-1

convertTypeAlt :: Int ModuleIndex SymbolType -> BEMonad BETypeAltP
convertTypeAlt functionIndex moduleIndex symbol=:{st_result}
	=	beTypeAlt (beNormalTypeNode (beFunctionSymbol functionIndex moduleIndex) (convertSymbolTypeArgs symbol)) (convertAnnotTypeNode st_result)

convertSymbolTypeArgs :: SymbolType -> BEMonad BETypeArgP
convertSymbolTypeArgs {st_args}
	=	convertTypeArgs st_args

convertBasicTypeKind :: BasicType -> BESymbKind
convertBasicTypeKind BT_Int
	=	BEIntType
convertBasicTypeKind BT_Char
	=	BECharType
convertBasicTypeKind BT_Real
	=	BERealType
convertBasicTypeKind BT_Bool
	=	BEBoolType
convertBasicTypeKind BT_File
	=	BEFileType
convertBasicTypeKind BT_World
	=	BEWorldType
convertBasicTypeKind BT_Dynamic
	=	BEDynamicType
convertBasicTypeKind (BT_String _)
	=	undef <<- "convertBasicTypeKind (BT_String _) shouldn't occur"

convertAnnotation :: Annotation -> BEAnnotation
convertAnnotation AN_None
	=	BENoAnnot
convertAnnotation AN_Strict
	=	BEStrictAnnot

convertAttribution :: TypeAttribute -> BEAttribution
convertAttribution TA_Unique
	=	BEUniqueAttr
convertAttribution _ // +++ uni vars, etc.
	=	BENoUniAttr

convertAnnotTypeNode :: AType -> BEMonad BETypeNodeP
convertAnnotTypeNode {at_type, at_annotation, at_attribute}
/*
	=	convertTypeNode at_type
	:-	beAnnotateTypeNode (convertAnnotation at_annotation)
	:-	beAttributeTypeNode (convertAttribution at_attribute)
*/
	=
//	\s -> (
	convertTypeNode at_type
	:-	beAnnotateTypeNode c_annot
	:-	beAttributeTypeNode c_attrib
//	) s
	where
		c_annot = convertAnnotation at_annotation
		c_attrib = convertAttribution at_attribute

convertTypeNode :: Type -> BEMonad BETypeNodeP
convertTypeNode (TB (BT_String type))
	=	convertTypeNode type
convertTypeNode (TB basicType)
	=	beNormalTypeNode (beBasicSymbol (convertBasicTypeKind basicType)) beNoTypeArgs	
convertTypeNode (TA typeSymbolIdent typeArgs)
	=	beNormalTypeNode (convertTypeSymbolIdent typeSymbolIdent) (convertTypeArgs typeArgs)
convertTypeNode (TV {tv_name})
	=	beVarTypeNode tv_name.id_name
convertTypeNode (TempQV n)
	=	beVarTypeNode ("_tqv" +++ toString n)
convertTypeNode (TempV n)
	=	beVarTypeNode ("_tv" +++ toString n)
convertTypeNode (a --> b)
	=	beNormalTypeNode (beBasicSymbol BEFunType) (convertTypeArgs [a, b])
convertTypeNode (a :@: b)
	=	beNormalTypeNode (beBasicSymbol BEApplySymb) (convertTypeArgs [{at_attribute=TA_Multi, at_annotation=AN_None, at_type = consVariableToType a} : b])
convertTypeNode TE
	=	beNormalTypeNode beDontCareDefinitionSymbol beNoTypeArgs
convertTypeNode typeNode
	=	undef <<- ("backendconvert, convertTypeNode: unknown type node", typeNode)

consVariableToType :: ConsVariable -> Type
consVariableToType (CV typeVar)
	=	TV typeVar
consVariableToType (TempCV varId)
	=	TempV varId
consVariableToType (TempQCV varId)
	=	TempQV varId

convertTypeArgs :: [AType] -> BEMonad BETypeArgP
convertTypeArgs args
	=	sfoldr (beTypeArgs o convertAnnotTypeNode) beNoTypeArgs args

convertFunctionBody :: Int Int Ident FunctionBody Int VarHeap -> BEMonad BERuleAltP
convertFunctionBody functionIndex lineNumber aliasDummyId (BackendBody bodies) main_dcl_module_n varHeap
	=	convertBackendBodies functionIndex lineNumber bodies varHeap
where
	convertBackendBodies :: Int Int [BackendBody] VarHeap -> BEMonad BERuleAltP
	convertBackendBodies functionIndex lineNumber bodies varHeap
		=	sfoldr (beRuleAlts o (flip (convertBackendBody functionIndex lineNumber)) varHeap) beNoRuleAlts bodies
	where
		convertBackendBody :: Int Int BackendBody VarHeap -> BEMonad BERuleAltP
		convertBackendBody functionIndex lineNumber body=:{bb_args, bb_rhs=ABCCodeExpr instructions inline} varHeap
			=	beNoNodeDefs ==> \noNodeDefs
			->	declareVars body (aliasDummyId, varHeap)
			o`	beCodeAlt
					lineNumber
					(convertLhsNodeDefs bb_args noNodeDefs varHeap)
					(convertBackendLhs functionIndex bb_args varHeap)
					(beAbcCodeBlock inline (convertStrings instructions))
		convertBackendBody functionIndex lineNumber body=:{bb_args, bb_rhs=AnyCodeExpr inParams outParams instructions} varHeap
			=	beNoNodeDefs ==> \noNodeDefs
			->	declareVars body (aliasDummyId, varHeap)
			o`	beCodeAlt
					lineNumber
					(convertLhsNodeDefs bb_args noNodeDefs varHeap)
					(convertBackendLhs functionIndex bb_args varHeap)
					(beAnyCodeBlock (convertCodeParameters inParams varHeap) (convertCodeParameters outParams varHeap) (convertStrings instructions))
		convertBackendBody functionIndex lineNumber body=:{bb_args, bb_rhs} varHeap
			=	beNoNodeDefs ==> \noNodeDefs
			->	declareVars body (aliasDummyId, varHeap)
			o`	beRuleAlt
					lineNumber
					(convertLhsNodeDefs bb_args noNodeDefs varHeap)
					(convertBackendLhs functionIndex bb_args varHeap)
					(convertRhsNodeDefs aliasDummyId bb_rhs main_dcl_module_n varHeap)
					(convertRhsStrictNodeIds bb_rhs varHeap)
					(convertRootExpr aliasDummyId bb_rhs main_dcl_module_n varHeap)

		convertBackendLhs :: Int [FunctionPattern] VarHeap -> BEMonad BENodeP
		convertBackendLhs functionIndex patterns varHeap
			=	beNormalNode (beFunctionSymbol functionIndex main_dcl_module_n) (convertPatterns patterns varHeap)

convertStrings :: [{#Char}] -> BEMonad BEStringListP
convertStrings strings
	=	sfoldr (beStrings o beString) beNoStrings strings

convertCodeParameters :: (CodeBinding a) VarHeap -> BEMonad BECodeParameterP | varInfoPtr a
convertCodeParameters codeParameters varHeap
	=	sfoldr (beCodeParameters o flip convertCodeParameter varHeap) beNoCodeParameters codeParameters

class varInfoPtr a :: a -> VarInfoPtr

instance varInfoPtr BoundVar where
	varInfoPtr boundVar
		=	boundVar.var_info_ptr

instance varInfoPtr FreeVar where
	varInfoPtr freeVar
		=	freeVar.fv_info_ptr

convertCodeParameter :: (Bind String a) VarHeap -> BEMonad BECodeParameterP | varInfoPtr a
convertCodeParameter {bind_src, bind_dst} varHeap
		=	beCodeParameter bind_src (convertVar (varInfoPtr bind_dst) varHeap)
/*
convertTransformedLhs :: Int [FreeVar] VarHeap -> BEMonad BENodeP
convertTransformedLhs functionIndex freeVars varHeap
	=	beNormalNode (beFunctionSymbol functionIndex cIclModIndex) (convertLhsArgs freeVars varHeap)
*/

convertPatterns :: [FunctionPattern] VarHeap -> BEMonad BEArgP
convertPatterns patterns varHeap
	=	sfoldr (beArgs o flip convertPattern varHeap) beNoArgs patterns

convertPattern :: FunctionPattern VarHeap -> BEMonad BENodeP
convertPattern (FP_Variable freeVar) varHeap
	=	convertFreeVarPattern freeVar varHeap
convertPattern (FP_Basic _ (Yes freeVar)) varHeap
	=	convertFreeVarPattern freeVar varHeap
convertPattern (FP_Basic value No) _
	=	beNormalNode (convertLiteralSymbol value) beNoArgs
convertPattern (FP_Algebraic _ freeVars (Yes freeVar)) varHeap
	=	convertFreeVarPattern freeVar varHeap
convertPattern (FP_Algebraic {glob_module, glob_object={ds_index}} subpatterns No) varHeap
	=	beNormalNode (beConstructorSymbol glob_module ds_index) (convertPatterns subpatterns varHeap)
convertPattern (FP_Dynamic _ _ _ (Yes freeVar)) varHeap
	=	convertFreeVarPattern freeVar varHeap
convertPattern FP_Empty varHeap
	=	beNodeIdNode beWildCardNodeId beNoArgs

convertFreeVarPattern :: FreeVar  VarHeap -> BEMonad BENodeP
convertFreeVarPattern freeVar varHeap
	=	beNodeIdNode (convertVar freeVar.fv_info_ptr varHeap) beNoArgs

convertLhsArgs :: [FreeVar] VarHeap -> BEMonad BEArgP
convertLhsArgs freeVars varHeap
	=	sfoldr (beArgs o (flip convertFreeVarPattern) varHeap) beNoArgs freeVars

convertVarPtr :: VarInfoPtr  VarHeap -> BEMonad BENodeP
convertVarPtr var varHeap
	=	beNodeIdNode (convertVar var varHeap) beNoArgs

convertVars :: [VarInfoPtr] VarHeap -> BEMonad BEArgP
convertVars vars varHeap
	=	sfoldr (beArgs o flip convertVarPtr varHeap) beNoArgs vars

convertRootExpr :: Ident Expression Int VarHeap -> BEMonad BENodeP
convertRootExpr aliasDummyId (Let {let_expr}) main_dcl_module_n varHeap
	=	convertRootExpr aliasDummyId let_expr main_dcl_module_n varHeap
convertRootExpr aliasDummyId (Conditional {if_cond=cond, if_then=then, if_else=Yes else}) main_dcl_module_n varHeap
	=	beGuardNode
			(convertExpr cond main_dcl_module_n varHeap)
			(convertRhsNodeDefs aliasDummyId then main_dcl_module_n varHeap)
			(convertRhsStrictNodeIds then varHeap)
			(convertRootExpr aliasDummyId then main_dcl_module_n varHeap)
			(convertRhsNodeDefs aliasDummyId else main_dcl_module_n  varHeap)
			(convertRhsStrictNodeIds else varHeap)
			(convertRootExpr aliasDummyId else main_dcl_module_n varHeap)
convertRootExpr aliasDummyId (Conditional {if_cond=cond, if_then=then, if_else=No}) main_dcl_module_n varHeap
		=	beGuardNode
				(convertExpr cond main_dcl_module_n varHeap)
				(convertRhsNodeDefs aliasDummyId then main_dcl_module_n varHeap)
				(convertRhsStrictNodeIds then varHeap)
				(convertRootExpr aliasDummyId then main_dcl_module_n varHeap)
				beNoNodeDefs
				beNoStrictNodeIds
				(beNormalNode (beBasicSymbol BEFailSymb) beNoArgs)
convertRootExpr _ expr main_dcl_module_n varHeap
	=	convertExpr expr main_dcl_module_n varHeap

// RWS +++ rewrite
convertLhsNodeDefs :: [FunctionPattern] BENodeDefP VarHeap -> BEMonad BENodeDefP
convertLhsNodeDefs [FP_Basic value (Yes freeVar) : patterns] nodeDefs varHeap
	=	convertLhsNodeDefs patterns nodeDefs varHeap ==> \nodeDefs
	->	defineLhsNodeDef freeVar (FP_Basic value No) nodeDefs varHeap
convertLhsNodeDefs [FP_Algebraic symbol subpatterns (Yes freeVar) : patterns] nodeDefs varHeap
	=	convertLhsNodeDefs subpatterns nodeDefs varHeap ==> \nodeDefs
	->	convertLhsNodeDefs patterns nodeDefs varHeap ==> \nodeDefs
	->	defineLhsNodeDef freeVar (FP_Algebraic symbol subpatterns No) nodeDefs varHeap
convertLhsNodeDefs [FP_Algebraic symbol subpatterns No : patterns] nodeDefs varHeap
	=	convertLhsNodeDefs subpatterns nodeDefs varHeap ==> \nodeDefs
	->	convertLhsNodeDefs patterns nodeDefs varHeap
convertLhsNodeDefs [FP_Dynamic varPtrs var typeCode (Yes freeVar) : patterns] nodeDefs varHeap
	=	convertLhsNodeDefs patterns nodeDefs varHeap ==> \nodeDefs
	->	defineLhsNodeDef freeVar (FP_Dynamic varPtrs var typeCode No) nodeDefs varHeap
convertLhsNodeDefs [_ : patterns] nodeDefs varHeap
	=	convertLhsNodeDefs patterns nodeDefs varHeap
convertLhsNodeDefs [] nodeDefs varHeap
	=	return nodeDefs

defineLhsNodeDef :: FreeVar FunctionPattern BENodeDefP VarHeap -> BEMonad BENodeDefP
defineLhsNodeDef freeVar pattern nodeDefs varHeap
	= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber freeVar.fv_info_ptr varHeap be0 in
		beNodeDefs
			(beNodeDef variable_sequence_number (convertPattern pattern varHeap))
			(return nodeDefs) be

collectNodeDefs :: Ident Expression -> [Bind Expression FreeVar]
collectNodeDefs aliasDummyId (Let {let_strict_binds, let_lazy_binds})
	= filterStrictAlias let_strict_binds let_lazy_binds
  where
	filterStrictAlias [] let_lazy_binds
		= let_lazy_binds
	filterStrictAlias [strict_bind=:{bind_src=App app}:strict_binds] let_lazy_binds
		| app.app_symb.symb_name==aliasDummyId
			// the compiled source was a strict alias like "#! x = y"
			= case hd app.app_args of
				Var _
					// the node is still such an alias and must be ignored
					-> filterStrictAlias strict_binds let_lazy_binds
				hd_app_args
					// the node is not an alias anymore: remove just the _dummyForStrictAlias call
					-> [{ strict_bind & bind_src = hd_app_args } : filterStrictAlias strict_binds let_lazy_binds]
	filterStrictAlias [strict_bind:strict_binds] let_lazy_binds
		= [strict_bind: filterStrictAlias strict_binds let_lazy_binds]
collectNodeDefs _ _
	=	[]

convertRhsNodeDefs :: Ident Expression Int VarHeap -> BEMonad BENodeDefP
convertRhsNodeDefs aliasDummyId expr main_dcl_module_n varHeap
	=	convertNodeDefs (collectNodeDefs aliasDummyId expr) varHeap
where
	convertNodeDefs :: [Bind Expression FreeVar] VarHeap -> BEMonad BENodeDefP
	convertNodeDefs binds varHeap
		=	sfoldr (beNodeDefs o flip convertNodeDef varHeap) beNoNodeDefs binds
		where
			convertNodeDef :: !(Bind Expression FreeVar) VarHeap -> BEMonad BENodeDefP
			convertNodeDef {bind_src=expr, bind_dst=freeVar} varHeap
				= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber freeVar.fv_info_ptr varHeap be0 in
					beNodeDef variable_sequence_number (convertExpr expr main_dcl_module_n varHeap) be

collectStrictNodeIds :: Expression -> [FreeVar]
collectStrictNodeIds (Let {let_strict_binds, let_expr})
	=	[bind_dst \\ {bind_dst} <- let_strict_binds]
collectStrictNodeIds _
	=	[]

convertStrictNodeId :: FreeVar VarHeap -> BEMonad BEStrictNodeIdP
convertStrictNodeId freeVar varHeap
	=	beStrictNodeId (convertVar freeVar.fv_info_ptr varHeap)

convertStrictNodeIds :: [FreeVar] VarHeap -> BEMonad BEStrictNodeIdP
convertStrictNodeIds freeVars varHeap
	=	sfoldr (beStrictNodeIds o flip convertStrictNodeId varHeap) beNoStrictNodeIds freeVars

convertRhsStrictNodeIds :: Expression VarHeap -> BEMonad BEStrictNodeIdP
convertRhsStrictNodeIds expression varHeap
	=	convertStrictNodeIds (collectStrictNodeIds expression) varHeap

convertLiteralSymbol :: BasicValue -> BEMonad BESymbolP
convertLiteralSymbol (BVI string)
	=	beLiteralSymbol BEIntDenot string
convertLiteralSymbol (BVB bool)
	=	beBoolSymbol bool
convertLiteralSymbol (BVC string)
	=	beLiteralSymbol BECharDenot string
convertLiteralSymbol (BVR string)
	=	beLiteralSymbol BERealDenot string
convertLiteralSymbol (BVS string)
	=	beLiteralSymbol BEStringDenot string 

convertTypeSymbolIdent :: TypeSymbIdent -> BEMonad BESymbolP
convertTypeSymbolIdent {type_index={glob_module, glob_object}}
	=	beTypeSymbol glob_object glob_module // ->> ("convertTypeSymbolIdent", (glob_module, glob_object))

convertExpr :: Expression Int VarHeap -> BEMonad BENodeP
convertExpr  expr main_dcl_module_n varHeap
	= convertExpr expr varHeap
where
	convertExpr :: Expression VarHeap -> BEMonad BENodeP
	convertExpr  (BasicExpr value _) varHeap
		=	beNormalNode (convertLiteralSymbol value) beNoArgs
	convertExpr  (App {app_symb, app_args}) varHeap
		=	beNormalNode (convertSymbol app_symb) (convertArgs app_args varHeap)
		where
			convertSymbol :: !SymbIdent -> BEMonad BESymbolP
			convertSymbol {symb_kind=SK_Function {glob_module, glob_object}}
				=	beFunctionSymbol glob_object glob_module
			convertSymbol {symb_kind=SK_LocalMacroFunction glob_object}
				=	beFunctionSymbol glob_object main_dcl_module_n
			convertSymbol {symb_kind=SK_GeneratedFunction _ index}
				=	beFunctionSymbol index main_dcl_module_n
			convertSymbol {symb_kind=SK_Constructor {glob_module, glob_object}}
				=	beConstructorSymbol glob_module glob_object // ->> ("convertSymbol", (glob_module, glob_object))
			convertSymbol symbol
				=	undef <<- ("backendconvert, convertSymbol: unknown symbol", symbol)
	convertExpr (Var var) varHeap
		=	beNodeIdNode (convertVar var.var_info_ptr varHeap) beNoArgs
	convertExpr (f @ [a]) varHeap
		=	beNormalNode (beBasicSymbol BEApplySymb) (convertArgs [f, a] varHeap)
	convertExpr (f @ [a:as]) varHeap
		=	convertExpr (f @ [a] @ as) varHeap
	convertExpr (Selection isUnique expression selections) varHeap
		=	convertSelections (convertExpr expression varHeap) varHeap (addKinds isUnique selections)
		where
			addKinds No selections
				=	[(BESelector, selection) \\ selection <- selections]
			addKinds _ [selection]
				=	[(BESelector_U, selection)]
			addKinds _ [selection : selections]
				=	[(BESelector_F, selection) : addMoreKinds selections]
				where
					addMoreKinds []
						=	[]
					addMoreKinds [selection]
						=	[(BESelector_L, selection)]
					addMoreKinds [selection : selections]
						=	[(BESelector_N, selection) : addMoreKinds selections]
			addKinds _ []
				=	[]
	convertExpr (RecordUpdate _ expr updates) varHeap
		=	foldl (convertUpdate varHeap) (convertExpr expr varHeap) updates
		where
			convertUpdate varHeap  expr {bind_src=NoBind _}
				=	expr
			convertUpdate varHeap expr {bind_src, bind_dst=bind_dst=:{glob_module, glob_object={fs_index}}}
				=	beUpdateNode
						(beArgs
							expr
							(beArgs
								(beSelectorNode BESelector (beFieldSymbol fs_index glob_module)
								(beArgs (convertExpr bind_src varHeap)
								beNoArgs))
							beNoArgs))
	convertExpr (Update expr1 [singleSelection] expr2) varHeap
		=	case singleSelection of
				RecordSelection _ _
					->	beUpdateNode (convertArgs [expr1, Selection No expr2 [singleSelection]] varHeap)
				ArraySelection {glob_object={ds_index}, glob_module} _ index
	// RWS not used?, eleminate beSpecialArrayFunctionSymbol?
					->	beNormalNode
							(beSpecialArrayFunctionSymbol BEArrayUpdateFun ds_index glob_module)
							(convertArgs [expr1, index, expr2] varHeap)
	//
				DictionarySelection dictionaryVar dictionarySelections _ index
					->	convertExpr (Selection No (Var dictionaryVar) dictionarySelections @ [expr1, index, expr2]) varHeap
	convertExpr (Update expr1 selections expr2) varHeap
		=	case lastSelection of
				RecordSelection _ _
					->	beUpdateNode (beArgs selection (convertArgs [Selection No expr2 [lastSelection]] varHeap))
				ArraySelection {glob_object={ds_index}, glob_module} _ index
					->	beNormalNode (beSpecialArrayFunctionSymbol BE_ArrayUpdateFun ds_index glob_module) (beArgs selection (convertArgs [index, expr2] varHeap))
				DictionarySelection dictionaryVar dictionarySelections _ index
					->	beNormalNode beDictionaryUpdateFunSymbol
								(beArgs dictionary (beArgs selection (convertArgs [index, expr2] varHeap)))
						with
							dictionary
								=	convertExpr (Selection No (Var dictionaryVar) dictionarySelections) varHeap
		where
			lastSelection
				=	last selections
			selection
				=	convertSelections (convertExpr expr1 varHeap) varHeap (addKinds (init selections))
			addKinds [selection : selections]
				=	[(BESelector_F, selection) : addMoreKinds selections]
				where
					addMoreKinds selections
						=	[(BESelector_U, selection) \\ selection <- selections]
			addKinds []
				=	[]
	convertExpr (TupleSelect {ds_arity} n expr) varHeap
		=	beTupleSelectNode ds_arity n (convertExpr expr varHeap)
	convertExpr (MatchExpr optionalTuple {glob_module, glob_object={ds_index}} expr) varHeap
		=	beMatchNode (arity optionalTuple) (beConstructorSymbol glob_module ds_index) (convertExpr expr varHeap)
		where
			arity :: (Optional (Global DefinedSymbol)) -> Int
			arity No
				=	1
			arity (Yes {glob_object={ds_arity}})
				=	ds_arity
	convertExpr (Conditional {if_cond=cond, if_then, if_else=Yes else}) varHeap
		=	beIfNode (convertExpr cond varHeap) (convertExpr if_then varHeap) (convertExpr else varHeap)
	convertExpr  expr _
		=	undef <<- ("backendconvert, convertExpr: unknown expression", expr)

	convertArgs :: [Expression] VarHeap -> BEMonad BEArgP
	convertArgs exprs varHeap
		=	sfoldr (beArgs o flip convertExpr varHeap) beNoArgs exprs
	
	convertSelections :: (BEMonad BENodeP) VarHeap [(BESelectorKind, Selection)] -> (BEMonad BENodeP)
	convertSelections expression varHeap selections
		=	foldl (convertSelection varHeap) expression selections
	
	convertSelection :: VarHeap (BEMonad BENodeP) (BESelectorKind, Selection) -> (BEMonad BENodeP)
	convertSelection varHeap expression (kind, RecordSelection {glob_object={ds_index}, glob_module} _)
		=	beSelectorNode kind (beFieldSymbol ds_index glob_module) (beArgs expression beNoArgs)
	convertSelection varHeap expression (kind, ArraySelection {glob_object={ds_index}, glob_module} _ index)
		=	beNormalNode (beSpecialArrayFunctionSymbol (selectionKindToArrayFunKind kind) ds_index glob_module) (beArgs expression (convertArgs [index] varHeap))
	convertSelection varHeap expression (kind, DictionarySelection dictionaryVar dictionarySelections _ index)
		=	case kind of
				BESelector
					->	beNormalNode (beBasicSymbol BEApplySymb)
								(beArgs
									(beNormalNode (beBasicSymbol BEApplySymb)
									(beArgs dictionary
										(beArgs expression beNoArgs)))
								(convertArgs [index] varHeap))
				_
					->	beNormalNode beDictionarySelectFunSymbol
								(beArgs dictionary (beArgs expression (convertArgs [index] varHeap)))
			where
				dictionary
					=	convertExpr (Selection No (Var dictionaryVar) dictionarySelections) varHeap

selectionKindToArrayFunKind BESelector
	=	BEArraySelectFun
selectionKindToArrayFunKind BESelector_U
	=	BE_UnqArraySelectFun
selectionKindToArrayFunKind BESelector_F
	=	BE_UnqArraySelectFun
selectionKindToArrayFunKind BESelector_L
	=	BE_UnqArraySelectLastFun
selectionKindToArrayFunKind BESelector_N
	=	BE_UnqArraySelectLastFun

convertVar :: VarInfoPtr VarHeap -> BEMonad BENodeIdP
convertVar varInfo varHeap
	= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber varInfo varHeap be0 in
		beNodeId variable_sequence_number be

getVariableSequenceNumber :: VarInfoPtr VarHeap *BackEndState-> (!Int,!*BackEndState)
getVariableSequenceNumber varInfoPtr varHeap be
	# (vi,be) = read_from_var_heap varInfoPtr varHeap be
	= case vi of
		VI_SequenceNumber sequenceNumber
			-> (sequenceNumber,be)
		VI_Alias {var_info_ptr}
			-> getVariableSequenceNumber var_info_ptr varHeap be

markExports :: DclModule {#ClassDef} {#CheckedTypeDef} {#ClassDef} {#CheckedTypeDef} (Optional {#Int}) -> BackEnder
markExports {dcl_conversions = Yes conversionTable} dclClasses dclTypes iclClasses iclTypes (Yes functionConversions)
	=	foldStateA (\icl -> beExportType icl icl) conversionTable.[cTypeDefs]
	o	foldStateWithIndexA beExportConstructor conversionTable.[cConstructorDefs]
	o	foldStateWithIndexA beExportField conversionTable.[cSelectorDefs]
	o	foldStateWithIndexA (exportDictionary iclClasses iclTypes) conversionTable.[cClassDefs]
	o	foldStateWithIndexA beExportFunction functionConversions
	where
		exportDictionary :: {#ClassDef} {#CheckedTypeDef} Index Index -> BackEnder
		exportDictionary iclClasses iclTypes dclClassIndex iclClassIndex
			=	beExportType (-1) iclTypeIndex	// remove -1 hack
			o	foldStateA exportDictionaryField rt_fields
			where
				dclTypeIndex
					=	dclClasses.[dclClassIndex].class_dictionary.ds_index
				iclTypeIndex
					=	iclClasses.[iclClassIndex].class_dictionary.ds_index
				{td_rhs = RecordType {rt_fields}}
					=	iclTypes.[iclTypeIndex]

				exportDictionaryField :: FieldSymbol -> BackEnder
				exportDictionaryField {fs_index}
					=	beExportField (-1) fs_index	// remove -1 hack
markExports _ _ _ _ _ _
	=	identity
