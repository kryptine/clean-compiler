/*
	module owner: Ronny Wichers Schreur
*/
implementation module backendinterface

import StdEnv

import frontend
import backend
import backendpreprocess, backendsupport, backendconvert
import Version

checkVersion :: VersionsCompatability *File -> (!Bool, !*File)
checkVersion VersionsAreCompatible errorFile
	=	(True, errorFile)
checkVersion VersionObservedIsTooNew errorFile
	#	errorFile
			=	fwrites "[Backend] the back end library is too new\n" errorFile
	=	(False, errorFile)
checkVersion VersionObservedIsTooOld errorFile
	#	errorFile
			=	fwrites "[Backend] the back end library is too old\n" errorFile
	=	(False, errorFile)

backEndInterface :: !{#Char} [{#Char}] !ListTypesOption !{#Char} !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*AttrVarHeap !*File !*Files -> (!Bool, !*VarHeap, !*AttrVarHeap, !*File, !*Files)
backEndInterface outputFileName commandLineArgs listTypes typesPath predef_symbols syntaxTree=:{fe_icl,fe_components,fe_dcls} main_dcl_module_n var_heap attrHeap errorFile files
	# (observedCurrent, observedOldestDefinition, observedOldestImplementation)
		=	BEGetVersion
	  observedVersion =
		{	versionCurrent
				=	observedCurrent
		,	versionOldestDefinition
				=	observedOldestDefinition
		,	versionOldestImplementation
				=	observedOldestImplementation
		}
	  expectedVersion =
		{	versionCurrent
				=	kBEVersionCurrent
		,	versionOldestDefinition
				=	kBEVersionOldestDefinition
		,	versionOldestImplementation
				=	kBEVersionOldestImplementation
		}
	# (compatible, errorFile)
		=	checkVersion (versionCompare expectedVersion observedVersion) errorFile
	| not compatible
		=	(False, var_heap, attrHeap, errorFile, files)
	# varHeap
		=	backEndPreprocess predef_symbols.[PD_DummyForStrictAliasFun].pds_ident functionIndices fe_icl var_heap
		with
			functionIndices
				=	flatten [[member \\ member <- group.group_members] \\ group <-: fe_components]
	# backEndFiles
		=	0
	# (backEnd, backEndFiles)
		=	BEInit (length commandLineArgs) backEndFiles
	# backEnd
		=	foldState BEArg commandLineArgs backEnd
	# (var_heap, attrHeap, backEnd)
		=	backEndConvertModules predef_symbols syntaxTree main_dcl_module_n varHeap attrHeap backEnd
	# (success, backEnd)
		=	BEGenerateCode outputFileName backEnd
	# backEnd
		=	BECloseFiles backEnd
	# (attrHeap, files, backEnd)
		// FIXME: should be type file
		=	optionallyPrintFunctionTypes listTypes typesPath (DictionaryToClassInfo main_dcl_module_n fe_icl fe_dcls) fe_components fe_icl.icl_functions attrHeap files backEnd
	# backEndFiles
		=	BEFree backEnd backEndFiles
	=	(backEndFiles == 0 && success, var_heap, attrHeap, errorFile, files)
import typesupport

optionallyPrintFunctionTypes :: ListTypesOption {#Char} DictionaryToClassInfo {!Group} {#FunDef} *AttrVarHeap *Files !*BackEnd -> (*AttrVarHeap, *Files, *BackEnd)
optionallyPrintFunctionTypes {lto_listTypesKind, lto_showAttributes} typesPath info components functions attrHeap files backEnd
	| lto_listTypesKind == ListTypesStrictExports || lto_listTypesKind == ListTypesAll
		# (opened, typesFile, files)
			=	fopen typesPath FAppendText files
		| not opened
			=	abort ("couldn't open types file \"" +++ typesPath +++ "\"\n")
		# (attrHeap, typesFile, backEnd)
			=	printFunctionTypes (lto_listTypesKind == ListTypesAll) lto_showAttributes info components functions attrHeap typesFile backEnd
		# (closed, files)
			=	fclose typesFile files
		| not closed
			=	abort ("couldn't close types file \"" +++ typesPath +++ "\"\n")
		=	(attrHeap, files, backEnd)
	// otherwise
		=	(attrHeap, files, backEnd)

printFunctionTypes :: Bool Bool DictionaryToClassInfo {!Group} {#FunDef} *AttrVarHeap *File *BackEnd -> (*AttrVarHeap, *File, *BackEnd)
printFunctionTypes all attr info components functions attrHeap file backEnd
	=	foldSt (printFunctionType all attr info) [(index, functions.[index]) \\ (_, index) <- functionIndices] (attrHeap, file, backEnd)
	where
		functionIndices
			=	flatten [[(componentIndex, member) \\ member <- group.group_members] \\ group <-: components & componentIndex <- [1..]]

printFunctionType :: Bool Bool DictionaryToClassInfo (Int, FunDef) (*AttrVarHeap, *File, *BackEnd) -> (*AttrVarHeap, *File, *BackEnd)
printFunctionType all attr info (functionIndex, {fun_symb,fun_type=Yes type}) (attrHeap, file, backEnd)
	| not all && functionIndex >= size info.dtic_dclModules.[info.dtci_iclModuleIndex].dcl_functions
		=	(attrHeap, file, backEnd)
	# (strictnessAdded, type, backEnd)
		=	addStrictnessFromBackEnd functionIndex fun_symb.id_name backEnd type
	| not strictnessAdded && not all
		=	(attrHeap, file, backEnd)
	// FIXME: shouldn't have to repair the invariant here
	# (type, attrHeap)
		=	collectSymbolTypeAttrVars type attrHeap
	# type
		=	dictionariesToClasses info type
	# (type, attrHeap)
		=	beautifulizeAttributes type attrHeap
	# file
		=	file <<< fun_symb <<< " :: "
				<:: ({ form_properties = (if attr cAttributed 0) bitor cAnnotated, form_attr_position = No }, type, Yes initialTypeVarBeautifulizer) <<< '\n'
	=	(attrHeap, file, backEnd)

addStrictnessFromBackEnd :: Int {#Char} *BackEnd SymbolType -> (Bool, SymbolType, *BackEnd)
addStrictnessFromBackEnd functionIndex functionName backEnd type
	# (bitSize, strictPositionsC, backEnd)
		=	BEStrictPositions functionIndex backEnd
	| bitSize == 0 // short cut
		=	(False, type, backEnd)
	# strictPositions
		=	copyInts ((bitSize+31)/32) strictPositionsC // assumes 32 bit ints
	# strictnessInfo
		=	{si_robust_encoding = False, si_positions = strictPositions, si_size = bitSize, si_name = functionName}
	  offset
	  	=	0
	# (robust, offset)
		=	nextBit strictnessInfo offset
	  strictnessInfo
	  	=	{strictnessInfo & si_robust_encoding = robust}
	# (anyStrictnessAdded, offset)
		=	nextBit strictnessInfo offset
	# (type, offset)
		=	addStrictness strictnessInfo type offset
	# type
		=	checkFinalOffset strictnessInfo offset type
	= (anyStrictnessAdded, type, backEnd)

:: StrictnessInfo =
	{	si_size :: !Int
	,	si_positions :: !LargeBitvect
	,	si_name :: {#Char}
	,	si_robust_encoding :: !Bool
	}

class addStrictness a :: !StrictnessInfo !a Int -> (!a, !Int)

nextBit :: StrictnessInfo Int -> (Bool, Int)
nextBit {si_size, si_positions, si_robust_encoding} offset
	| offset < si_size
		=	(bitvectSelect offset si_positions, offset+1)
	// otherwise
		| si_robust_encoding
			=	abort "backendinterface, nextBit: bit vector too small"
		// otherwise
			=	(False, offset)

checkStrictness :: StrictnessInfo Bool Int -> Int
checkStrictness info=:{si_robust_encoding} wasStrict offset
	| si_robust_encoding
		# (bit, offset)
			=	nextBit info offset
		| bit <> wasStrict
			=	abort "backendinterface, checkStrictness: wrong info for strictness annotation"
		=	offset
	// otherwise
		=	offset

checkType :: StrictnessInfo Bool Int -> Int
checkType info=:{si_robust_encoding} isTuple offset
	| si_robust_encoding
		# (bit, offset)
			=	nextBit info offset
		| bit <> isTuple
			=	abort "backendinterface, checkType: wrong type"
		=	offset
	// otherwise
		=	offset

checkFinalOffset :: StrictnessInfo Int a -> a
checkFinalOffset info=:{si_size, si_robust_encoding} offset value
	| offset < si_size || (si_robust_encoding && offset > si_size)
		=	abort "backendinterface, checkFinalOffset: wrong offset"
	// otherwise
		=	value

instance addStrictness SymbolType where
	addStrictness strictPositions=:{si_size} args offset
		| offset >= si_size // short cut
			=	(args, offset)
	addStrictness strictPositions type=:{st_args} offset
		# (st_args, offset)
			=	addStrictness strictPositions st_args offset
		=	({type & st_args = st_args}, offset)

instance addStrictness [a] | addStrictness a where
	addStrictness strictPositions l offset
		=	mapSt (addStrictness strictPositions) l offset

instance addStrictness AType where
	addStrictness strictPositions arg=:{at_annotation, at_type} offset
		# (at_annotation, offset)
			=	addStrictness strictPositions at_annotation offset
		# (at_type, offset)
			=	addStrictnessToType strictPositions (at_annotation == AN_Strict) at_type offset
		=	({arg & at_annotation = at_annotation, at_type = at_type}, offset)

instance addStrictness Annotation where
	addStrictness info annotation offset
		# offset
			=	checkStrictness info wasStrict offset
		# (strictAdded, offset)
			=	nextBit info offset
		| strictAdded
			| wasStrict
				=	abort "backendinterface, addStrictness: already strict"
			// otherwise
				=	(AN_Strict, offset)
		// otherwise
			=	(annotation, offset)
		where
			wasStrict
				=	annotation == AN_Strict

addStrictnessToType :: StrictnessInfo Bool Type Int -> (Type, Int)
addStrictnessToType strictPositions isStrict type=:(TA ident=:{type_name,type_arity} args) offset
	# offset
		=	checkType strictPositions isTuple offset
	| isTuple && isStrict
		# (args, offset)
			=	addStrictness strictPositions args offset
		=	(TA ident args, offset)
	// otherwise
		=	(type, offset)
	where
		// FIXME: don't match on name but use predef info
		isTuple
			= type_name.id_name == "_Tuple" +++ toString type_arity
addStrictnessToType strictPositions _ type offset
	# offset
		=	checkType strictPositions False offset
	=	(type, offset)

collectSymbolTypeAttrVars :: SymbolType *AttrVarHeap -> (SymbolType, *AttrVarHeap)
collectSymbolTypeAttrVars type=:{st_attr_vars, st_result, st_args} attrVarHeap
	# attrVarHeap
		=	foldSt markAttrVarCollected st_attr_vars attrVarHeap
	# (st_attr_vars, attrVarHeap)
		=	collectAttrVars st_result (collectAttrVars st_args (st_attr_vars, attrVarHeap))
	=	({type & st_attr_vars = st_attr_vars}, attrVarHeap)

/* maybe should collect st_vars as well (these are not used currently) */
class collectAttrVars a :: a ([AttributeVar], *AttrVarHeap) -> ([AttributeVar], *AttrVarHeap)

instance collectAttrVars AType where
	collectAttrVars {at_attribute, at_type} collect
		=	collectAttrVars at_attribute (collectAttrVars at_type collect)

instance collectAttrVars TypeAttribute where
	collectAttrVars (TA_Var attrVar) collect
		=	collectAttrVars attrVar collect
	collectAttrVars (TA_RootVar attrVar) collect
		=	collectAttrVars attrVar collect
	collectAttrVars (TA_List _ attribute) collect
		=	collectAttrVars attribute collect
	collectAttrVars (TA_Locked attribute) collect
		=	collectAttrVars attribute collect
	collectAttrVars _ collect
		=	collect

instance collectAttrVars Type where
	collectAttrVars (TA _ types) collect
		=	collectAttrVars types collect
	collectAttrVars (type1 --> type2) collect
		=	collectAttrVars type1 (collectAttrVars type2 collect)
	collectAttrVars (TArrow1 type) collect
		=	collectAttrVars type collect
	collectAttrVars (_ :@: types) collect
		=	collectAttrVars types collect
	collectAttrVars (TFA _ type) collect
		=	collectAttrVars type collect
	collectAttrVars _ collect
		=	collect

instance collectAttrVars AttributeVar where
	collectAttrVars  attrVar=:{av_info_ptr} (attrVars, attrVarHeap)
		# (info, attrVarHeap)
			=	readPtr av_info_ptr attrVarHeap
		=	case info of
				AVI_Collected
					->	(attrVars, attrVarHeap)
				_
					->	([attrVar : attrVars], markAttrVarCollected attrVar attrVarHeap)

instance collectAttrVars [a] | collectAttrVars a where
	collectAttrVars l collect
		=	foldSt collectAttrVars l collect

markAttrVarCollected :: AttributeVar *AttrVarHeap -> *AttrVarHeap
markAttrVarCollected {av_info_ptr} attrVarHeap
	=	writePtr av_info_ptr AVI_Collected attrVarHeap

:: DictionaryToClassInfo =
	{	dtci_iclModuleIndex :: Int
	,	dtci_iclModule :: IclModule
	,	dtic_dclModules :: {#DclModule}
	}

DictionaryToClassInfo iclModuleIndex iclModule dclModules :== 
	{	dtci_iclModuleIndex = iclModuleIndex
	,	dtci_iclModule = iclModule
	,	dtic_dclModules = dclModules
	}

dictionariesToClasses :: DictionaryToClassInfo SymbolType -> SymbolType
dictionariesToClasses info type=:{st_args, st_arity, st_context=[]}
	# (reversedTypes, reversedContexts)
		=	dictionaryArgsToClasses info st_args ([], [])
	=	{type & st_args = reverse reversedTypes, st_context = reverse reversedContexts,
				st_arity = st_arity - length reversedContexts}

dictionaryArgsToClasses :: DictionaryToClassInfo [AType] ([AType], [TypeContext]) -> ([AType], [TypeContext])
dictionaryArgsToClasses info args result
	=	foldSt (dictionaryArgToClass info) args result

dictionaryArgToClass :: DictionaryToClassInfo AType ([AType], [TypeContext]) -> ([AType], [TypeContext])
dictionaryArgToClass info type=:{at_type=TA typeSymbol args} (reversedTypes, reversedContexts)
	=	case typeToClass info typeSymbol of
			Yes klass
				->	(reversedTypes, [context : reversedContexts])
				with
					context	
						=	{tc_class = klass, tc_types = [at_type \\ {at_type} <- args], tc_var = nilPtr}
			No
				->	([type : reversedTypes], reversedContexts)
dictionaryArgToClass _ type (reversedTypes, reversedContexts)
	=	([type : reversedTypes], reversedContexts)

typeToClass :: DictionaryToClassInfo TypeSymbIdent -> Optional (Global DefinedSymbol)
typeToClass info {type_name, type_arity, type_index={glob_module, glob_object}}
	=	case typeIndexToClassIndex info glob_module glob_object of
			Yes classIndex
				->	Yes {glob_module=glob_module, glob_object = {ds_ident = type_name, ds_arity = type_arity, ds_index = glob_object}}
			No
				->	No
	where
		/*
			This how the types are organised (#classes == #dictionaries)

						  com_classes
			+--------(1)-------+--------(2)-------+
			|   dcl classes    |   icl classes    |
			+------------------+------------------+
						  nDclClasses		 nIclClasses

									com_type_defs
			+-----------+--------(1)-------+-----------+--------(2)-------+
			| dcl types | dcl dictionaries | icl types | icl dictionaries |
			+-----------+------------------+-----------+------------------+
									   nDclTypes					   nIclTypes
		*/
		typeIndexToClassIndex :: DictionaryToClassInfo Int Int -> Optional Int
		typeIndexToClassIndex {dtci_iclModuleIndex, dtci_iclModule, dtic_dclModules} moduleIndex typeIndex
			| moduleIndex <> dtci_iclModuleIndex || typeIndex < nDclTypes
				=	toClassIndex typeIndex nDclTypes nDclClasses 0
			// otherwise
				=	toClassIndex (typeIndex-nDclTypes) (nIclTypes-nDclTypes) (nIclClasses-nDclClasses) nDclClasses
			where
				dclModule
					=	dtic_dclModules.[moduleIndex]
				nDclTypes
					=	size dclModule.dcl_common.com_type_defs
				nDclClasses
					=	size dclModule.dcl_common.com_class_defs
				nIclTypes
					=	size dtci_iclModule.icl_common.com_type_defs
				nIclClasses
					=	size dtci_iclModule.icl_common.com_class_defs

				toClassIndex :: Int Int Int Int -> Optional Int
				toClassIndex typeIndex nTypes nClasses offset
					| classIndex < 0
						=	No
					// otherwise
						=	Yes (classIndex + offset)
					where
						classIndex
							=	typeIndex - (nTypes - nClasses)

copyInts :: !Int !Int -> {#Int}
copyInts length cArray
    = code {
    		push_b 0
            create_array_ INT 0 1
  
            push_a  0
            ccall   BECopyInts "IIA-I"
            pop_b   1
	}
