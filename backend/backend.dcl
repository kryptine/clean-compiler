definition module backend;

//1.3
from StdString import String;
//3.1

:: CPtr (:== Int);
:: *UWorld :== Int;
:: *BackEnd (:== CPtr);
:: BESymbolP (:== CPtr);
:: BETypeNodeP (:== CPtr);
:: BETypeArgP (:== CPtr);
:: BETypeAltP (:== CPtr);
:: BENodeP (:== CPtr);
:: BEArgP (:== CPtr);
:: BERuleAltP (:== CPtr);
:: BEImpRuleP (:== CPtr);
:: BETypeP (:== CPtr);
:: BEFlatTypeP (:== CPtr);
:: BETypeVarP (:== CPtr);
:: BETypeVarListP (:== CPtr);
:: BEConstructorListP (:== CPtr);
:: BEFieldListP (:== CPtr);
:: BENodeIdP (:== CPtr);
:: BENodeDefP (:== CPtr);
:: BEStrictNodeIdP (:== CPtr);
:: BECodeParameterP (:== CPtr);
:: BECodeBlockP (:== CPtr);
:: BEStringListP (:== CPtr);
:: BENodeIdListP (:== CPtr);
:: BENodeIdRefCountListP (:== CPtr);
:: BEUniVarEquations (:== CPtr);
:: BEAttributeKindList (:== CPtr);
:: BEAnnotation :== Int;
:: BEAttribution :== Int;
:: BESymbKind :== Int;
:: BEArrayFunKind :== Int;
:: BESelectorKind :== Int;
:: BESpecialIdentIndex :== Int;
BEGetVersion :: (!Int,!Int,!Int);
// void BEGetVersion (int* current,int* oldestDefinition,int* oldestImplementation);
BEInit :: !Int !UWorld -> (!BackEnd,!UWorld);
// BackEnd BEInit (int argc);
BECloseFiles :: !BackEnd -> BackEnd;
// void BECloseFiles ();
BEFree :: !BackEnd !UWorld -> UWorld;
// void BEFree (BackEnd backEnd);
BEArg :: !String !BackEnd -> BackEnd;
// void BEArg (CleanString arg);
BEDeclareModules :: !Int !BackEnd -> BackEnd;
// void BEDeclareModules (int nModules);
BEBindSpecialModule :: !BESpecialIdentIndex !Int !BackEnd -> BackEnd;
// void BEBindSpecialModule (BESpecialIdentIndex index,int moduleIndex);
BEBindSpecialFunction :: !BESpecialIdentIndex !Int !Int !BackEnd -> BackEnd;
// void BEBindSpecialFunction (BESpecialIdentIndex index,int functionIndex,int moduleIndex);
BESpecialArrayFunctionSymbol :: !BEArrayFunKind !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BESpecialArrayFunctionSymbol (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BEDictionarySelectFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionarySelectFunSymbol ();
BEDictionaryUpdateFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionaryUpdateFunSymbol ();
BEFunctionSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFunctionSymbol (int functionIndex,int moduleIndex);
BEConstructorSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEConstructorSymbol (int constructorIndex,int moduleIndex);
BEFieldSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFieldSymbol (int fieldIndex,int moduleIndex);
BETypeSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BETypeSymbol (int typeIndex,int moduleIndex);
BEDontCareDefinitionSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDontCareDefinitionSymbol ();
BEBoolSymbol :: !Bool !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBoolSymbol (int value);
BELiteralSymbol :: !BESymbKind !String !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BELiteralSymbol (BESymbKind kind,CleanString value);
BEPredefineListConstructorSymbol :: !Int !Int !BESymbKind !Int !Int !BackEnd -> BackEnd;
// void BEPredefineListConstructorSymbol (int constructorIndex,int moduleIndex,BESymbKind symbolKind,int head_strictness,int tail_strictness);
BEPredefineListTypeSymbol :: !Int !Int !BESymbKind !Int !Int !BackEnd -> BackEnd;
// void BEPredefineListTypeSymbol (int typeIndex,int moduleIndex,BESymbKind symbolKind,int head_strictness,int tail_strictness);
BEAdjustStrictListConsInstance :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustStrictListConsInstance (int functionIndex,int moduleIndex);
BEAdjustUnboxedListDeconsInstance :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustUnboxedListDeconsInstance (int functionIndex,int moduleIndex);
BEAdjustOverloadedNilFunction :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustOverloadedNilFunction (int functionIndex,int moduleIndex);
BEOverloadedConsSymbol :: !Int !Int !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEOverloadedConsSymbol (int constructorIndex,int moduleIndex,int deconsIndex,int deconsModuleIndex);
BEOverloadedPushNode :: !Int !BESymbolP !BEArgP !BENodeIdListP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEOverloadedPushNode (int arity,BESymbolP symbol,BEArgP arguments,BENodeIdListP nodeIds,BENodeP decons_node);
BEPredefineConstructorSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineConstructorSymbol (int arity,int constructorIndex,int moduleIndex,BESymbKind symbolKind);
BEPredefineTypeSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineTypeSymbol (int arity,int typeIndex,int moduleIndex,BESymbKind symbolKind);
BEBasicSymbol :: !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBasicSymbol (BESymbKind kind);
BEVarTypeNode :: !String !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEVarTypeNode (CleanString name);
BETypeVarListElem :: !BETypeVarP !BEAttribution !BackEnd -> (!BETypeVarListP,!BackEnd);
// BETypeVarListP BETypeVarListElem (BETypeVarP typeVar,BEAttribution attribute);
BETypeVars :: !BETypeVarListP !BETypeVarListP !BackEnd -> (!BETypeVarListP,!BackEnd);
// BETypeVarListP BETypeVars (BETypeVarListP typeVarListElem,BETypeVarListP typeVarList);
BENoTypeVars :: !BackEnd -> (!BETypeVarListP,!BackEnd);
// BETypeVarListP BENoTypeVars ();
BENormalTypeNode :: !BESymbolP !BETypeArgP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BENormalTypeNode (BESymbolP symbol,BETypeArgP args);
BEAnnotateTypeNode :: !BEAnnotation !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEAnnotateTypeNode (BEAnnotation annotation,BETypeNodeP typeNode);
BEAddForAllTypeVariables :: !BETypeVarListP !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEAddForAllTypeVariables (BETypeVarListP vars,BETypeNodeP type);
BEAttributeTypeNode :: !BEAttribution !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEAttributeTypeNode (BEAttribution attribution,BETypeNodeP typeNode);
BEAttributeKind :: !BEAttribution !BackEnd -> (!BEAttributeKindList,!BackEnd);
// BEAttributeKindList BEAttributeKind (BEAttribution attributeKind);
BENoAttributeKinds :: !BackEnd -> (!BEAttributeKindList,!BackEnd);
// BEAttributeKindList BENoAttributeKinds ();
BEAttributeKinds :: !BEAttributeKindList !BEAttributeKindList !BackEnd -> (!BEAttributeKindList,!BackEnd);
// BEAttributeKindList BEAttributeKinds (BEAttributeKindList elem,BEAttributeKindList list);
BEUniVarEquation :: !BEAttribution !BEAttributeKindList !BackEnd -> (!BEUniVarEquations,!BackEnd);
// BEUniVarEquations BEUniVarEquation (BEAttribution demanded,BEAttributeKindList offered);
BENoUniVarEquations :: !BackEnd -> (!BEUniVarEquations,!BackEnd);
// BEUniVarEquations BENoUniVarEquations ();
BEUniVarEquationsList :: !BEUniVarEquations !BEUniVarEquations !BackEnd -> (!BEUniVarEquations,!BackEnd);
// BEUniVarEquations BEUniVarEquationsList (BEUniVarEquations elem,BEUniVarEquations list);
BENoTypeArgs :: !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BENoTypeArgs ();
BETypeArgs :: !BETypeNodeP !BETypeArgP !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BETypeArgs (BETypeNodeP node,BETypeArgP nextArgs);
BETypeAlt :: !BETypeNodeP !BETypeNodeP !BEUniVarEquations !BackEnd -> (!BETypeAltP,!BackEnd);
// BETypeAltP BETypeAlt (BETypeNodeP lhs,BETypeNodeP rhs,BEUniVarEquations attributeEquations);
BENormalNode :: !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENormalNode (BESymbolP symbol,BEArgP args);
BEMatchNode :: !Int !BESymbolP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEMatchNode (int arity,BESymbolP symbol,BENodeP node);
BETupleSelectNode :: !Int !Int !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BETupleSelectNode (int arity,int index,BENodeP node);
BEIfNode :: !BENodeP !BENodeP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEIfNode (BENodeP cond,BENodeP then,BENodeP elsje);
BEGuardNode :: !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEGuardNode (BENodeP cond,BENodeDefP thenNodeDefs,BEStrictNodeIdP thenStricts,BENodeP then,BENodeDefP elseNodeDefs,BEStrictNodeIdP elseStricts,BENodeP elsje);
BESetNodeDefRefCounts :: !BENodeP !BackEnd -> BackEnd;
// void BESetNodeDefRefCounts (BENodeP lhs);
BEAddNodeIdsRefCounts :: !Int !BESymbolP !BENodeIdListP !BackEnd -> BackEnd;
// void BEAddNodeIdsRefCounts (int sequenceNumber,BESymbolP symbol,BENodeIdListP nodeIds);
BESwitchNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BESwitchNode (BENodeIdP nodeId,BEArgP caseNode);
BECaseNode :: !Int !BESymbolP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BECaseNode (int symbolArity,BESymbolP symbol,BENodeDefP nodeDefs,BEStrictNodeIdP strictNodeIds,BENodeP node);
BEEnterLocalScope :: !BackEnd -> BackEnd;
// void BEEnterLocalScope ();
BELeaveLocalScope :: !BENodeP !BackEnd -> BackEnd;
// void BELeaveLocalScope (BENodeP node);
BEPushNode :: !Int !BESymbolP !BEArgP !BENodeIdListP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEPushNode (int arity,BESymbolP symbol,BEArgP arguments,BENodeIdListP nodeIds);
BEDefaultNode :: !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEDefaultNode (BENodeDefP nodeDefs,BEStrictNodeIdP strictNodeIds,BENodeP node);
BESelectorNode :: !BESelectorKind !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BESelectorNode (BESelectorKind selectorKind,BESymbolP fieldSymbol,BEArgP args);
BEUpdateNode :: !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEUpdateNode (BEArgP args);
BENodeIdNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENodeIdNode (BENodeIdP nodeId,BEArgP args);
BENoArgs :: !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BENoArgs ();
BEArgs :: !BENodeP !BEArgP !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BEArgs (BENodeP node,BEArgP nextArgs);
BERuleAlt :: !Int !BENodeDefP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BERuleAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BENodeDefP rhsDefs,BEStrictNodeIdP lhsStrictNodeIds,BENodeP rhs);
BERuleAlts :: !BERuleAltP !BERuleAltP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BERuleAlts (BERuleAltP alt,BERuleAltP alts);
BENoRuleAlts :: !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BENoRuleAlts ();
BEDeclareNodeId :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareNodeId (int sequenceNumber,int lhsOrRhs,CleanString name);
BENodeId :: !Int !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BENodeId (int sequenceNumber);
BEWildCardNodeId :: !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BEWildCardNodeId ();
BENodeDef :: !Int !BENodeP !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENodeDef (int sequenceNumber,BENodeP node);
BENoNodeDefs :: !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENoNodeDefs ();
BENodeDefs :: !BENodeDefP !BENodeDefP !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENodeDefs (BENodeDefP nodeDef,BENodeDefP nodeDefs);
BEStrictNodeId :: !BENodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BEStrictNodeId (BENodeIdP nodeId);
BENoStrictNodeIds :: !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BENoStrictNodeIds ();
BEStrictNodeIds :: !BEStrictNodeIdP !BEStrictNodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BEStrictNodeIds (BEStrictNodeIdP strictNodeId,BEStrictNodeIdP strictNodeIds);
BERule :: !Int !Int !BETypeAltP !BERuleAltP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERule (int functionIndex,int isCaf,BETypeAltP type,BERuleAltP alts);
BEDeclareRuleType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareRuleType (int functionIndex,int moduleIndex,CleanString name);
BEDefineRuleType :: !Int !Int !BETypeAltP !BackEnd -> BackEnd;
// void BEDefineRuleType (int functionIndex,int moduleIndex,BETypeAltP typeAlt);
BEAdjustArrayFunction :: !BEArrayFunKind !Int !Int !BackEnd -> BackEnd;
// void BEAdjustArrayFunction (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BENoRules :: !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BENoRules ();
BERules :: !BEImpRuleP !BEImpRuleP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERules (BEImpRuleP rule,BEImpRuleP rules);
BETypes :: !BETypeP !BETypeP !BackEnd -> (!BETypeP,!BackEnd);
// BETypeP BETypes (BETypeP type,BETypeP types);
BENoTypes :: !BackEnd -> (!BETypeP,!BackEnd);
// BETypeP BENoTypes ();
BEFlatType :: !BESymbolP !BEAttribution !BETypeVarListP !BackEnd -> (!BEFlatTypeP,!BackEnd);
// BEFlatTypeP BEFlatType (BESymbolP symbol,BEAttribution attribution,BETypeVarListP arguments);
BEAlgebraicType :: !BEFlatTypeP !BEConstructorListP !BackEnd -> BackEnd;
// void BEAlgebraicType (BEFlatTypeP lhs,BEConstructorListP constructors);
BERecordType :: !Int !BEFlatTypeP !BETypeNodeP !Int !BEFieldListP !BackEnd -> BackEnd;
// void BERecordType (int moduleIndex,BEFlatTypeP lhs,BETypeNodeP constructorType,int is_boxed_record,BEFieldListP fields);
BEAbsType :: !BEFlatTypeP !BackEnd -> BackEnd;
// void BEAbsType (BEFlatTypeP lhs);
BEConstructors :: !BEConstructorListP !BEConstructorListP !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BEConstructors (BEConstructorListP constructor,BEConstructorListP constructors);
BENoConstructors :: !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BENoConstructors ();
BEConstructor :: !BETypeNodeP !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BEConstructor (BETypeNodeP type);
BEDeclareField :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareField (int fieldIndex,int moduleIndex,CleanString name);
BEField :: !Int !Int !BETypeNodeP !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BEField (int fieldIndex,int moduleIndex,BETypeNodeP type);
BEFields :: !BEFieldListP !BEFieldListP !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BEFields (BEFieldListP field,BEFieldListP fields);
BENoFields :: !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BENoFields ();
BEDeclareConstructor :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareConstructor (int constructorIndex,int moduleIndex,CleanString name);
BETypeVar :: !String !BackEnd -> (!BETypeVarP,!BackEnd);
// BETypeVarP BETypeVar (CleanString name);
BEDeclareType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareType (int typeIndex,int moduleIndex,CleanString name);
BEDeclareFunction :: !String !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareFunction (CleanString name,int arity,int functionIndex,int ancestor);
BECodeAlt :: !Int !BENodeDefP !BENodeP !BECodeBlockP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BECodeAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BECodeBlockP codeBlock);
BEString :: !String !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BEString (CleanString cleanString);
BEStrings :: !BEStringListP !BEStringListP !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BEStrings (BEStringListP string,BEStringListP strings);
BENoStrings :: !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BENoStrings ();
BECodeParameter :: !String !BENodeIdP !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BECodeParameter (CleanString location,BENodeIdP nodeId);
BECodeParameters :: !BECodeParameterP !BECodeParameterP !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BECodeParameters (BECodeParameterP parameter,BECodeParameterP parameters);
BENoCodeParameters :: !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BENoCodeParameters ();
BENodeIdListElem :: !BENodeIdP !BackEnd -> (!BENodeIdListP,!BackEnd);
// BENodeIdListP BENodeIdListElem (BENodeIdP nodeId);
BENodeIds :: !BENodeIdListP !BENodeIdListP !BackEnd -> (!BENodeIdListP,!BackEnd);
// BENodeIdListP BENodeIds (BENodeIdListP nid,BENodeIdListP nids);
BENoNodeIds :: !BackEnd -> (!BENodeIdListP,!BackEnd);
// BENodeIdListP BENoNodeIds ();
BEAbcCodeBlock :: !Bool !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAbcCodeBlock (int inline,BEStringListP instructions);
BEAnyCodeBlock :: !BECodeParameterP !BECodeParameterP !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAnyCodeBlock (BECodeParameterP inParams,BECodeParameterP outParams,BEStringListP instructions);
BEDeclareIclModule :: !String !String !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareIclModule (CleanString name,CleanString modificationTime,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclareDclModule :: !Int !String !String !Bool !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareDclModule (int moduleIndex,CleanString name,CleanString modificationTime,int systemModule,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclarePredefinedModule :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclarePredefinedModule (int nTypes,int nConstructors);
BEDefineRules :: !BEImpRuleP !BackEnd -> BackEnd;
// void BEDefineRules (BEImpRuleP rules);
BEGenerateCode :: !String !BackEnd -> (!Bool,!BackEnd);
// int BEGenerateCode (CleanString outputFile);
BEExportType :: !Bool !Int !BackEnd -> BackEnd;
// void BEExportType (int isDictionary,int typeIndex);
BEExportConstructor :: !Int !BackEnd -> BackEnd;
// void BEExportConstructor (int constructorIndex);
BEExportField :: !Bool !Int !BackEnd -> BackEnd;
// void BEExportField (int isDictionaryField,int fieldIndex);
BEExportFunction :: !Int !BackEnd -> BackEnd;
// void BEExportFunction (int functionIndex);
BEDefineImportedObjsAndLibs :: !BEStringListP !BEStringListP !BackEnd -> BackEnd;
// void BEDefineImportedObjsAndLibs (BEStringListP objs,BEStringListP libs);
BEInsertForeignExport :: !BESymbolP !Int !BackEnd -> BackEnd;
// void BEInsertForeignExport (BESymbolP symbol_p,int stdcall);
BESetMainDclModuleN :: !Int !BackEnd -> BackEnd;
// void BESetMainDclModuleN (int main_dcl_module_n_parameter);
BEStrictPositions :: !Int !BackEnd -> (!Int,!Int,!BackEnd);
// void BEStrictPositions (int functionIndex,int* bits,int** positions);
BECopyInts :: !Int !Int !Int -> Int;
// int BECopyInts (int cLength,int* ints,int* cleanArray);
BEDeclareDynamicTypeSymbol :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclareDynamicTypeSymbol (int typeIndex,int moduleIndex);
BEDynamicTempTypeSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDynamicTempTypeSymbol ();
kBEVersionCurrent:==0x02116000;
kBEVersionOldestDefinition:==0x02100401;
kBEVersionOldestImplementation:==0x02100401;
kBEDebug:==1;
kPredefinedModuleIndex:==1;
BENoAnnot:==0;
BEStrictAnnot:==1;
BENoUniAttr:==0;
BENotUniqueAttr:==1;
BEUniqueAttr:==2;
BEExistsAttr:==3;
BEUniqueVariable:==4;
BEFirstUniVarNumber:==5;
BEIntType:==0;
BEBoolType:==1;
BECharType:==2;
BERealType:==3;
BEFileType:==4;
BEStringType:==5;
BEWorldType:==6;
BEProcIdType:==7;
BERedIdType:==8;
BENrOfBasicTypes:==9;
BEIntDenot:==10;
BEBoolDenot:==11;
BECharDenot:==12;
BERealDenot:==13;
BENrOfBasicDenots:==14;
BEStringDenot:==15;
BEFunType:==16;
BEArrayType:==17;
BEStrictArrayType:==18;
BEUnboxedArrayType:==19;
BEListType:==20;
BETupleType:==21;
BEEmptyType:==22;
BEDynamicType:==23;
BENrOfPredefTypes:==24;
BETupleSymb:==25;
BEConsSymb:==26;
BENilSymb:==27;
BEApplySymb:==28;
BEIfSymb:==29;
BEFailSymb:==30;
BEAllSymb:==31;
BESelectSymb:==32;
BENrOfPredefFunsOrConses:==33;
BEDefinition:==34;
BENewSymbol:==35;
BEInstanceSymb:==36;
BEEmptySymbol:==37;
BEFieldSymbolList:==38;
BEErroneousSymb:==39;
BECreateArrayFun:==0;
BEArraySelectFun:==1;
BEUnqArraySelectFun:==2;
BEArrayUpdateFun:==3;
BEArrayReplaceFun:==4;
BEArraySizeFun:==5;
BEUnqArraySizeFun:==6;
BE_CreateArrayFun:==7;
BE_UnqArraySelectFun:==8;
BE_UnqArraySelectNextFun:==9;
BE_UnqArraySelectLastFun:==10;
BE_ArrayUpdateFun:==11;
BENoArrayFun:==12;
BESelectorDummy:==0;
BESelector:==1;
BESelector_U:==2;
BESelector_F:==3;
BESelector_L:==4;
BESelector_N:==5;
BESpecialIdentStdMisc:==0;
BESpecialIdentAbort:==1;
BESpecialIdentUndef:==2;
BESpecialIdentStdBool:==3;
BESpecialIdentAnd:==4;
BESpecialIdentOr:==5;
BESpecialIdentCount:==6;
BELhsNodeId:==0;
BERhsNodeId:==1;
BEIsNotACaf:==0;
BEIsACaf:==1;
