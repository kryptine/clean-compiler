implementation module backend;

//1.3
from StdString import String;
//3.1

:: *UWorld :== Int;
:: *BackEnd :== Int;
:: BESymbolP :== Int;
:: BETypeNodeP :== Int;
:: BETypeArgP :== Int;
:: BETypeAltP :== Int;
:: BENodeP :== Int;
:: BEArgP :== Int;
:: BERuleAltP :== Int;
:: BEImpRuleP :== Int;
:: BETypeP :== Int;
:: BEFlatTypeP :== Int;
:: BETypeVarP :== Int;
:: BETypeVarListP :== Int;
:: BEConstructorListP :== Int;
:: BEFieldListP :== Int;
:: BENodeIdP :== Int;
:: BENodeDefP :== Int;
:: BEStrictNodeIdP :== Int;
:: BECodeParameterP :== Int;
:: BECodeBlockP :== Int;
:: BEStringListP :== Int;
:: BEAnnotation :== Int;
:: BEAttribution :== Int;
:: BESymbKind :== Int;
:: BEArrayFunKind :== Int;
:: BESelectorKind :== Int;
:: BEUpdateKind :== Int;

BEGetVersion :: (!Int,!Int,!Int);
BEGetVersion  = code {
	ccall BEGetVersion ":VIII"
}
// void BEGetVersion (int* current,int* oldestDefinition,int* oldestImplementation);

BEInit :: !Int !UWorld -> (!BackEnd,!UWorld);
BEInit a0 a1 = code {
	ccall BEInit "I:I:I"
}
// BackEnd BEInit (int argc);

BEFree :: !BackEnd !UWorld -> UWorld;
BEFree a0 a1 = code {
	ccall BEFree "I:V:I"
}
// void BEFree (BackEnd backEnd);

BEArg :: !String !BackEnd -> BackEnd;
BEArg a0 a1 = code {
	ccall BEArg "S:V:I"
}
// void BEArg (CleanString arg);

BEDeclareModules :: !Int !BackEnd -> BackEnd;
BEDeclareModules a0 a1 = code {
	ccall BEDeclareModules "I:V:I"
}
// void BEDeclareModules (int nModules);

BESpecialArrayFunctionSymbol :: !BEArrayFunKind !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
BESpecialArrayFunctionSymbol a0 a1 a2 a3 = code {
	ccall BESpecialArrayFunctionSymbol "III:I:I"
}
// BESymbolP BESpecialArrayFunctionSymbol (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);

BEDictionarySelectFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
BEDictionarySelectFunSymbol a0 = code {
	ccall BEDictionarySelectFunSymbol ":I:I"
}
// BESymbolP BEDictionarySelectFunSymbol ();

BEDictionaryUpdateFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
BEDictionaryUpdateFunSymbol a0 = code {
	ccall BEDictionaryUpdateFunSymbol ":I:I"
}
// BESymbolP BEDictionaryUpdateFunSymbol ();

BEFunctionSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
BEFunctionSymbol a0 a1 a2 = code {
	ccall BEFunctionSymbol "II:I:I"
}
// BESymbolP BEFunctionSymbol (int functionIndex,int moduleIndex);

BEConstructorSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
BEConstructorSymbol a0 a1 a2 = code {
	ccall BEConstructorSymbol "II:I:I"
}
// BESymbolP BEConstructorSymbol (int constructorIndex,int moduleIndex);

BEFieldSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
BEFieldSymbol a0 a1 a2 = code {
	ccall BEFieldSymbol "II:I:I"
}
// BESymbolP BEFieldSymbol (int fieldIndex,int moduleIndex);

BETypeSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
BETypeSymbol a0 a1 a2 = code {
	ccall BETypeSymbol "II:I:I"
}
// BESymbolP BETypeSymbol (int typeIndex,int moduleIndex);

BEDontCareDefinitionSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
BEDontCareDefinitionSymbol a0 = code {
	ccall BEDontCareDefinitionSymbol ":I:I"
}
// BESymbolP BEDontCareDefinitionSymbol ();

BEBoolSymbol :: !Bool !BackEnd -> (!BESymbolP,!BackEnd);
BEBoolSymbol a0 a1 = code {
	ccall BEBoolSymbol "I:I:I"
}
// BESymbolP BEBoolSymbol (int value);

BELiteralSymbol :: !BESymbKind !String !BackEnd -> (!BESymbolP,!BackEnd);
BELiteralSymbol a0 a1 a2 = code {
	ccall BELiteralSymbol "IS:I:I"
}
// BESymbolP BELiteralSymbol (BESymbKind kind,CleanString value);

BEPredefineConstructorSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
BEPredefineConstructorSymbol a0 a1 a2 a3 a4 = code {
	ccall BEPredefineConstructorSymbol "IIII:V:I"
}
// void BEPredefineConstructorSymbol (int arity,int constructorIndex,int moduleIndex,BESymbKind symbolKind);

BEPredefineTypeSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
BEPredefineTypeSymbol a0 a1 a2 a3 a4 = code {
	ccall BEPredefineTypeSymbol "IIII:V:I"
}
// void BEPredefineTypeSymbol (int arity,int typeIndex,int moduleIndex,BESymbKind symbolKind);

BEBasicSymbol :: !Int !BackEnd -> (!BESymbolP,!BackEnd);
BEBasicSymbol a0 a1 = code {
	ccall BEBasicSymbol "I:I:I"
}
// BESymbolP BEBasicSymbol (BESymbKind kind);

BEVarTypeNode :: !String !BackEnd -> (!BETypeNodeP,!BackEnd);
BEVarTypeNode a0 a1 = code {
	ccall BEVarTypeNode "S:I:I"
}
// BETypeNodeP BEVarTypeNode (CleanString name);

BETypeVars :: !BETypeVarP !BETypeVarListP !BackEnd -> (!BETypeVarListP,!BackEnd);
BETypeVars a0 a1 a2 = code {
	ccall BETypeVars "II:I:I"
}
// BETypeVarListP BETypeVars (BETypeVarP typeVar,BETypeVarListP typeVarList);

BENoTypeVars :: !BackEnd -> (!BETypeVarListP,!BackEnd);
BENoTypeVars a0 = code {
	ccall BENoTypeVars ":I:I"
}
// BETypeVarListP BENoTypeVars ();

BENormalTypeNode :: !BESymbolP !BETypeArgP !BackEnd -> (!BETypeNodeP,!BackEnd);
BENormalTypeNode a0 a1 a2 = code {
	ccall BENormalTypeNode "II:I:I"
}
// BETypeNodeP BENormalTypeNode (BESymbolP symbol,BETypeArgP args);

BEAnnotateTypeNode :: !BEAnnotation !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
BEAnnotateTypeNode a0 a1 a2 = code {
	ccall BEAnnotateTypeNode "II:I:I"
}
// BETypeNodeP BEAnnotateTypeNode (BEAnnotation annotation,BETypeNodeP typeNode);

BEAttributeTypeNode :: !BEAttribution !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
BEAttributeTypeNode a0 a1 a2 = code {
	ccall BEAttributeTypeNode "II:I:I"
}
// BETypeNodeP BEAttributeTypeNode (BEAttribution attribution,BETypeNodeP typeNode);

BENoTypeArgs :: !BackEnd -> (!BETypeArgP,!BackEnd);
BENoTypeArgs a0 = code {
	ccall BENoTypeArgs ":I:I"
}
// BETypeArgP BENoTypeArgs ();

BETypeArgs :: !BETypeNodeP !BETypeArgP !BackEnd -> (!BETypeArgP,!BackEnd);
BETypeArgs a0 a1 a2 = code {
	ccall BETypeArgs "II:I:I"
}
// BETypeArgP BETypeArgs (BETypeNodeP node,BETypeArgP nextArgs);

BETypeAlt :: !BETypeNodeP !BETypeNodeP !BackEnd -> (!BETypeAltP,!BackEnd);
BETypeAlt a0 a1 a2 = code {
	ccall BETypeAlt "II:I:I"
}
// BETypeAltP BETypeAlt (BETypeNodeP lhs,BETypeNodeP rhs);

BENormalNode :: !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
BENormalNode a0 a1 a2 = code {
	ccall BENormalNode "II:I:I"
}
// BENodeP BENormalNode (BESymbolP symbol,BEArgP args);

BEMatchNode :: !Int !BESymbolP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
BEMatchNode a0 a1 a2 a3 = code {
	ccall BEMatchNode "III:I:I"
}
// BENodeP BEMatchNode (int arity,BESymbolP symbol,BENodeP node);

BETupleSelectNode :: !Int !Int !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
BETupleSelectNode a0 a1 a2 a3 = code {
	ccall BETupleSelectNode "III:I:I"
}
// BENodeP BETupleSelectNode (int arity,int index,BENodeP node);

BEIfNode :: !BENodeP !BENodeP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
BEIfNode a0 a1 a2 a3 = code {
	ccall BEIfNode "III:I:I"
}
// BENodeP BEIfNode (BENodeP cond,BENodeP then,BENodeP elsje);

BEGuardNode :: !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
BEGuardNode a0 a1 a2 a3 a4 a5 a6 a7 = code {
	ccall BEGuardNode "IIIIIII:I:I"
}
// BENodeP BEGuardNode (BENodeP cond,BENodeDefP thenNodeDefs,BEStrictNodeIdP thenStricts,BENodeP then,BENodeDefP elseNodeDefs,BEStrictNodeIdP elseStricts,BENodeP elsje);

BESelectorNode :: !BESelectorKind !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
BESelectorNode a0 a1 a2 a3 = code {
	ccall BESelectorNode "III:I:I"
}
// BENodeP BESelectorNode (BESelectorKind selectorKind,BESymbolP fieldSymbol,BEArgP args);

BEUpdateNode :: !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
BEUpdateNode a0 a1 = code {
	ccall BEUpdateNode "I:I:I"
}
// BENodeP BEUpdateNode (BEArgP args);

BENodeIdNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
BENodeIdNode a0 a1 a2 = code {
	ccall BENodeIdNode "II:I:I"
}
// BENodeP BENodeIdNode (BENodeIdP nodeId,BEArgP args);

BENoArgs :: !BackEnd -> (!BEArgP,!BackEnd);
BENoArgs a0 = code {
	ccall BENoArgs ":I:I"
}
// BEArgP BENoArgs ();

BEArgs :: !BENodeP !BEArgP !BackEnd -> (!BEArgP,!BackEnd);
BEArgs a0 a1 a2 = code {
	ccall BEArgs "II:I:I"
}
// BEArgP BEArgs (BENodeP node,BEArgP nextArgs);

BERuleAlt :: !Int !BENodeDefP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BERuleAltP,!BackEnd);
BERuleAlt a0 a1 a2 a3 a4 a5 a6 = code {
	ccall BERuleAlt "IIIIII:I:I"
}
// BERuleAltP BERuleAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BENodeDefP rhsDefs,BEStrictNodeIdP lhsStrictNodeIds,BENodeP rhs);

BERuleAlts :: !BERuleAltP !BERuleAltP !BackEnd -> (!BERuleAltP,!BackEnd);
BERuleAlts a0 a1 a2 = code {
	ccall BERuleAlts "II:I:I"
}
// BERuleAltP BERuleAlts (BERuleAltP alt,BERuleAltP alts);

BENoRuleAlts :: !BackEnd -> (!BERuleAltP,!BackEnd);
BENoRuleAlts a0 = code {
	ccall BENoRuleAlts ":I:I"
}
// BERuleAltP BENoRuleAlts ();

BEDeclareNodeId :: !Int !Int !String !BackEnd -> BackEnd;
BEDeclareNodeId a0 a1 a2 a3 = code {
	ccall BEDeclareNodeId "IIS:V:I"
}
// void BEDeclareNodeId (int sequenceNumber,int lhsOrRhs,CleanString name);

BENodeId :: !Int !BackEnd -> (!BENodeIdP,!BackEnd);
BENodeId a0 a1 = code {
	ccall BENodeId "I:I:I"
}
// BENodeIdP BENodeId (int sequenceNumber);

BEWildCardNodeId :: !BackEnd -> (!BENodeIdP,!BackEnd);
BEWildCardNodeId a0 = code {
	ccall BEWildCardNodeId ":I:I"
}
// BENodeIdP BEWildCardNodeId ();

BENodeDef :: !Int !BENodeP !BackEnd -> (!BENodeDefP,!BackEnd);
BENodeDef a0 a1 a2 = code {
	ccall BENodeDef "II:I:I"
}
// BENodeDefP BENodeDef (int sequenceNumber,BENodeP node);

BENoNodeDefs :: !BackEnd -> (!BENodeDefP,!BackEnd);
BENoNodeDefs a0 = code {
	ccall BENoNodeDefs ":I:I"
}
// BENodeDefP BENoNodeDefs ();

BENodeDefs :: !BENodeDefP !BENodeDefP !BackEnd -> (!BENodeDefP,!BackEnd);
BENodeDefs a0 a1 a2 = code {
	ccall BENodeDefs "II:I:I"
}
// BENodeDefP BENodeDefs (BENodeDefP nodeDef,BENodeDefP nodeDefs);

BEStrictNodeId :: !BENodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
BEStrictNodeId a0 a1 = code {
	ccall BEStrictNodeId "I:I:I"
}
// BEStrictNodeIdP BEStrictNodeId (BENodeIdP nodeId);

BENoStrictNodeIds :: !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
BENoStrictNodeIds a0 = code {
	ccall BENoStrictNodeIds ":I:I"
}
// BEStrictNodeIdP BENoStrictNodeIds ();

BEStrictNodeIds :: !BEStrictNodeIdP !BEStrictNodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
BEStrictNodeIds a0 a1 a2 = code {
	ccall BEStrictNodeIds "II:I:I"
}
// BEStrictNodeIdP BEStrictNodeIds (BEStrictNodeIdP strictNodeId,BEStrictNodeIdP strictNodeIds);

BERule :: !Int !Int !BETypeAltP !BERuleAltP !BackEnd -> (!BEImpRuleP,!BackEnd);
BERule a0 a1 a2 a3 a4 = code {
	ccall BERule "IIII:I:I"
}
// BEImpRuleP BERule (int functionIndex,int isCaf,BETypeAltP type,BERuleAltP alts);

BEDeclareRuleType :: !Int !Int !String !BackEnd -> BackEnd;
BEDeclareRuleType a0 a1 a2 a3 = code {
	ccall BEDeclareRuleType "IIS:V:I"
}
// void BEDeclareRuleType (int functionIndex,int moduleIndex,CleanString name);

BEDefineRuleType :: !Int !Int !BETypeAltP !BackEnd -> BackEnd;
BEDefineRuleType a0 a1 a2 a3 = code {
	ccall BEDefineRuleType "III:V:I"
}
// void BEDefineRuleType (int functionIndex,int moduleIndex,BETypeAltP typeAlt);

BEAdjustArrayFunction :: !BEArrayFunKind !Int !Int !BackEnd -> BackEnd;
BEAdjustArrayFunction a0 a1 a2 a3 = code {
	ccall BEAdjustArrayFunction "III:V:I"
}
// void BEAdjustArrayFunction (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);

BENoRules :: !BackEnd -> (!BEImpRuleP,!BackEnd);
BENoRules a0 = code {
	ccall BENoRules ":I:I"
}
// BEImpRuleP BENoRules ();

BERules :: !BEImpRuleP !BEImpRuleP !BackEnd -> (!BEImpRuleP,!BackEnd);
BERules a0 a1 a2 = code {
	ccall BERules "II:I:I"
}
// BEImpRuleP BERules (BEImpRuleP rule,BEImpRuleP rules);

BETypes :: !BETypeP !BETypeP !BackEnd -> (!BETypeP,!BackEnd);
BETypes a0 a1 a2 = code {
	ccall BETypes "II:I:I"
}
// BETypeP BETypes (BETypeP type,BETypeP types);

BENoTypes :: !BackEnd -> (!BETypeP,!BackEnd);
BENoTypes a0 = code {
	ccall BENoTypes ":I:I"
}
// BETypeP BENoTypes ();

BEFlatType :: !BESymbolP !BETypeVarListP !BackEnd -> (!BEFlatTypeP,!BackEnd);
BEFlatType a0 a1 a2 = code {
	ccall BEFlatType "II:I:I"
}
// BEFlatTypeP BEFlatType (BESymbolP symbol,BETypeVarListP arguments);

BEAlgebraicType :: !BEFlatTypeP !BEConstructorListP !BackEnd -> BackEnd;
BEAlgebraicType a0 a1 a2 = code {
	ccall BEAlgebraicType "II:V:I"
}
// void BEAlgebraicType (BEFlatTypeP lhs,BEConstructorListP constructors);

BERecordType :: !Int !BEFlatTypeP !BETypeNodeP !BEFieldListP !BackEnd -> BackEnd;
BERecordType a0 a1 a2 a3 a4 = code {
	ccall BERecordType "IIII:V:I"
}
// void BERecordType (int moduleIndex,BEFlatTypeP lhs,BETypeNodeP constructorType,BEFieldListP fields);

BEAbsType :: !BEFlatTypeP !BackEnd -> BackEnd;
BEAbsType a0 a1 = code {
	ccall BEAbsType "I:V:I"
}
// void BEAbsType (BEFlatTypeP lhs);

BEConstructors :: !BEConstructorListP !BEConstructorListP !BackEnd -> (!BEConstructorListP,!BackEnd);
BEConstructors a0 a1 a2 = code {
	ccall BEConstructors "II:I:I"
}
// BEConstructorListP BEConstructors (BEConstructorListP constructor,BEConstructorListP constructors);

BENoConstructors :: !BackEnd -> (!BEConstructorListP,!BackEnd);
BENoConstructors a0 = code {
	ccall BENoConstructors ":I:I"
}
// BEConstructorListP BENoConstructors ();

BEConstructor :: !BETypeNodeP !BackEnd -> (!BEConstructorListP,!BackEnd);
BEConstructor a0 a1 = code {
	ccall BEConstructor "I:I:I"
}
// BEConstructorListP BEConstructor (BETypeNodeP type);

BEDeclareField :: !Int !Int !String !BackEnd -> BackEnd;
BEDeclareField a0 a1 a2 a3 = code {
	ccall BEDeclareField "IIS:V:I"
}
// void BEDeclareField (int fieldIndex,int moduleIndex,CleanString name);

BEField :: !Int !Int !BETypeNodeP !BackEnd -> (!BEFieldListP,!BackEnd);
BEField a0 a1 a2 a3 = code {
	ccall BEField "III:I:I"
}
// BEFieldListP BEField (int fieldIndex,int moduleIndex,BETypeNodeP type);

BEFields :: !BEFieldListP !BEFieldListP !BackEnd -> (!BEFieldListP,!BackEnd);
BEFields a0 a1 a2 = code {
	ccall BEFields "II:I:I"
}
// BEFieldListP BEFields (BEFieldListP field,BEFieldListP fields);

BENoFields :: !BackEnd -> (!BEFieldListP,!BackEnd);
BENoFields a0 = code {
	ccall BENoFields ":I:I"
}
// BEFieldListP BENoFields ();

BEDeclareConstructor :: !Int !Int !String !BackEnd -> BackEnd;
BEDeclareConstructor a0 a1 a2 a3 = code {
	ccall BEDeclareConstructor "IIS:V:I"
}
// void BEDeclareConstructor (int constructorIndex,int moduleIndex,CleanString name);

BETypeVar :: !String !BackEnd -> (!BETypeVarP,!BackEnd);
BETypeVar a0 a1 = code {
	ccall BETypeVar "S:I:I"
}
// BETypeVarP BETypeVar (CleanString name);

BEDeclareType :: !Int !Int !String !BackEnd -> BackEnd;
BEDeclareType a0 a1 a2 a3 = code {
	ccall BEDeclareType "IIS:V:I"
}
// void BEDeclareType (int typeIndex,int moduleIndex,CleanString name);

BEDeclareFunction :: !String !Int !Int !Int !BackEnd -> BackEnd;
BEDeclareFunction a0 a1 a2 a3 a4 = code {
	ccall BEDeclareFunction "SIII:V:I"
}
// void BEDeclareFunction (CleanString name,int arity,int functionIndex,int ancestor);

BECodeAlt :: !Int !BENodeDefP !BENodeP !BECodeBlockP !BackEnd -> (!BERuleAltP,!BackEnd);
BECodeAlt a0 a1 a2 a3 a4 = code {
	ccall BECodeAlt "IIII:I:I"
}
// BERuleAltP BECodeAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BECodeBlockP codeBlock);

BEString :: !String !BackEnd -> (!BEStringListP,!BackEnd);
BEString a0 a1 = code {
	ccall BEString "S:I:I"
}
// BEStringListP BEString (CleanString cleanString);

BEStrings :: !BEStringListP !BEStringListP !BackEnd -> (!BEStringListP,!BackEnd);
BEStrings a0 a1 a2 = code {
	ccall BEStrings "II:I:I"
}
// BEStringListP BEStrings (BEStringListP string,BEStringListP strings);

BENoStrings :: !BackEnd -> (!BEStringListP,!BackEnd);
BENoStrings a0 = code {
	ccall BENoStrings ":I:I"
}
// BEStringListP BENoStrings ();

BECodeParameter :: !String !BENodeIdP !BackEnd -> (!BECodeParameterP,!BackEnd);
BECodeParameter a0 a1 a2 = code {
	ccall BECodeParameter "SI:I:I"
}
// BECodeParameterP BECodeParameter (CleanString location,BENodeIdP nodeId);

BECodeParameters :: !BECodeParameterP !BECodeParameterP !BackEnd -> (!BECodeParameterP,!BackEnd);
BECodeParameters a0 a1 a2 = code {
	ccall BECodeParameters "II:I:I"
}
// BECodeParameterP BECodeParameters (BECodeParameterP parameter,BECodeParameterP parameters);

BENoCodeParameters :: !BackEnd -> (!BECodeParameterP,!BackEnd);
BENoCodeParameters a0 = code {
	ccall BENoCodeParameters ":I:I"
}
// BECodeParameterP BENoCodeParameters ();

BEAbcCodeBlock :: !Bool !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
BEAbcCodeBlock a0 a1 a2 = code {
	ccall BEAbcCodeBlock "II:I:I"
}
// BECodeBlockP BEAbcCodeBlock (int inline,BEStringListP instructions);

BEAnyCodeBlock :: !BECodeParameterP !BECodeParameterP !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
BEAnyCodeBlock a0 a1 a2 a3 = code {
	ccall BEAnyCodeBlock "III:I:I"
}
// BECodeBlockP BEAnyCodeBlock (BECodeParameterP inParams,BECodeParameterP outParams,BEStringListP instructions);

BEDeclareIclModule :: !String !Int !Int !Int !Int !BackEnd -> BackEnd;
BEDeclareIclModule a0 a1 a2 a3 a4 a5 = code {
	ccall BEDeclareIclModule "SIIII:V:I"
}
// void BEDeclareIclModule (CleanString name,int nFunctions,int nTypes,int nConstructors,int nFields);

BEDeclareDclModule :: !Int !String !Bool !Int !Int !Int !Int !BackEnd -> BackEnd;
BEDeclareDclModule a0 a1 a2 a3 a4 a5 a6 a7 = code {
	ccall BEDeclareDclModule "ISIIIII:V:I"
}
// void BEDeclareDclModule (int moduleIndex,CleanString name,int systemModule,int nFunctions,int nTypes,int nConstructors,int nFields);

BEDeclarePredefinedModule :: !Int !Int !BackEnd -> BackEnd;
BEDeclarePredefinedModule a0 a1 a2 = code {
	ccall BEDeclarePredefinedModule "II:V:I"
}
// void BEDeclarePredefinedModule (int nTypes,int nConstructors);

BEDefineRules :: !BEImpRuleP !BackEnd -> BackEnd;
BEDefineRules a0 a1 = code {
	ccall BEDefineRules "I:V:I"
}
// void BEDefineRules (BEImpRuleP rules);

BEGenerateCode :: !String !BackEnd -> (!Bool,!BackEnd);
BEGenerateCode a0 a1 = code {
	ccall BEGenerateCode "S:I:I"
}
// int BEGenerateCode (CleanString outputFile);

BEExportType :: !Int !Int !BackEnd -> BackEnd;
BEExportType a0 a1 a2 = code {
	ccall BEExportType "II:V:I"
}
// void BEExportType (int dclTypeIndex,int iclTypeIndex);

BESwapTypes :: !Int !Int !BackEnd -> BackEnd;
BESwapTypes a0 a1 a2 = code {
	ccall BESwapTypes "II:V:I"
}
// void BESwapTypes (int frm,int to);

BEExportConstructor :: !Int !Int !BackEnd -> BackEnd;
BEExportConstructor a0 a1 a2 = code {
	ccall BEExportConstructor "II:V:I"
}
// void BEExportConstructor (int dclConstructorIndex,int iclConstructorIndex);

BEExportField :: !Int !Int !BackEnd -> BackEnd;
BEExportField a0 a1 a2 = code {
	ccall BEExportField "II:V:I"
}
// void BEExportField (int dclTypeIndex,int iclTypeIndex);

BEExportFunction :: !Int !Int !BackEnd -> BackEnd;
BEExportFunction a0 a1 a2 = code {
	ccall BEExportFunction "II:V:I"
}
// void BEExportFunction (int dclFunctionIndex,int iclFunctionIndex);

BEDefineImportedObjsAndLibs :: !BEStringListP !BEStringListP !BackEnd -> BackEnd;
BEDefineImportedObjsAndLibs a0 a1 a2 = code {
	ccall BEDefineImportedObjsAndLibs "II:V:I"
}
// void BEDefineImportedObjsAndLibs (BEStringListP objs,BEStringListP libs);

BESetMainDclModuleN :: !Int !BackEnd -> BackEnd;
BESetMainDclModuleN a0 a1 = code {
	ccall BESetMainDclModuleN "I:V:I"
}
// void BESetMainDclModuleN (int main_dcl_module_n_parameter);

BEDeclareDynamicTypeSymbol :: !Int !Int !BackEnd -> BackEnd;
BEDeclareDynamicTypeSymbol a0 a1 a2 = code {
	ccall BEDeclareDynamicTypeSymbol "II:V:I"
}
// void BEDeclareDynamicTypeSymbol (int typeIndex,int moduleIndex);

BEDynamicTempTypeSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
BEDynamicTempTypeSymbol a0 = code {
	ccall BEDynamicTempTypeSymbol ":I:I"
}
// BESymbolP BEDynamicTempTypeSymbol ();
kBEVersionCurrent:==0x02000206;
kBEVersionOldestDefinition:==0x02000204;
kBEVersionOldestImplementation:==0x02000206;
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
BEUpdateDummy:==0;
BEUpdate:==1;
BEUpdate_U:==2;
BELhsNodeId:==0;
BERhsNodeId:==1;
BEIsNotACaf:==0;
BEIsACaf:==1;
