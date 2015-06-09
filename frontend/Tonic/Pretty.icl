implementation module Tonic.Pretty

from StdClass import class + (..)
from StdOverloaded import class < (..)
from StdInt import instance + Int, instance < Int
from StdList import ++, foldr, map
from StdOverloaded import class +++ (..), class % (..)
from StdString import instance +++ {#Char}, instance % {#Char}, instance toString Int
from StdFunc import o
from StdBool import ||, &&
import StdArray
import StdMisc
import Data.Void
import Data.Func
import Data.List

import Data.Graph
import Data.Maybe
import Text.PPrint
import Tonic.AbsSyn
import Tonic.Util
import iTasks._Framework.Tonic.AbsSyn

from general import ::Optional (Yes, No)
from syntax import
  :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let {..}, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..},
  :: SymbIdent {..}, :: SymbKind (..), :: VarContexts, :: TypeKind, :: FunctionInfoPtr, :: FunctionInfo, :: Priority (..), :: Assoc (..), :: VarInfoPtr, :: DynamicExpr,
  :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index, :: Bind,
  :: Position, :: AType {..}, :: Env, :: Ident {..}, :: SymbolPtr,
  :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..),
  :: FieldSymbol, :: IclModule, :: DclModule, :: FunDef, :: Optional,
  :: SymbolType {..}, :: LetBind, :: TypeVar {..}, :: StrictnessList (..),
  :: TypeContext {..}, :: AttributeVar {..}, :: AttrInequality {..},
  :: TypeVarInfoPtr {..}, :: AttrVarInfoPtr, :: Type (..), :: TCClass,
  :: TypeVarInfo, :: AttrVarInfo, :: FunType {..}, :: FunSpecials, :: TempVarId,
  :: ATypeVar, :: BasicType, :: ConsVariable, :: TypeAttribute, :: TypeSymbIdent {..},
  :: TypeSymbProperties, instance toString BasicType, :: ConsVariable (..),
  :: ParsedExpr (..), :: ArrayKind (..), :: DynamicType, :: Sequence (..), :: Qualifier {..},
  :: LocalDefs, :: FileName, :: LineAndColumn, :: Generator {..}, :: GeneratorKind (..),
  :: CaseAlt, :: ParsedSelection, :: ParsedSelectorKind, :: ElemAssignment, :: FieldAssignment,
  :: OptionalRecordName, :: BoundExpr, :: FieldNameOrQualifiedFieldName

ppDebugApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppDebugApp app menv
  # ((_, args), menv) = dropAppContexts app menv
  # (ads, menv)       = mapSt ppExpression args menv
  # sid               = ppSymbIdent app.app_symb
  = (text "<App>" <+> sid <+> brackets (hcat $ intersperse (text ", ") ads), menv)
  //let argsPP = hcat $ intersperse (text ", ") $ foldr (\x xs -> [ppExpression x menv:xs]) [] app.app_args

ppApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppApp app menv
  | isCons ident || isNil ident
      # ((_, args), menv) = dropAppContexts app menv
      # (d, menv)         = ppList args menv
      = (brackets d, menv)
  | otherwise
      # (ifx, menv) = isInfix app.app_symb menv
      | ifx         = ppInfix app menv
      | otherwise   = ppPrefix app menv
  where
  psi menv       = ppSymbIdent app.app_symb menv
  //args menv      = case args of
                     //[Selection _ _ _ : _]   -> (args, menv)
                     //_                       -> let ((_, xs), menv) = dropAppContexts app menv
                                                //in  (xs, menv)
  ident          = app.app_symb.symb_ident.id_name
  ppList []     menv = (empty, menv)
  ppList [x:xs] menv
    | isCons ident
        # (px, menv) = ppExpression x menv
        # (ld, menv) = ppList xs menv
        = (if (isnull xs) px (px <+> char ':' <+> ld), menv)
    | otherwise    = (empty, menv)

ppPrefix :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppPrefix app=:{App|app_symb} menv
  # ((_, args), menv) = dropAppContexts app menv
  # psi               = ppSymbIdent app_symb
  # (esd, menv)       = mapSt ppExpression args menv
  = (psi <+> hcat (intersperse (text " ") esd), menv)

//import StdDebug

ppInfix :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppInfix app=:{App|app_symb,app_args} menv
  # ((ctxs, args), menv) = dropAppContexts app menv
  = case args of
      [l:r:_]
        # (ld, menv)           = ppExpression l menv
        # psi                  = ppSymbIdent app_symb
        # (rd, menv)           = ppExpression r menv
        = (ld <+> psi <+> rd, menv)
      _ = (ppSymbIdent app_symb, menv)

ppSymbIdent :: SymbIdent -> Doc
ppSymbIdent si = ppIdent si.symb_ident

ppIdent :: Ident -> Doc
ppIdent ident = text ident.id_name

ppBoundVar :: BoundVar -> Doc
ppBoundVar bv = ppIdent bv.var_ident

ppDebugExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)
ppDebugExpression (Var bv)             menv
  # bvd = ppBoundVar bv
  = (text "<Var>" <+> bvd, menv)
ppDebugExpression (App app)            menv = ppDebugApp app menv
ppDebugExpression (Selection sk e ss)  menv
  # (ed, menv) = ppDebugExpression e menv
  # sd         = map ppSelection ss
  = (text "<Selection>" <+> ed <-> mkRecSel sd, menv)
ppDebugExpression (BasicExpr bv)       menv
  = (text "<BasicValue>" <+> ppBasicValue bv, menv)
ppDebugExpression _                    menv = (text "ppDebugExpression: _", menv) // empty

ppExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)
ppExpression (Var bv)             menv = (ppBoundVar bv, menv)
ppExpression (App app)            menv = ppApp app menv
// TODO Infix check
ppExpression (e @ [e1, e2])             menv
  # (ed, menv)  = ppExpression e menv
  # (e1d, menv) = ppExpression e1 menv
  # (e2d, menv) = ppExpression e2 menv
  = (e1d <+> ed <+> e2d, menv) // TODO: isTask etc
ppExpression (e @ es)             menv
  # (ed, menv)  = ppExpression e menv
  # (esd, menv) = mapSt ppExpression es menv
  = (ed <+> hcat esd, menv) // TODO: isTask etc
ppExpression (Selection sk e ss)  menv
  # (ed, menv) = ppExpression e menv
  # selsd      = map ppSelection ss
  = (ed <-> mkRecSel selsd, menv)
ppExpression (FreeVar fv)                 menv = (ppFreeVar fv, menv)
ppExpression (BasicExpr bv)               menv = (ppBasicValue bv, menv)
ppExpression (Let _)                      menv = (text "ppExpression: Let", menv) // empty
ppExpression (Case _)                     menv = (text "ppExpression: Case", menv) // empty
ppExpression (Update _ _ _)               menv = (text "ppExpression: Update", menv) // empty
ppExpression (RecordUpdate _ _ _)         menv = (text "ppExpression: RecordUpdate", menv) // empty
ppExpression (TupleSelect _ _ _)          menv = (text "ppExpression: TupleSelect", menv) // empty
ppExpression (Conditional _)              menv = (text "ppExpression: Conditional", menv) // empty
ppExpression (AnyCodeExpr _ _ _)          menv = (text "ppExpression: AnyCodeExpr", menv) // empty
ppExpression (ABCCodeExpr _ _)            menv = (text "ppExpression: ABCCodeExpr", menv) // empty
ppExpression (MatchExpr _ _)              menv = (text "ppExpression: MatchExpr", menv) // empty
ppExpression (IsConstructor _ _ _ _ _ _)  menv = (text "ppExpression: IsConstructor", menv) // empty
ppExpression (DictionariesFunction _ _ _) menv = (text "ppExpression: DictionariesFunction", menv) // empty
ppExpression (Constant _ _ _)             menv = (text "ppExpression: Constant", menv) // empty
ppExpression (ClassVariable _)            menv = (text "ppExpression: ClassVariable", menv) // empty
ppExpression (DynamicExpr _)              menv = (text "ppExpression: DynamicExpr", menv) // empty
ppExpression (TypeCodeExpression _)       menv = (text "ppExpression: TypeCodeExpression", menv) // empty
ppExpression (TypeSignature _ _)          menv = (text "ppExpression: TypeSignature", menv) // empty
ppExpression EE                           menv = (text "ppExpression: EE", menv) // empty
ppExpression (NoBind _)                   menv = (text "ppExpression: NoBind", menv) // empty
ppExpression (FailExpr _)                 menv = (text "ppExpression: FailExpr", menv) // empty
ppExpression _                            menv = (text "ppExpression: _", menv) // empty

mkRecSel :: [Doc] -> Doc
mkRecSel ds = char '.' <-> hcat (intersperse (char '.') ds)

ppFreeVar :: FreeVar -> Doc
ppFreeVar fv = ppIdent fv.fv_ident

ppBasicValue :: BasicValue -> Doc
ppBasicValue (BVI   str) = text str
ppBasicValue (BVInt i)   = int i
ppBasicValue (BVC   str) = text str
ppBasicValue (BVB   b)   = bool b
ppBasicValue (BVR   str) = text str
ppBasicValue (BVS   str) = text str

ppSelection :: Selection -> Doc
ppSelection (RecordSelection gds n)            = ppDefinedSymbol gds.glob_object
ppSelection (ArraySelection gds einf e)        = ppDefinedSymbol gds.glob_object // TODO use e
ppSelection (DictionarySelection bv ss einf e) = text" TODO: DictionarySelection"

ppDebugSelection :: Selection -> Doc
ppDebugSelection (RecordSelection gds n)            = ppDefinedSymbol gds.glob_object
ppDebugSelection (ArraySelection gds einf e)        = ppDefinedSymbol gds.glob_object // TODO use e
ppDebugSelection (DictionarySelection bv ss einf e) = text" TODO: DictionarySelection"

ppDefinedSymbol :: DefinedSymbol -> Doc
ppDefinedSymbol ds = ppIdent ds.ds_ident

ppCompact :: (Doc -> String)
ppCompact = display o renderCompact

ppType :: Type -> Doc
ppType (TA tsi ats)      = ppTypeSymbIdent tsi <-> if (length ats > 0) (text " " <-> hcat (intersperse (char ' ') (map ppAType ats))) (text "")
ppType (TAS tsi ats sl)  = ppTypeSymbIdent tsi <-> if (length ats > 0) (text " " <-> hcat (intersperse (char ' ') (map ppAType ats))) (text "")
ppType (at1 --> at2)     = ppAType at1 <-> text " -> " <-> ppAType at2
ppType (TArrow)          = text "TArrow"
ppType (TArrow1	at)      = text "TArrow1 " <-> ppAType at
ppType (cv :@: ats)      = ppConsVariable cv <-> text " :@: " <-> hcat (intersperse (char ' ') (map ppAType ats))
ppType (TB bt)           = text (toString bt)
ppType (TFA ats t)       = text "TFA "
ppType (GTV tv)          = text tv.tv_ident.id_name
ppType (TV tv)           = text tv.tv_ident.id_name
ppType (TFAC atvs t tcs) = text "TFAC"
ppType (TempV tvi)       = text "TempV"
ppType (TempQV tvi)      = text "TempQV"
ppType (TempQDV tvi)     = text "TempQDV"
ppType (TLifted tv)      = text "TLifted"
ppType (TQualifiedIdent i s ats) = text "TQualifiedIdent"
ppType (TGenericFunctionInDictionary gds tk gi) = text "TGenericFunctionInDictionary"
ppType (TLiftedSubst t)  = text "TLiftedSubst"
ppType TE                = text "TE"

ppConsVariable :: ConsVariable -> Doc
ppConsVariable (CV       tyvar  ) = ppTypeVar tyvar
ppConsVariable (TempCV   tempvar) = text (toString tempvar)
ppConsVariable (TempQCV  tempvar) = text (toString tempvar)
ppConsVariable (TempQCDV tempvar) = text (toString tempvar)

ppTypeVar :: TypeVar -> Doc
ppTypeVar tv = text tv.tv_ident.id_name

ppAType :: AType -> Doc
ppAType {at_type} = ppType at_type

ppTypeSymbIdent :: TypeSymbIdent -> Doc
ppTypeSymbIdent tsi = text (tsi.type_ident.id_name)

ppParsedExpr :: ParsedExpr -> Doc
ppParsedExpr (PE_List exprs) = text "[" <-> hcat (intersperse (text ", ") (map ppParsedExpr exprs)) <-> text "]"
ppParsedExpr (PE_Tuple args) = text "(" <-> hcat (intersperse (text ", ") (map ppParsedExpr args)) <-> text ")"
ppParsedExpr (PE_Basic basic_value) = ppBasicValue basic_value
//ppParsedExpr (PE_Selection selector_kind expr selectors) =  file <<< expr <<< selector_kind <<< selectors
//ppParsedExpr (PE_Update expr1 selections expr2) =  file <<< '{' <<< expr1  <<< " & " <<<  selections <<< " = " <<< expr2 <<< '}'
//ppParsedExpr (PE_Record PE_Empty _ fields) = file <<< '{' <<< fields <<< '}'
//ppParsedExpr (PE_Record rec _ fields) = file <<< '{' <<< rec <<< " & " <<< fields <<< '}'
ppParsedExpr (PE_ListCompr _ _ expr quals) = text "[" <-> ppParsedExpr expr <-> text " \\\\ " <-> hcat (intersperse (text ", ") (map ppQualifier quals)) <-> text "]"
ppParsedExpr (PE_ArrayCompr _ expr quals) = text "{" <-> ppParsedExpr expr <-> text " \\\\ " <-> hcat (intersperse (text ", ") (map ppQualifier quals)) <-> text "}"
ppParsedExpr (PE_Sequ seq)   = text "[" <-> ppSequence seq <-> text "]"
ppParsedExpr PE_Empty        = text "** E **"
ppParsedExpr (PE_Ident symb) = ppIdent symb
ppParsedExpr PE_WildCard     = char '_'
ppParsedExpr (PE_Lambda _ exprs expr _) = char '\\' <-> hcat (intersperse (text " ") (map ppParsedExpr exprs)) <-> text " -> " <-> ppParsedExpr expr
//ppParsedExpr (PE_Bound bind) = file <<< bind
//ppParsedExpr (PE_Case _ expr alts) = file <<< "case " <<< expr <<< " of\n" <<< alts
//ppParsedExpr (PE_Let defs expr) = file <<< "let " <<< defs <<< " in\n" <<< expr
//ppParsedExpr (PE_DynamicPattern expr type) = file <<< expr <<< "::" <<< type
//ppParsedExpr (PE_Dynamic expr maybetype)
  //= case maybetype of
    //Yes type
        //-> file <<< "dynamic " <<< expr <<< "::" <<< type
    //No
        //-> file <<< "dynamic " <<< expr
ppParsedExpr _ = text "some expression"

ppSequence :: Sequence -> Doc
ppSequence (SQ_FromThen _ e1 e2)      = ppParsedExpr e1 <-> char ',' <-> ppParsedExpr e2 <-> text ".."
ppSequence (SQ_FromThenTo _ e1 e2 e3) = ppParsedExpr e1 <-> char ',' <-> ppParsedExpr e2 <-> text ".." <-> ppParsedExpr e3
ppSequence (SQ_From _ e)              = ppParsedExpr e
ppSequence (SQ_FromTo _ e1 e2)        = ppParsedExpr e1 <-> text ".." <-> ppParsedExpr e2

ppQualifier :: Qualifier -> Doc
ppQualifier {qual_generators,qual_filter = Yes qual_filter} = hcat (intersperse (text " ") (map ppGenerator qual_generators)) <-> text "| " <-> ppParsedExpr qual_filter
ppQualifier {qual_generators,qual_filter = No}              = hcat (intersperse (text " ") (map ppGenerator qual_generators))

ppGenerator :: Generator -> Doc
ppGenerator {gen_kind,gen_pattern,gen_expr} = ppParsedExpr gen_pattern <-> text (gen_kind_to_string gen_kind) <-> ppParsedExpr gen_expr
  where
  gen_kind_to_string IsListGenerator = " <- "
  gen_kind_to_string IsOverloadedListGenerator = " <|- "
  gen_kind_to_string IsArrayGenerator = " <-: "

