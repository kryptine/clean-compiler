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
import iTasks.Framework.Tonic.AbsSyn

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
  :: TypeSymbProperties, instance toString BasicType

ppDebugApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppDebugApp app menv
  # ((_, args), menv) = dropAppContexts app menv
  # (ads, menv)       = mapSt ppExpression args menv
  # (sid, menv)       = ppSymbIdent app.app_symb menv
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
  # (psi, menv)       = ppSymbIdent app_symb menv
  # (esd, menv)       = mapSt ppExpression args menv
  = (psi <+> hcat (intersperse (text " ") esd), menv)

//import StdDebug

ppInfix :: App *ModuleEnv -> *(Doc, *ModuleEnv)
ppInfix app=:{App|app_symb,app_args} menv
  # ((ctxs, args), menv) = dropAppContexts app menv
  = case args of
      [l:r:_]
        # (ld, menv)           = ppExpression l menv
        # (psi, menv)          = ppSymbIdent app_symb menv
        # (rd, menv)           = ppExpression r menv
        = (ld <+> psi <+> rd, menv)
      _ = ppSymbIdent app_symb menv

ppSymbIdent :: SymbIdent *ModuleEnv -> *(Doc, *ModuleEnv)
ppSymbIdent si menv = ppIdent si.symb_ident menv

ppIdent :: Ident *ModuleEnv -> *(Doc, *ModuleEnv)
ppIdent ident menv = (text ident.id_name, menv)

ppBoundVar :: BoundVar *ModuleEnv -> *(Doc, *ModuleEnv)
ppBoundVar bv menv = ppIdent bv.var_ident menv

ppDebugExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)
ppDebugExpression (Var bv)             menv
  # (bvd, menv) = ppBoundVar bv menv
  = (text "<Var>" <+> bvd, menv)
ppDebugExpression (App app)            menv = ppDebugApp app menv
ppDebugExpression (Selection sk e ss)  menv
  # (ed, menv) = ppDebugExpression e menv
  # (sd, menv) = mapSt ppSelection ss menv
  = (text "<Selection>" <+> ed <-> mkRecSel sd, menv)
ppDebugExpression (BasicExpr bv)       menv
  = (text "<BasicValue>" <+> ppBasicValue bv, menv)
ppDebugExpression _                    menv = (text "ppDebugExpression: _", menv) // empty

ppExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)
ppExpression (Var bv)             menv = ppBoundVar bv menv
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
  # (ed, menv)    = ppExpression e menv
  # (selsd, menv) = mapSt ppSelection ss menv
  = (ed <-> mkRecSel selsd, menv)
ppExpression (FreeVar fv)                 menv = ppFreeVar fv menv
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

ppFreeVar :: FreeVar *ModuleEnv -> *(Doc, *ModuleEnv)
ppFreeVar fv menv = ppIdent fv.fv_ident menv

ppBasicValue :: BasicValue -> Doc
ppBasicValue (BVI   str) = text str
ppBasicValue (BVInt i)   = int i
ppBasicValue (BVC   str) = text str
ppBasicValue (BVB   b)   = bool b
ppBasicValue (BVR   str) = text str
ppBasicValue (BVS   str) = text str

ppSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)
ppSelection (RecordSelection gds n)             menv = ppDefinedSymbol gds.glob_object menv
ppSelection (ArraySelection gds einf e)         menv = (text "TODO: ArraySelection", menv)
ppSelection (DictionarySelection bv ss einf e)  menv = (text" TODO: DictionarySelection", menv)

ppDebugSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)
ppDebugSelection (RecordSelection gds n)             menv = ppDefinedSymbol gds.glob_object menv
ppDebugSelection (ArraySelection gds einf e)         menv = (text "TODO: ArraySelection", menv)
ppDebugSelection (DictionarySelection bv ss einf e)  menv = (text" TODO: DictionarySelection", menv)

ppDefinedSymbol :: DefinedSymbol *ModuleEnv -> *(Doc, *ModuleEnv)
ppDefinedSymbol ds menv = ppIdent ds.ds_ident menv

ppCompact :: (Doc -> String)
ppCompact = display o renderCompact

ppType :: Type -> Doc
ppType (TA tsi ats)      = ppTypeSymbIdent tsi <-> if (length ats > 0) (text " " <-> hcat (intersperse (char ' ') (map ppAType ats))) (text "")
ppType (TAS tsi ats sl)  = ppTypeSymbIdent tsi <-> if (length ats > 0) (text " " <-> hcat (intersperse (char ' ') (map ppAType ats))) (text "")
ppType (at1 --> at2)     = ppAType at1 <-> text " --> " <-> ppAType at2
ppType (TArrow)          = text "->"
ppType (TArrow1	at)      = text "TArrow1"
ppType (cv :@: ats)      = text ":@:"
ppType (TB bt)           = text (toString bt)
ppType (TFA ats t)       = text "TFA"
ppType (GTV tv)          = text tv.tv_ident.id_name
ppType (TV tv)           = text tv.tv_ident.id_name
ppType (TFAC atvs t tcs) = text "TFAC"
ppType (TempV tvi)       = text "TempV"
ppType (TempQV tvi)      = text "TempQV"
ppType (TempQDV tvi)     = text "TempQDV"
ppType (TLifted tv)      = text "TypeVar"
ppType (TQualifiedIdent i s ats) = text "TQualifiedIdent"
ppType (TGenericFunctionInDictionary gds tk gi) = text "TGenericFunctionInDictionary"
ppType (TLiftedSubst t)  = text "TLiftedSubst"
ppType TE                = text "TE"

ppAType :: AType -> Doc
ppAType {at_type} = ppType at_type

ppTypeSymbIdent :: TypeSymbIdent -> Doc
ppTypeSymbIdent tsi = text (tsi.type_ident.id_name)
