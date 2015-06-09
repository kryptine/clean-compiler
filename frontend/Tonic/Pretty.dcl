definition module Tonic.Pretty

from Text.PPrint import :: Doc
from syntax import :: App, :: SymbIdent, :: Ident, :: BoundVar, :: Expression,
  :: FreeVar, :: BasicValue, :: DefinedSymbol, :: Selection, :: SymbIdent,
  :: Type, :: AType, :: TypeSymbIdent, :: ParsedExpr
from Tonic.AbsSyn import :: ModuleEnv

ppDebugApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppSymbIdent :: SymbIdent -> Doc

ppIdent :: Ident -> Doc

ppBoundVar :: BoundVar -> Doc

ppDebugExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

ppExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

mkRecSel :: [Doc] -> Doc

ppFreeVar :: FreeVar -> Doc

ppBasicValue :: BasicValue -> Doc

ppSelection :: Selection -> Doc

ppDebugSelection :: Selection -> Doc

ppDefinedSymbol :: DefinedSymbol -> Doc

ppCompact :: (Doc -> String)

ppType :: Type -> Doc

ppAType :: AType -> Doc

ppTypeSymbIdent :: TypeSymbIdent -> Doc

ppParsedExpr :: ParsedExpr -> Doc
