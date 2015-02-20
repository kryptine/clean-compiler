definition module Tonic.Pretty

from Text.PPrint import :: Doc
from syntax import :: App, :: SymbIdent, :: Ident, :: BoundVar, :: Expression,
  :: FreeVar, :: BasicValue, :: DefinedSymbol, :: Selection, :: SymbIdent,
  :: Type, :: AType, :: TypeSymbIdent
from Tonic.AbsSyn import :: ModuleEnv

ppDebugApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppSymbIdent :: SymbIdent *ModuleEnv -> *(Doc, *ModuleEnv)

ppIdent :: Ident *ModuleEnv -> *(Doc, *ModuleEnv)

ppBoundVar :: BoundVar *ModuleEnv -> *(Doc, *ModuleEnv)

ppDebugExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

ppExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

mkRecSel :: [Doc] -> Doc

ppFreeVar :: FreeVar *ModuleEnv -> *(Doc, *ModuleEnv)

ppBasicValue :: BasicValue -> Doc

ppSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)

ppDebugSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)

ppDefinedSymbol :: DefinedSymbol *ModuleEnv -> *(Doc, *ModuleEnv)

ppCompact :: (Doc -> String)

ppType :: Type -> Doc

ppAType :: AType -> Doc

ppTypeSymbIdent :: TypeSymbIdent -> Doc
