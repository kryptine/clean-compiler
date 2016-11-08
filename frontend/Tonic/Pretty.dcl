definition module Tonic.Pretty

from Text.PPrint import :: Doc
from syntax import :: App, :: SymbIdent, :: Ident, :: BoundVar, :: Expression,
  :: FreeVar, :: BasicValue, :: DefinedSymbol, :: Selection, :: SymbIdent,
  :: Type, :: AType, :: TypeSymbIdent, :: ParsedExpr, :: TypeContext
from Tonic.AbsSyn import :: ChnExpression

ppDebugApp :: App *ChnExpression -> *(Doc, *ChnExpression)

ppApp :: App *ChnExpression -> *(Doc, *ChnExpression)

ppSymbIdent :: SymbIdent -> Doc

ppIdent :: Ident -> Doc

ppBoundVar :: BoundVar -> Doc

ppDebugExpression :: Expression *ChnExpression -> *(Doc, *ChnExpression)

ppExpression :: Expression *ChnExpression -> *(Doc, *ChnExpression)

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

ppTypeContext :: TypeContext *ChnExpression -> *(Doc, *ChnExpression)
