definition module Tonic.Pretty

from Text.PPrint import :: Doc
import Tonic.AbsSyn
import syntax

class PP a where
  pp :: InhExpression a -> Doc

instance PP [a] | PP a

instance PP Expression

instance PP Ident

instance PP BoundVar

instance PP FreeVar

instance PP SymbIdent

instance PP BasicValue

instance PP DefinedSymbol

instance PP (Global a) | PP a

instance PP Selection

instance PP GExpression

instance PP GLet

instance PP GLetBind

mkPretty :: InhExpression -> (a -> String) | PP a
