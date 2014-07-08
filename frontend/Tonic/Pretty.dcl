definition module Tonic.Pretty

from Text.PPrint import :: Doc
from syntax import :: App, :: SymbIdent, :: Ident, :: BoundVar, :: Expression,
  :: FreeVar, :: BasicValue, :: DefinedSymbol, :: Selection, :: SymbIdent
from Tonic.AbsSyn import :: ModuleEnv
from iTasks.Framework.Tonic.AbsSyn import :: GinGraph, :: GLet,
  :: GinGraph, :: GNode, :: Graph, :: GEdge

ppDebugApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppApp :: App *ModuleEnv -> *(Doc, *ModuleEnv)

ppSymbIdent :: SymbIdent *ModuleEnv -> *(Doc, *ModuleEnv)

ppIdent :: Ident *ModuleEnv -> *(Doc, *ModuleEnv)

ppBoundVar :: BoundVar *ModuleEnv -> *(Doc, *ModuleEnv)

ppDebugExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

ppExpression :: Expression *ModuleEnv -> *(Doc, *ModuleEnv)

mkRecSel :: [Doc] -> Doc

ppFreeVar :: FreeVar *ModuleEnv -> *(Doc, *ModuleEnv)

ppBasicValue :: BasicValue *ModuleEnv -> *(Doc, *ModuleEnv)

ppSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)

ppDebugSelection :: Selection *ModuleEnv -> *(Doc, *ModuleEnv)

ppDefinedSymbol :: DefinedSymbol *ModuleEnv -> *(Doc, *ModuleEnv)

ppGLet :: GLet -> Doc

ppCompact :: (Doc -> String)

//mkTaskDot :: String GinGraph *ModuleEnv -> *(String, *ModuleEnv)

//mkDotAttrKV :: String String -> String

//mkDotArgs :: [String] -> String

//mkDotNodeLbl :: String Int -> String

//nodeToDot :: String GinGraph Int *ModuleEnv -> *(String, *ModuleEnv)

getNodeData` :: Int GinGraph -> GNode
