definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule, :: ParsedExpr, :: CommonDefs, :: CommonDefsR, :: DclInstanceMemberTypeAndFunction
from general import :: Optional
from checksupport import :: Heaps
from Tonic.AbsSyn import :: InhExpression, :: ChnExpression, :: SynExpression
from iTasks._Framework.Tonic.AbsSyn import :: TExpr
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol, :: PredefinedSymbols
from overloading import :: InstanceTree

mkBlueprint :: !InhExpression !Expression !*ChnExpression -> *(!SynExpression, !*ChnExpression)
