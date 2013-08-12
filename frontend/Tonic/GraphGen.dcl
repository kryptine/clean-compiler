definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from Tonic.AbsSyn import :: InhExpression, :: SynExpression, :: ExpressionAlg, :: GNode, :: GinGraph, :: GGraph, :: GEdge, :: ModuleEnv
from Text.PPrint import :: Doc

edgeErr :: ModuleEnv String (Maybe Int) Expression (Maybe Int) Expression -> a

connectId :: InhExpression SynExpression -> (Maybe Int, SynExpression)

mkGraphAlg :: InhExpression -> ExpressionAlg SynExpression

listExprToList :: Expression -> [Expression]

nodeErr :: ModuleEnv (Maybe Int) Expression -> String

addEmptyEdge :: (Int, Int) GinGraph -> GinGraph

addNode` :: GNode GinGraph -> SynExpression

funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph

