definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from Tonic.AbsSyn import :: InhExpression, :: SynExpression, :: ExpressionAlg, :: GNode, :: GinGraph, :: GGraph, :: GEdge
from Text.PPrint import :: Doc

edgeErr :: InhExpression String (Maybe Int) Expression (Maybe Int) Expression -> a

connectId :: InhExpression SynExpression -> (Maybe Int, SynExpression)

mkGraphAlg :: InhExpression -> ExpressionAlg SynExpression

listExprToList :: Expression InhExpression -> [Expression]

nodeErr :: InhExpression (Maybe Int) Expression -> String

addEmptyEdge :: (Int, Int) GinGraph -> GinGraph

addNode` :: GNode GinGraph -> SynExpression

funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph

prettyAlg :: InhExpression -> ExpressionAlg Doc

getNodeData` :: Int GinGraph -> GNode

mkTaskDot :: InhExpression String GGraph -> String

mkDotAttrKV :: String String -> String

mkDotArgs :: [String] -> String

mkDotNodeLbl :: String Int -> String

nodeToDot :: InhExpression String GinGraph Int -> String

