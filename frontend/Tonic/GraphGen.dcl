definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule, :: ParsedExpr, :: CommonDefs
from general import :: Optional
from checksupport import :: Heaps
from Tonic.AbsSyn import :: ModuleEnv, :: TypeName, :: ModuleName, :: TaskName, :: VariableName, :: InhExpression, :: ChnExpression
from iTasks._Framework.Tonic.AbsSyn import :: TExpr, :: TCleanExpr
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol, :: PredefinedSymbols
from overloading import :: InstanceTree

funToGraph :: FunDef FunDef [(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} InhExpression *ChnExpression
           -> *(Maybe ([(TCleanExpr, TCleanExpr)], TExpr, Expression), *ChnExpression)
