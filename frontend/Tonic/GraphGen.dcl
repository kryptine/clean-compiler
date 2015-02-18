definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from checksupport import :: Heaps
from Tonic.AbsSyn import :: ModuleEnv, :: TypeName, :: ModuleName, :: TaskName, :: VariableName
from iTasks.Framework.Tonic.AbsSyn import :: TExpr, :: TCleanExpr
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol, :: PredefinedSymbols

funToGraph :: FunDef *ModuleEnv *Heaps *PredefinedSymbols -> *(Maybe ([(VariableName, TCleanExpr)], TExpr, Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)

