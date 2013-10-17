definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from Tonic.AbsSyn import :: GinGraph, :: GEdge, :: GNode, :: ModuleEnv
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol

funToGraph :: PredefinedSymbol FunDef *ModuleEnv -> *(Maybe GinGraph, *ModuleEnv)

