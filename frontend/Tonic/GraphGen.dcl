definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from checksupport import :: Heaps
from Tonic.AbsSyn import :: GinGraph, :: GEdge, :: GNode, :: ModuleEnv
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol

funToGraph :: PredefinedSymbol PredefinedSymbol FunDef *ModuleEnv *Heaps -> *(([String], Maybe GinGraph, Maybe Expression), *ModuleEnv, *Heaps)

