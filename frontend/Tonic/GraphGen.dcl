definition module Tonic.GraphGen

from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from syntax import :: Expression, :: FunDef, :: IclModule, :: DclModule
from general import :: Optional
from checksupport import :: Heaps
from Tonic.AbsSyn import :: GinGraph, :: GEdge, :: GNode, :: ModuleEnv, :: TypeName, :: ModuleName, :: TaskName, :: VariableName
from Text.PPrint import :: Doc
from Data.Map import :: Map
from predef import :: PredefinedSymbol, :: PredefinedSymbols

funToGraph :: FunDef *ModuleEnv *Heaps *PredefinedSymbols -> *(([(VariableName, TypeName)], Maybe GinGraph, Maybe Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)

