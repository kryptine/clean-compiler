definition module Tonic.Util

from syntax import :: App, :: FunType, :: ConsDef
from StdArray import class Array
from Data.Maybe import :: Maybe
from Data.Map import :: Map
import Tonic.AbsSyn

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a

findInArr :: (e -> Bool) (a e) -> Maybe (Int, e) | Array a e

concatStrings :: [String] -> .String

intercalateString :: String [String] -> String

dropAppContexts :: App *ModuleEnv -> *(([Expression], [Expression]), *ModuleEnv)

extractFunDefs :: !*{#FunDef} -> *(!{#FunDef}, !*{#FunDef})

reifyConsDef :: String *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)

reifyFunType :: String *ModuleEnv -> *(Maybe FunType, *ModuleEnv)

reifyFunDef :: String *ModuleEnv -> *(Maybe (Int, FunDef), *ModuleEnv)

reifySymbolType :: String *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)

isCons :: String -> Bool

isNil :: String -> Bool

appIsList :: App -> Bool

exprIsListConstr :: Expression -> Bool

exprIsListCompr :: Expression -> Bool

isListCompr :: String -> Bool

safeHead :: [a] -> Maybe a

fromOptional :: a (Optional a) -> a

optional :: b (a -> b) (Optional a) -> b

appFunName :: App -> String

freeVarName :: FreeVar -> String

dropContexts :: SymbolType [a] -> ([a], [a])

numContexts :: SymbolType -> Int

funIsTask :: FunDef -> Bool

identIsLambda :: Ident -> Bool

exprIsLambda :: Expression -> Bool

symTyIsTask :: SymbolType -> Bool

symbIdentIsTask :: ModuleN SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

isInfix :: String *ModuleEnv -> *(Bool, *ModuleEnv)

prioIsInfix :: Priority -> Bool

fdArrToMap :: .{#FunDef} -> Map String FunDef

getFunName :: FunDef -> String

getFunArgs :: FunDef -> [FreeVar]

getFunRhs :: FunDef -> Expression

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv

updateFunRhs :: Int !*{#FunDef} Expression -> !*{#FunDef}

emptyEdge :: GEdge

mkEdge :: String -> GEdge

getLetBinds :: Let -> [LetBind]

mkGLetBinds :: Let *ModuleEnv -> *([(String, String)], *ModuleEnv)
