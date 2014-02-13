definition module Tonic.Util

from syntax import :: App, :: FunType, :: ConsDef, :: Index
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

muselect :: !u:(a e) !Int -> *(Maybe e, !u:(a e)) | Array a e

reifyConsDef :: SymbIdent *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)

reifyFunType :: SymbIdent *ModuleEnv -> *(Maybe FunType, *ModuleEnv)

symbIdentModuleIdx :: SymbIdent -> Maybe Index

symbIdentObjectIdx :: SymbIdent -> Maybe Index

reifyFunDef :: SymbIdent *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)

reifySymbIdentSymbolType :: SymbIdent *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)

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

symbIdentIsTask :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

isInfix :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

prioIsInfix :: Priority -> Bool

fdArrToMap :: .{#FunDef} -> Map String FunDef

getFunArgs :: FunDef -> [FreeVar]

getFunRhs :: FunDef -> Expression

updateWithAnnot :: SymbIdent (Maybe Expression) *ModuleEnv -> *ModuleEnv

updateFunRhs :: Index !*{#FunDef} Expression -> !*{#FunDef}

emptyEdge :: GEdge

mkEdge :: String -> GEdge

getLetBinds :: Let -> [LetBind]

mkGLetBinds :: Let *ModuleEnv -> *([(String, String)], *ModuleEnv)

predefIsUndefined :: PredefinedSymbol -> Bool

isPartialApp :: Expression *ModuleEnv -> *(Bool, *ModuleEnv)

mkStr :: String -> Expression

mkInt :: Int -> Expression

appPredefinedSymbol :: String PredefinedSymbol [Expression] -> App

returnsNonFun :: Expression *ModuleEnv -> *(Bool, *ModuleEnv)
