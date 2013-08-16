definition module Tonic.Util

from syntax import :: App, :: FunType
from StdArray import class Array
from Data.Maybe import :: Maybe
import Tonic.AbsSyn

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a

findInArr :: (e -> Bool) (a e) -> Maybe e | Array a e

concatStrings :: [String] -> .String

intercalateString :: String [String] -> String

dropAppContexts :: App ModuleEnv -> [Expression]

reifyFunType :: ModuleEnv Ident -> Maybe FunType

reifyFunDef :: ModuleEnv Ident -> Maybe GFunDef

reifySymbolType :: ModuleEnv Ident -> Maybe SymbolType

persistHasRec :: [SynExpression] SynExpression -> SynExpression

appIsCons :: App -> Bool

appIsNil :: App -> Bool

appIsList :: App -> Bool

exprIsListConstr :: Expression -> Bool

exprIsListCompr :: Expression -> Bool

withHead :: (a -> b) b [a] -> b

safeHead :: [a] -> Maybe a

withTwo :: (a a -> b) b [a] -> b

fromOptional :: a (Optional a) -> a

optional :: b (a -> b) (Optional a) -> b

//appFunName :: App -> String

freeVarName :: FreeVar -> String

dropContexts :: SymbolType [a] -> [a]

numContexts :: SymbolType -> Int

numFunArgs :: GFunDef -> Int

funIsTask :: FunDef -> Bool

symbIdentIsLam :: SymbIdent -> Bool

identIsLam :: Ident -> Bool

exprIsLam :: Expression -> Bool

symTyIsTask :: SymbolType -> Bool

identIsTask :: ModuleEnv Ident -> Bool

symbIdentIsTask :: ModuleEnv SymbIdent -> Bool

//isInfix :: ModuleEnv SymbIdent -> Bool
