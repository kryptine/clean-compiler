definition module Tonic.Util

from syntax import :: App, :: FunType, :: ConsDef, :: Index, :: SymbKind, :: Type, :: TypeSymbIdent
from typesupport import :: FunctionType
from StdArray import class Array
from Data.Maybe import :: Maybe
from Data.Map import :: Map
import Tonic.AbsSyn
from iTasks.Framework.Tonic.AbsSyn import :: PPOr

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a

findInArr :: (e -> Bool) (a e) -> Maybe (Int, e) | Array a e

concatStrings :: [String] -> .String

intercalateString :: String [String] -> String

dropAppContexts :: App *ModuleEnv -> *(([Expression], [Expression]), *ModuleEnv)

copyFunDefs :: !*{#FunDef} -> *(!*{#FunDef}, !*{#FunDef})

muselect :: !u:(a e) !Int -> *(Maybe e, !u:(a e)) | Array a e

reifyConsDef :: SymbIdent *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)

reifyFunType :: SymbIdent *ModuleEnv -> *(Maybe FunType, *ModuleEnv)

symbIdentModuleIdx :: SymbIdent -> Maybe Index

symbIdentObjectIdx :: SymbIdent -> Maybe Index

reifyFunDef :: SymbIdent *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)

reifySymbIdentSymbolType :: SymbIdent *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)

reifyArgsAndDef :: SymbIdent *ModuleEnv -> *(([FreeVar], FunDef), *ModuleEnv)

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

funTy :: FunDef -> Type

functorContent :: Type -> Maybe Type

funArgTys :: FunDef -> [Type]

identIsLambda :: Ident -> Bool

exprIsLambda :: Expression -> Bool

symTyIsTask :: SymbolType -> Bool

atypeIsTask :: AType -> Bool

typeIsTask :: Type -> Bool

atypeIsListOfTask :: AType -> Bool

typeIsListOfTask :: Type -> Bool

symbIdentIsTask :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

isInfix :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

prioIsInfix :: Priority -> Bool

fdArrToMap :: .{#FunDef} -> Map String FunDef

getFunArgs :: FunDef -> [FreeVar]

getFunRhs :: FunDef -> Expression

updateWithAnnot :: SymbIdent Expression *ModuleEnv -> *ModuleEnv

updateFunRhs :: Index !*{#FunDef} Expression -> !*{#FunDef}

addInhId :: InhExpression Int -> InhExpression

predefIsUndefined :: PredefinedSymbol -> Bool

argsRemaining :: App *ModuleEnv -> *(Int, *ModuleEnv)

isPartialApp :: App *ModuleEnv -> *(Bool, *ModuleEnv)

exprIsTask :: Expression *ModuleEnv -> *(Bool, *ModuleEnv)

mkStr :: String -> Expression

mkInt :: Int -> Expression

appPredefinedSymbol :: Int [Expression] ((Global Index) -> SymbKind) *PredefinedSymbols -> *(App, *PredefinedSymbols)

mkPredefSymbIdent :: Ident PredefinedSymbol ((Global Index) -> SymbKind) -> SymbIdent

class ToStatic a where
  toStatic :: a *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

class FromStatic a where
  fromStatic :: Expression -> a

instance ToStatic [Expression]

instance FromStatic [Expression]

instance ToStatic (Expression, Expression)

freeVarToVar :: FreeVar -> BoundVar

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st

intersperse` :: String (a -> String) [a] -> String
