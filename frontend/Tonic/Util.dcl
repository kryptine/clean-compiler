definition module Tonic.Util

from syntax import :: App, :: FunType, :: ConsDef, :: Index, :: SymbKind, :: Type, :: TypeSymbIdent, :: TypeDefInfos, :: TypeDefInfo
from typesupport import :: FunctionType
from StdArray import class Array
from Data.Maybe import :: Maybe
from Data.Map import :: Map
import Tonic.AbsSyn

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

reifyFunDefsIdxPriority :: Index *ModuleEnv -> *(Maybe Priority, *ModuleEnv)

reifyDclModulesIdxPriority :: (Global Index) *ModuleEnv -> *(Maybe Priority, *ModuleEnv)

reifyDclModulesIdxPriority` :: Index Index *ModuleEnv -> *(Maybe Priority, *ModuleEnv)

reifySymbIdentPriority :: SymbIdent *ModuleEnv -> *(Maybe Priority, *ModuleEnv)

reifySymbIdentSymbolType :: SymbIdent *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)

reifyArgsAndDef :: SymbIdent *ModuleEnv -> *(([FreeVar], FunDef), *ModuleEnv)

reifyDclModule :: SymbIdent *ModuleEnv -> *(Maybe DclModule, *ModuleEnv)

isCons :: String -> Bool

isNil :: String -> Bool

appIsList :: App -> Bool

exprIsListConstr :: Expression -> Bool

exprIsListCompr :: Expression -> Bool

appIsListComp :: App -> Bool

safeHead :: [a] -> Maybe a

fromOptional :: a (Optional a) -> a

optional :: b (a -> b) (Optional a) -> b

appFunName :: App -> String

typeToTCleanExpr :: Type -> TExpr
freeVarName :: FreeVar -> String

dropContexts :: SymbolType [a] -> ([a], [a])

numContexts :: SymbolType -> Int

funIsTopLevelBlueprint :: FunDef InhExpression *ChnExpression -> *(Bool, *ChnExpression)

funTy :: FunDef -> Type

functorContent :: Type -> Maybe Type

funArgTys :: FunDef -> [Type]

identIsLambda :: Ident -> Bool

identIsListComprehension :: Ident -> Bool

exprIsLambda :: Expression -> Bool

symTyIsTask :: SymbolType -> Bool

atypeIsTask :: AType -> Bool

typeIsTask :: Type -> Bool

atypeIsListOfTask :: AType -> Bool

typeIsListOfTask :: Type -> Bool

symbIdentIsTask :: SymbIdent *ChnExpression -> *(Bool, *ChnExpression)

isInfix :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)

prioIsInfix :: Priority -> Bool

fdArrToMap :: .{#FunDef} -> Map String FunDef

getFunArgs :: FunDef -> [FreeVar]

getFunRhs :: FunDef -> Expression

updateWithAnnot :: SymbIdent Expression *ModuleEnv -> *ModuleEnv

updateFunRhs :: Index !*{#FunDef} Expression -> *{#FunDef}

dispenseUnique :: *ChnExpression -> *(Int, *ChnExpression)

predefIsUndefined :: PredefinedSymbol -> Bool

argsRemaining :: App *ModuleEnv -> *(Int, *ModuleEnv)

isPartialApp :: App *ModuleEnv -> *(Bool, *ModuleEnv)

exprIsTask :: Expression *ChnExpression -> *(Bool, *ChnExpression)

mkStr :: String -> Expression

mkInt :: Int -> Expression

appPredefinedSymbolWithEI :: Int [Expression] ((Global Index) -> SymbKind) *Heaps *PredefinedSymbols -> *(App, *Heaps, *PredefinedSymbols)

appPredefinedSymbol :: Int [Expression] ((Global Index) -> SymbKind) *PredefinedSymbols -> *(App, *PredefinedSymbols)

mkPredefSymbIdent :: Ident PredefinedSymbol ((Global Index) -> SymbKind) -> SymbIdent

class ToStatic a where
  toStatic :: a *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

class FromStatic a where
  fromStatic :: Expression -> a

instance ToStatic [Expression]

instance FromStatic [Expression]

instance ToStatic (Expression, Expression)

instance FromStatic (Expression, Expression)

instance FromStatic String

freeVarToVar :: FreeVar *Heaps -> *(BoundVar, *Heaps)

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st

intersperse` :: String (a -> String) [a] -> String

stringContents :: String -> String

listExprToList :: Expression -> [Expression]

tupleToTupleExpr :: (Expression, Expression) *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

tupleExprToTuple :: Expression -> (Expression, Expression)

pdssAreDefined :: [Int] *PredefinedSymbols -> *(Bool, *PredefinedSymbols)

//exprToTCleanExpr :: Expression *ModuleEnv -> *(TCleanExpr, *ModuleEnv)

mselect :: (a e) !Int -> Maybe e | Array a e

typeHasClassInstance :: Type Int InhExpression *ChnExpression -> *(Bool, *ChnExpression)
