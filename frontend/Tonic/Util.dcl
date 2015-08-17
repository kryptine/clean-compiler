definition module Tonic.Util

from syntax import :: App, :: FunType, :: ConsDef, :: Index, :: SymbKind, :: Type, :: TypeSymbIdent, :: TypeDefInfos, :: TypeDefInfo
from typesupport import :: FunctionType
from StdArray import class Array
from Data.Maybe import :: Maybe
from Data.Map import :: Map
import Tonic.AbsSyn
from iTasks._Framework.Tonic.AbsSyn import :: TPriority

dropAppContexts :: App *ChnExpression -> *(([Expression], [Expression]), *ChnExpression)

copyFunDefs :: !*{#FunDef} -> *(!*{#FunDef}, !*{#FunDef})

muselect :: !u:(a e) !Int -> *(Maybe e, !u:(a e)) | Array a e

reifyConsDef :: SymbIdent *ChnExpression -> *(Maybe ConsDef, *ChnExpression)

reifyFunType :: SymbIdent *ChnExpression -> *(Maybe FunType, *ChnExpression)

symbIdentModuleIdx :: SymbIdent -> Maybe Index

symbIdentObjectIdx :: SymbIdent -> Index

reifyFunDef :: SymbIdent *ChnExpression -> *(Maybe FunDef, *ChnExpression)

reifyFunDefsIdxPriority :: Index *ChnExpression -> *(Maybe Priority, *ChnExpression)

reifyDclModulesIdxPriority :: (Global Index) *ChnExpression -> *(Maybe Priority, *ChnExpression)

reifyDclModulesIdxPriority` :: Index Index *ChnExpression -> *(Maybe Priority, *ChnExpression)

reifySymbIdentPriority :: SymbIdent *ChnExpression -> *(Maybe Priority, *ChnExpression)

reifySymbIdentSymbolType :: SymbIdent *ChnExpression -> *(Maybe SymbolType, *ChnExpression)

reifyArgsAndDef :: SymbIdent *ChnExpression -> *(([FreeVar], FunDef), *ChnExpression)

reifyDclModule :: SymbIdent *ChnExpression -> *(Maybe DclModule, *ChnExpression)

isCons :: String -> Bool

isNil :: String -> Bool

appIsList :: App -> Bool

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

funIsBlueprintPart :: FunDef InhExpression *ChnExpression -> *(Bool, *ChnExpression)

typeIsBlueprintPart :: Type InhExpression *ChnExpression -> *(Bool, *ChnExpression)

funTy :: FunDef -> Type

funArgTys :: FunDef -> [Type]

identIsLambda :: Ident -> Bool

identIsListComprehension :: Ident -> Bool

exprIsLambda :: Expression -> Bool

symbIdentIsBPPart :: SymbIdent InhExpression *ChnExpression -> *(Bool, *ChnExpression)

isInfix :: SymbIdent *ChnExpression -> *(Bool, *ChnExpression)

prioIsInfix :: Priority -> Bool

symbIdentArity :: SymbIdent *ChnExpression -> *(Maybe Int, *ChnExpression)

getFunArgs :: FunDef -> [FreeVar]

getFunRhs :: FunDef -> Expression

updateWithAnnot :: Int Expression InhExpression *ChnExpression -> *ChnExpression

updateFun :: Index !*{#FunDef} (FunDef -> FunDef) -> *{#FunDef}

updateFunRhs :: Index !*{#FunDef} Expression -> *{#FunDef}

predefIsUndefined :: PredefinedSymbol -> Bool

argsRemaining :: App *ChnExpression -> *(Int, *ChnExpression)

isPartialApp :: App *ChnExpression -> *(Bool, *ChnExpression)

mkStr :: String -> Expression

mkInt :: Int -> Expression

mkBool :: Bool -> Expression

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

instance ToStatic (Expression, Expression, Expression)

instance FromStatic (Expression, Expression, Expression)

instance FromStatic String

listToListExpr :: [Expression] *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

freeVarToVar :: FreeVar *Heaps -> *(BoundVar, *Heaps)

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st

intersperse` :: String (a -> String) [a] -> String

stringContents :: String -> String

listExprToList :: Expression -> [Expression]

tupleToTupleExpr :: (Expression, Expression) *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

tupleExprToTuple :: Expression -> (Expression, Expression)

pdssAreDefined :: [Int] *PredefinedSymbols -> *(Bool, *PredefinedSymbols)

mselect :: (a e) !Int -> Maybe e | Array a e

typeHasClassInstance :: Type Int InhExpression *ChnExpression -> *(Bool, *ChnExpression)

fromPriority :: Priority -> TPriority

allVarsBound :: !InhExpression !(Map Int BoundVar) -> Bool

mkCaseDetFun :: !(Maybe (FreeVar, Index)) !ExprId !Int ![BoundVar] !Expression !InhExpression !*ChnExpression -> *(Expression, *ChnExpression)

wrapBody :: InhExpression SynExpression Bool *ChnExpression -> *(SynExpression, *ChnExpression)
