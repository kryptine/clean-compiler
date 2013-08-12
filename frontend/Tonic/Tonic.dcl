definition module Tonic.Tonic
from Text.PPrint import :: Doc
import Tonic.AbsSyn

from syntax import :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..}, :: SymbIdent {..}, :: SymbKind, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index,
  :: Bind, :: Position, :: AType, :: Env, :: Ident {..}, :: SymbolPtr, :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..), :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind

:: Expressions :== [Expression]

mkPretty :: ModuleEnv -> (a -> String) | PPAG a

ppCompact :: (Doc -> String)

ppDebugExpression :: ModuleEnv Expression -> Doc

mkPPInh :: ModuleEnv -> Inh_Expression

mkTaskDot :: ModuleEnv String GGraph -> String

mkDotAttrKV :: String String -> String

mkDotArgs :: [String] -> String

mkDotNodeLbl :: String Int -> String

nodeToDot :: ModuleEnv String GinGraph Int -> String

getNodeData` :: Int GinGraph -> GNode

class PPAG a where
  ppAg :: ModuleEnv a -> Doc

instance PPAG Expression

instance PPAG Ident

instance PPAG BoundVar

instance PPAG FreeVar

instance PPAG SymbIdent

instance PPAG BasicValue

instance PPAG DefinedSymbol

instance PPAG Selection

instance PPAG GExpression

instance PPAG GLet

instance PPAG GLetBind

from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// Expression --------------------------------------------------
// wrapper
:: Inh_Expression  = Inh_Expression (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Expression :: Inh_Expression -> (ModuleEnv)
mergeId_Inh_Expression :: Inh_Expression -> (Int)
graph_Inh_Expression :: Inh_Expression -> (GinGraph)
currTaskName_Inh_Expression :: Inh_Expression -> (String)
caseExpr_Inh_Expression :: Inh_Expression -> (Maybe Expression)
:: Syn_Expression  = Syn_Expression (GinGraph) (Bool) (Maybe Int) (Doc) (Doc) (Bool)
recNode_Syn_Expression :: Syn_Expression -> (Bool)
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppAg_Syn_Expression :: Syn_Expression -> (Doc)
mNodeId_Syn_Expression :: Syn_Expression -> (Maybe Int)
hasRecs_Syn_Expression :: Syn_Expression -> (Bool)
graph_Syn_Expression :: Syn_Expression -> (GinGraph)
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )

// cata
sem_Expression :: Expression  -> T_Expression 

// semantic domain
:: T_Expression  = T_Expression (Identity (T_Expression_s2 ))
:: T_Expression_s2  = C_Expression_s2 (T_Expression_v1 )
:: T_Expression_s3  = C_Expression_s3
:: T_Expression_v1  :== (T_Expression_vIn1 ) -> (T_Expression_vOut1 )
:: T_Expression_vIn1  = T_Expression_vIn1 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Expression_vOut1  = T_Expression_vOut1 (GinGraph) (Bool) (Maybe Int) (Doc) (Doc) (Bool)
sem_Expression_Var  :: (BoundVar) -> T_Expression 
sem_Expression_App  :: (App) -> T_Expression 
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) ([Selection]) -> T_Expression 
sem_Expression_Update  :: (T_Expression ) ([Selection]) (T_Expression ) -> T_Expression 
sem_Expression_RecordUpdate  :: (Global DefinedSymbol) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_TupleSelect  :: (DefinedSymbol) (Int) (T_Expression ) -> T_Expression 
sem_Expression_BasicExpr  :: (BasicValue) -> T_Expression 
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_IsConstructor  :: (T_Expression ) (Global DefinedSymbol) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_FreeVar  :: (FreeVar) -> T_Expression 
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_Constant  :: (SymbIdent) (Int) (Priority) -> T_Expression 
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_EE  ::   T_Expression 
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_FailExpr  :: (Ident) -> T_Expression 

// Expressions -------------------------------------------------
// wrapper
:: Inh_Expressions  = Inh_Expressions (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Expressions :: Inh_Expressions -> (ModuleEnv)
mergeId_Inh_Expressions :: Inh_Expressions -> (Int)
graph_Inh_Expressions :: Inh_Expressions -> (GinGraph)
currTaskName_Inh_Expressions :: Inh_Expressions -> (String)
caseExpr_Inh_Expressions :: Inh_Expressions -> (Maybe Expression)
:: Syn_Expressions  = Syn_Expressions (GinGraph) (Bool) (Maybe Int) (Doc) (Doc) (Bool)
recNode_Syn_Expressions :: Syn_Expressions -> (Bool)
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
mNodeId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
hasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
graph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )

// cata
sem_Expressions :: Expressions  -> T_Expressions 

// semantic domain
:: T_Expressions  = T_Expressions (Identity (T_Expressions_s5 ))
:: T_Expressions_s5  = C_Expressions_s5 (T_Expressions_v4 )
:: T_Expressions_s6  = C_Expressions_s6
:: T_Expressions_v4  :== (T_Expressions_vIn4 ) -> (T_Expressions_vOut4 )
:: T_Expressions_vIn4  = T_Expressions_vIn4 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Expressions_vOut4  = T_Expressions_vOut4 (GinGraph) (Bool) (Maybe Int) (Doc) (Doc) (Bool)
sem_Expressions_Cons  :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Nil  ::   T_Expressions 
