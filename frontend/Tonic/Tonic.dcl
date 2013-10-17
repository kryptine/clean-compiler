definition module Tonic.Tonic
from Text.PPrint import :: Doc
import Tonic.AbsSyn

from syntax import :: FunType, :: Index, :: FunSpecials, :: SymbolPtr,
  :: Assoc, :: SymbKind, :: TypeVar, :: StrictnessList, :: TypeContext,
  :: AttributeVar, :: AttrInequality, :: SymbolTableEntry

:: Expressions :== [Expression]
:: GLetBinds :== [GLetBind]
:: Selections :== [Selection]
:: GlobalDefinedSymbol :== Global DefinedSymbol
:: FreeVars :== [FreeVar]
:: MaybeExpression :== Maybe Expression

ppCompact :: (Doc -> String)

ppExpression :: ModuleEnv Expression -> Doc

ppDebugExpression :: ModuleEnv Expression -> Doc

ppFreeVar :: ModuleEnv FreeVar -> Doc

mkPPInhExpression :: ModuleEnv -> Inh_Expression

mkPPInhFreeVar :: ModuleEnv -> Inh_FreeVar

mkTaskDot :: ModuleEnv String GGraph -> String

mkDotAttrKV :: String String -> String

mkDotArgs :: [String] -> String

mkDotNodeLbl :: String Int -> String

nodeToDot :: ModuleEnv String GinGraph Int -> String

getNodeData` :: Int GinGraph -> GNode

funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph

from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// App ---------------------------------------------------------
// wrapper
:: Inh_App  = Inh_App (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_App :: Inh_App -> (ModuleEnv)
mergeId_Inh_App :: Inh_App -> (Int)
graph_Inh_App :: Inh_App -> (GinGraph)
currTaskName_Inh_App :: Inh_App -> (String)
caseExpr_Inh_App :: Inh_App -> (Maybe Expression)
:: Syn_App  = Syn_App (App) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool)
secondArgRecNode_Syn_App :: Syn_App -> (Bool)
secondArgMExitId_Syn_App :: Syn_App -> (Maybe Int)
secondArgMEntryId_Syn_App :: Syn_App -> (Maybe Int)
secondArgIdent_Syn_App :: Syn_App -> (String)
secondArgHasRecs_Syn_App :: Syn_App -> (Bool)
secondArgGraph_Syn_App :: Syn_App -> (GinGraph)
secondArg_Syn_App :: Syn_App -> (MaybeExpression)
recNode_Syn_App :: Syn_App -> (Bool)
ppDebugs_Syn_App :: Syn_App -> ([Doc])
ppDebug_Syn_App :: Syn_App -> (Doc)
ppAgs_Syn_App :: Syn_App -> ([Doc])
ppAg_Syn_App :: Syn_App -> (Doc)
mExitId_Syn_App :: Syn_App -> (Maybe Int)
mEntryId_Syn_App :: Syn_App -> (Maybe Int)
hasRecs_Syn_App :: Syn_App -> (Bool)
graph_Syn_App :: Syn_App -> (GinGraph)
firstArgRecNode_Syn_App :: Syn_App -> (Bool)
firstArgMExitId_Syn_App :: Syn_App -> (Maybe Int)
firstArgMEntryId_Syn_App :: Syn_App -> (Maybe Int)
firstArgIdent_Syn_App :: Syn_App -> (String)
firstArgHasRecs_Syn_App :: Syn_App -> (Bool)
firstArgGraph_Syn_App :: Syn_App -> (GinGraph)
firstArg_Syn_App :: Syn_App -> (MaybeExpression)
copy_Syn_App :: Syn_App -> (App)
wrap_App :: T_App  Inh_App  -> (Syn_App )

// cata
sem_App :: App  -> T_App 

// semantic domain
:: T_App  = T_App (Identity (T_App_s2 ))
:: T_App_s2  = C_App_s2 (T_App_v1 )
:: T_App_s3  = C_App_s3
:: T_App_v1  :== (T_App_vIn1 ) -> (T_App_vOut1 )
:: T_App_vIn1  = T_App_vIn1 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_App_vOut1  = T_App_vOut1 (App) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool)
sem_App_App  :: (T_SymbIdent ) (T_Expressions ) (ExprInfoPtr)  -> T_App 

// BasicValue --------------------------------------------------
// wrapper
:: Inh_BasicValue  = Inh_BasicValue (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_BasicValue :: Inh_BasicValue -> (ModuleEnv)
mergeId_Inh_BasicValue :: Inh_BasicValue -> (Int)
graph_Inh_BasicValue :: Inh_BasicValue -> (GinGraph)
currTaskName_Inh_BasicValue :: Inh_BasicValue -> (String)
caseExpr_Inh_BasicValue :: Inh_BasicValue -> (Maybe Expression)
:: Syn_BasicValue  = Syn_BasicValue (BasicValue) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_BasicValue :: Syn_BasicValue -> (Bool)
ppDebugs_Syn_BasicValue :: Syn_BasicValue -> ([Doc])
ppDebug_Syn_BasicValue :: Syn_BasicValue -> (Doc)
ppAgs_Syn_BasicValue :: Syn_BasicValue -> ([Doc])
ppAg_Syn_BasicValue :: Syn_BasicValue -> (Doc)
mExitId_Syn_BasicValue :: Syn_BasicValue -> (Maybe Int)
mEntryId_Syn_BasicValue :: Syn_BasicValue -> (Maybe Int)
hasRecs_Syn_BasicValue :: Syn_BasicValue -> (Bool)
graph_Syn_BasicValue :: Syn_BasicValue -> (GinGraph)
copy_Syn_BasicValue :: Syn_BasicValue -> (BasicValue)
wrap_BasicValue :: T_BasicValue  Inh_BasicValue  -> (Syn_BasicValue )

// cata
sem_BasicValue :: BasicValue  -> T_BasicValue 

// semantic domain
:: T_BasicValue  = T_BasicValue (Identity (T_BasicValue_s5 ))
:: T_BasicValue_s5  = C_BasicValue_s5 (T_BasicValue_v4 )
:: T_BasicValue_s6  = C_BasicValue_s6
:: T_BasicValue_v4  :== (T_BasicValue_vIn4 ) -> (T_BasicValue_vOut4 )
:: T_BasicValue_vIn4  = T_BasicValue_vIn4 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_BasicValue_vOut4  = T_BasicValue_vOut4 (BasicValue) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_BasicValue_BVI  :: (String) -> T_BasicValue 
sem_BasicValue_BVInt  :: (Int) -> T_BasicValue 
sem_BasicValue_BVC  :: (String) -> T_BasicValue 
sem_BasicValue_BVB  :: (Bool) -> T_BasicValue 
sem_BasicValue_BVR  :: (String) -> T_BasicValue 
sem_BasicValue_BVS  :: (String) -> T_BasicValue 

// BoundVar ----------------------------------------------------
// wrapper
:: Inh_BoundVar  = Inh_BoundVar (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_BoundVar :: Inh_BoundVar -> (ModuleEnv)
mergeId_Inh_BoundVar :: Inh_BoundVar -> (Int)
graph_Inh_BoundVar :: Inh_BoundVar -> (GinGraph)
currTaskName_Inh_BoundVar :: Inh_BoundVar -> (String)
caseExpr_Inh_BoundVar :: Inh_BoundVar -> (Maybe Expression)
:: Syn_BoundVar  = Syn_BoundVar (BoundVar) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_BoundVar :: Syn_BoundVar -> (Bool)
ppDebugs_Syn_BoundVar :: Syn_BoundVar -> ([Doc])
ppDebug_Syn_BoundVar :: Syn_BoundVar -> (Doc)
ppAgs_Syn_BoundVar :: Syn_BoundVar -> ([Doc])
ppAg_Syn_BoundVar :: Syn_BoundVar -> (Doc)
mExitId_Syn_BoundVar :: Syn_BoundVar -> (Maybe Int)
mEntryId_Syn_BoundVar :: Syn_BoundVar -> (Maybe Int)
hasRecs_Syn_BoundVar :: Syn_BoundVar -> (Bool)
graph_Syn_BoundVar :: Syn_BoundVar -> (GinGraph)
copy_Syn_BoundVar :: Syn_BoundVar -> (BoundVar)
wrap_BoundVar :: T_BoundVar  Inh_BoundVar  -> (Syn_BoundVar )

// cata
sem_BoundVar :: BoundVar  -> T_BoundVar 

// semantic domain
:: T_BoundVar  = T_BoundVar (Identity (T_BoundVar_s8 ))
:: T_BoundVar_s8  = C_BoundVar_s8 (T_BoundVar_v7 )
:: T_BoundVar_s9  = C_BoundVar_s9
:: T_BoundVar_v7  :== (T_BoundVar_vIn7 ) -> (T_BoundVar_vOut7 )
:: T_BoundVar_vIn7  = T_BoundVar_vIn7 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_BoundVar_vOut7  = T_BoundVar_vOut7 (BoundVar) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_BoundVar_BoundVar  :: (T_Ident ) (VarInfoPtr) (ExprInfoPtr) -> T_BoundVar 

// DefinedSymbol -----------------------------------------------
// wrapper
:: Inh_DefinedSymbol  = Inh_DefinedSymbol (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (ModuleEnv)
mergeId_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (Int)
graph_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (GinGraph)
currTaskName_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (String)
caseExpr_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (Maybe Expression)
:: Syn_DefinedSymbol  = Syn_DefinedSymbol (DefinedSymbol) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Bool)
ppDebugs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> ([Doc])
ppDebug_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Doc)
ppAgs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> ([Doc])
ppAg_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Doc)
mExitId_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Maybe Int)
mEntryId_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Maybe Int)
hasRecs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Bool)
graph_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (GinGraph)
copy_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (DefinedSymbol)
wrap_DefinedSymbol :: T_DefinedSymbol  Inh_DefinedSymbol  -> (Syn_DefinedSymbol )

// cata
sem_DefinedSymbol :: DefinedSymbol  -> T_DefinedSymbol 

// semantic domain
:: T_DefinedSymbol  = T_DefinedSymbol (Identity (T_DefinedSymbol_s11 ))
:: T_DefinedSymbol_s11  = C_DefinedSymbol_s11 (T_DefinedSymbol_v10 )
:: T_DefinedSymbol_s12  = C_DefinedSymbol_s12
:: T_DefinedSymbol_v10  :== (T_DefinedSymbol_vIn10 ) -> (T_DefinedSymbol_vOut10 )
:: T_DefinedSymbol_vIn10  = T_DefinedSymbol_vIn10 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_DefinedSymbol_vOut10  = T_DefinedSymbol_vOut10 (DefinedSymbol) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_DefinedSymbol_DefinedSymbol  :: (T_Ident ) (Int) (Index) -> T_DefinedSymbol 

// Expression --------------------------------------------------
// wrapper
:: Inh_Expression  = Inh_Expression (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Expression :: Inh_Expression -> (ModuleEnv)
mergeId_Inh_Expression :: Inh_Expression -> (Int)
graph_Inh_Expression :: Inh_Expression -> (GinGraph)
currTaskName_Inh_Expression :: Inh_Expression -> (String)
caseExpr_Inh_Expression :: Inh_Expression -> (Maybe Expression)
:: Syn_Expression  = Syn_Expression (Expression) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_Expression :: Syn_Expression -> (Bool)
ppDebugs_Syn_Expression :: Syn_Expression -> ([Doc])
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppAgs_Syn_Expression :: Syn_Expression -> ([Doc])
ppAg_Syn_Expression :: Syn_Expression -> (Doc)
mExitId_Syn_Expression :: Syn_Expression -> (Maybe Int)
mEntryId_Syn_Expression :: Syn_Expression -> (Maybe Int)
hasRecs_Syn_Expression :: Syn_Expression -> (Bool)
graph_Syn_Expression :: Syn_Expression -> (GinGraph)
copy_Syn_Expression :: Syn_Expression -> (Expression)
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )

// cata
sem_Expression :: Expression  -> T_Expression 

// semantic domain
:: T_Expression  = T_Expression (Identity (T_Expression_s14 ))
:: T_Expression_s14  = C_Expression_s14 (T_Expression_v13 )
:: T_Expression_s15  = C_Expression_s15
:: T_Expression_v13  :== (T_Expression_vIn13 ) -> (T_Expression_vOut13 )
:: T_Expression_vIn13  = T_Expression_vIn13 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Expression_vOut13  = T_Expression_vOut13 (Expression) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_Expression_Var  :: (T_BoundVar ) -> T_Expression 
sem_Expression_App  :: (T_App ) -> T_Expression 
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) (T_Selections ) -> T_Expression 
sem_Expression_Update  :: (T_Expression ) (T_Selections ) (T_Expression ) -> T_Expression 
sem_Expression_RecordUpdate  :: (T_GlobalDefinedSymbol ) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_TupleSelect  :: (T_DefinedSymbol ) (Int) (T_Expression ) -> T_Expression 
sem_Expression_BasicExpr  :: (T_BasicValue ) -> T_Expression 
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_IsConstructor  :: (T_Expression ) (T_GlobalDefinedSymbol ) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_FreeVar  :: (T_FreeVar ) -> T_Expression 
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_Constant  :: (T_SymbIdent ) (Int) (Priority) -> T_Expression 
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_EE  ::   T_Expression 
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_FailExpr  :: (T_Ident ) -> T_Expression 

// Expressions -------------------------------------------------
// wrapper
:: Inh_Expressions  = Inh_Expressions (Doc) (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv) (Int)
numContexts_Inh_Expressions :: Inh_Expressions -> (Int)
moduleEnv_Inh_Expressions :: Inh_Expressions -> (ModuleEnv)
mergeId_Inh_Expressions :: Inh_Expressions -> (Int)
graph_Inh_Expressions :: Inh_Expressions -> (GinGraph)
currTaskName_Inh_Expressions :: Inh_Expressions -> (String)
caseExpr_Inh_Expressions :: Inh_Expressions -> (Maybe Expression)
appSymbDoc_Inh_Expressions :: Inh_Expressions -> (Doc)
:: Syn_Expressions  = Syn_Expressions (Expressions) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Doc) (Doc) ([Doc]) (Bool) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool)
secondArgRecNode_Syn_Expressions :: Syn_Expressions -> (Bool)
secondArgMExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
secondArgMEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
secondArgIdent_Syn_Expressions :: Syn_Expressions -> (String)
secondArgHasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
secondArgGraph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
secondArg_Syn_Expressions :: Syn_Expressions -> (MaybeExpression)
recNode_Syn_Expressions :: Syn_Expressions -> (Bool)
ppTail_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppPrefix_Syn_Expressions :: Syn_Expressions -> (Doc)
ppInfix_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebugs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAgs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
mExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
hasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
graph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
firstArgRecNode_Syn_Expressions :: Syn_Expressions -> (Bool)
firstArgMExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
firstArgMEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
firstArgIdent_Syn_Expressions :: Syn_Expressions -> (String)
firstArgHasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
firstArgGraph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
firstArg_Syn_Expressions :: Syn_Expressions -> (MaybeExpression)
copy_Syn_Expressions :: Syn_Expressions -> (Expressions)
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )

// cata
sem_Expressions :: Expressions  -> T_Expressions 

// semantic domain
:: T_Expressions  = T_Expressions (Identity (T_Expressions_s17 ))
:: T_Expressions_s17  = C_Expressions_s17 (T_Expressions_v16 )
:: T_Expressions_s18  = C_Expressions_s18
:: T_Expressions_v16  :== (T_Expressions_vIn16 ) -> (T_Expressions_vOut16 )
:: T_Expressions_vIn16  = T_Expressions_vIn16 (Doc) (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv) (Int)
:: T_Expressions_vOut16  = T_Expressions_vOut16 (Expressions) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Doc) (Doc) ([Doc]) (Bool) (MaybeExpression) (GinGraph) (Bool) (String) (Maybe Int) (Maybe Int) (Bool)
sem_Expressions_Cons  :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Nil  ::   T_Expressions 

// FreeVar -----------------------------------------------------
// wrapper
:: Inh_FreeVar  = Inh_FreeVar (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_FreeVar :: Inh_FreeVar -> (ModuleEnv)
mergeId_Inh_FreeVar :: Inh_FreeVar -> (Int)
graph_Inh_FreeVar :: Inh_FreeVar -> (GinGraph)
currTaskName_Inh_FreeVar :: Inh_FreeVar -> (String)
caseExpr_Inh_FreeVar :: Inh_FreeVar -> (Maybe Expression)
:: Syn_FreeVar  = Syn_FreeVar (FreeVar) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_FreeVar :: Syn_FreeVar -> (Bool)
ppDebugs_Syn_FreeVar :: Syn_FreeVar -> ([Doc])
ppDebug_Syn_FreeVar :: Syn_FreeVar -> (Doc)
ppAgs_Syn_FreeVar :: Syn_FreeVar -> ([Doc])
ppAg_Syn_FreeVar :: Syn_FreeVar -> (Doc)
mExitId_Syn_FreeVar :: Syn_FreeVar -> (Maybe Int)
mEntryId_Syn_FreeVar :: Syn_FreeVar -> (Maybe Int)
hasRecs_Syn_FreeVar :: Syn_FreeVar -> (Bool)
graph_Syn_FreeVar :: Syn_FreeVar -> (GinGraph)
copy_Syn_FreeVar :: Syn_FreeVar -> (FreeVar)
wrap_FreeVar :: T_FreeVar  Inh_FreeVar  -> (Syn_FreeVar )

// cata
sem_FreeVar :: FreeVar  -> T_FreeVar 

// semantic domain
:: T_FreeVar  = T_FreeVar (Identity (T_FreeVar_s20 ))
:: T_FreeVar_s20  = C_FreeVar_s20 (T_FreeVar_v19 )
:: T_FreeVar_s21  = C_FreeVar_s21
:: T_FreeVar_v19  :== (T_FreeVar_vIn19 ) -> (T_FreeVar_vOut19 )
:: T_FreeVar_vIn19  = T_FreeVar_vIn19 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_FreeVar_vOut19  = T_FreeVar_vOut19 (FreeVar) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_FreeVar_FreeVar  :: (Level) (T_Ident ) (VarInfoPtr) (Int) -> T_FreeVar 

// FreeVars ----------------------------------------------------
// wrapper
:: Inh_FreeVars  = Inh_FreeVars (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_FreeVars :: Inh_FreeVars -> (ModuleEnv)
mergeId_Inh_FreeVars :: Inh_FreeVars -> (Int)
graph_Inh_FreeVars :: Inh_FreeVars -> (GinGraph)
currTaskName_Inh_FreeVars :: Inh_FreeVars -> (String)
caseExpr_Inh_FreeVars :: Inh_FreeVars -> (Maybe Expression)
:: Syn_FreeVars  = Syn_FreeVars (FreeVars) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
recNode_Syn_FreeVars :: Syn_FreeVars -> (Bool)
mExitId_Syn_FreeVars :: Syn_FreeVars -> (Maybe Int)
mEntryId_Syn_FreeVars :: Syn_FreeVars -> (Maybe Int)
hasRecs_Syn_FreeVars :: Syn_FreeVars -> (Bool)
graph_Syn_FreeVars :: Syn_FreeVars -> (GinGraph)
copy_Syn_FreeVars :: Syn_FreeVars -> (FreeVars)
wrap_FreeVars :: T_FreeVars  Inh_FreeVars  -> (Syn_FreeVars )

// cata
sem_FreeVars :: FreeVars  -> T_FreeVars 

// semantic domain
:: T_FreeVars  = T_FreeVars (Identity (T_FreeVars_s23 ))
:: T_FreeVars_s23  = C_FreeVars_s23 (T_FreeVars_v22 )
:: T_FreeVars_s24  = C_FreeVars_s24
:: T_FreeVars_v22  :== (T_FreeVars_vIn22 ) -> (T_FreeVars_vOut22 )
:: T_FreeVars_vIn22  = T_FreeVars_vIn22 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_FreeVars_vOut22  = T_FreeVars_vOut22 (FreeVars) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
sem_FreeVars_Cons  :: (T_FreeVar ) (T_FreeVars ) -> T_FreeVars 
sem_FreeVars_Nil  ::   T_FreeVars 

// FunType -----------------------------------------------------
// wrapper
:: Inh_FunType  = Inh_FunType (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_FunType :: Inh_FunType -> (ModuleEnv)
mergeId_Inh_FunType :: Inh_FunType -> (Int)
graph_Inh_FunType :: Inh_FunType -> (GinGraph)
currTaskName_Inh_FunType :: Inh_FunType -> (String)
caseExpr_Inh_FunType :: Inh_FunType -> (Maybe Expression)
:: Syn_FunType  = Syn_FunType (FunType) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
recNode_Syn_FunType :: Syn_FunType -> (Bool)
mExitId_Syn_FunType :: Syn_FunType -> (Maybe Int)
mEntryId_Syn_FunType :: Syn_FunType -> (Maybe Int)
hasRecs_Syn_FunType :: Syn_FunType -> (Bool)
graph_Syn_FunType :: Syn_FunType -> (GinGraph)
copy_Syn_FunType :: Syn_FunType -> (FunType)
wrap_FunType :: T_FunType  Inh_FunType  -> (Syn_FunType )

// cata
sem_FunType :: FunType  -> T_FunType 

// semantic domain
:: T_FunType  = T_FunType (Identity (T_FunType_s26 ))
:: T_FunType_s26  = C_FunType_s26 (T_FunType_v25 )
:: T_FunType_s27  = C_FunType_s27
:: T_FunType_v25  :== (T_FunType_vIn25 ) -> (T_FunType_vOut25 )
:: T_FunType_vIn25  = T_FunType_vIn25 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_FunType_vOut25  = T_FunType_vOut25 (FunType) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
sem_FunType_FunType  :: (T_Ident ) (Int) (T_Priority ) (T_SymbolType ) (Position) (FunSpecials) (VarInfoPtr) -> T_FunType 

// GExpression -------------------------------------------------
// wrapper
:: Inh_GExpression  = Inh_GExpression (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GExpression :: Inh_GExpression -> (ModuleEnv)
mergeId_Inh_GExpression :: Inh_GExpression -> (Int)
graph_Inh_GExpression :: Inh_GExpression -> (GinGraph)
currTaskName_Inh_GExpression :: Inh_GExpression -> (String)
caseExpr_Inh_GExpression :: Inh_GExpression -> (Maybe Expression)
:: Syn_GExpression  = Syn_GExpression (GExpression) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_GExpression :: Syn_GExpression -> (Bool)
ppDebugs_Syn_GExpression :: Syn_GExpression -> ([Doc])
ppDebug_Syn_GExpression :: Syn_GExpression -> (Doc)
ppAgs_Syn_GExpression :: Syn_GExpression -> ([Doc])
ppAg_Syn_GExpression :: Syn_GExpression -> (Doc)
mExitId_Syn_GExpression :: Syn_GExpression -> (Maybe Int)
mEntryId_Syn_GExpression :: Syn_GExpression -> (Maybe Int)
hasRecs_Syn_GExpression :: Syn_GExpression -> (Bool)
graph_Syn_GExpression :: Syn_GExpression -> (GinGraph)
copy_Syn_GExpression :: Syn_GExpression -> (GExpression)
wrap_GExpression :: T_GExpression  Inh_GExpression  -> (Syn_GExpression )

// cata
sem_GExpression :: GExpression  -> T_GExpression 

// semantic domain
:: T_GExpression  = T_GExpression (Identity (T_GExpression_s29 ))
:: T_GExpression_s29  = C_GExpression_s29 (T_GExpression_v28 )
:: T_GExpression_s30  = C_GExpression_s30
:: T_GExpression_v28  :== (T_GExpression_vIn28 ) -> (T_GExpression_vOut28 )
:: T_GExpression_vIn28  = T_GExpression_vIn28 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GExpression_vOut28  = T_GExpression_vOut28 (GExpression) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_GExpression_GUndefinedExpression  ::   T_GExpression 
sem_GExpression_GGraphExpression  :: (GGraph) -> T_GExpression 
sem_GExpression_GListExpression  :: ([GExpression]) -> T_GExpression 
sem_GExpression_GCleanExpression  :: (GCleanExpression) -> T_GExpression 

// GFunDef -----------------------------------------------------
// wrapper
:: Inh_GFunDef  = Inh_GFunDef (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GFunDef :: Inh_GFunDef -> (ModuleEnv)
mergeId_Inh_GFunDef :: Inh_GFunDef -> (Int)
graph_Inh_GFunDef :: Inh_GFunDef -> (GinGraph)
currTaskName_Inh_GFunDef :: Inh_GFunDef -> (String)
caseExpr_Inh_GFunDef :: Inh_GFunDef -> (Maybe Expression)
:: Syn_GFunDef  = Syn_GFunDef (GFunDef) ([FreeVar]) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
recNode_Syn_GFunDef :: Syn_GFunDef -> (Bool)
mExitId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
mEntryId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
hasRecs_Syn_GFunDef :: Syn_GFunDef -> (Bool)
graph_Syn_GFunDef :: Syn_GFunDef -> (GinGraph)
funArgs_Syn_GFunDef :: Syn_GFunDef -> ([FreeVar])
copy_Syn_GFunDef :: Syn_GFunDef -> (GFunDef)
wrap_GFunDef :: T_GFunDef  Inh_GFunDef  -> (Syn_GFunDef )

// cata
sem_GFunDef :: GFunDef  -> T_GFunDef 

// semantic domain
:: T_GFunDef  = T_GFunDef (Identity (T_GFunDef_s32 ))
:: T_GFunDef_s32  = C_GFunDef_s32 (T_GFunDef_v31 )
:: T_GFunDef_s33  = C_GFunDef_s33
:: T_GFunDef_v31  :== (T_GFunDef_vIn31 ) -> (T_GFunDef_vOut31 )
:: T_GFunDef_vIn31  = T_GFunDef_vIn31 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GFunDef_vOut31  = T_GFunDef_vOut31 (GFunDef) ([FreeVar]) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
sem_GFunDef_GFunDef  :: (String) (T_FreeVars ) (T_Expression ) (Optional SymbolType) (T_Priority ) -> T_GFunDef 

// GLet --------------------------------------------------------
// wrapper
:: Inh_GLet  = Inh_GLet (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GLet :: Inh_GLet -> (ModuleEnv)
mergeId_Inh_GLet :: Inh_GLet -> (Int)
graph_Inh_GLet :: Inh_GLet -> (GinGraph)
currTaskName_Inh_GLet :: Inh_GLet -> (String)
caseExpr_Inh_GLet :: Inh_GLet -> (Maybe Expression)
:: Syn_GLet  = Syn_GLet (GLet) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_GLet :: Syn_GLet -> (Bool)
ppDebugs_Syn_GLet :: Syn_GLet -> ([Doc])
ppDebug_Syn_GLet :: Syn_GLet -> (Doc)
ppAgs_Syn_GLet :: Syn_GLet -> ([Doc])
ppAg_Syn_GLet :: Syn_GLet -> (Doc)
mExitId_Syn_GLet :: Syn_GLet -> (Maybe Int)
mEntryId_Syn_GLet :: Syn_GLet -> (Maybe Int)
hasRecs_Syn_GLet :: Syn_GLet -> (Bool)
graph_Syn_GLet :: Syn_GLet -> (GinGraph)
copy_Syn_GLet :: Syn_GLet -> (GLet)
wrap_GLet :: T_GLet  Inh_GLet  -> (Syn_GLet )

// cata
sem_GLet :: GLet  -> T_GLet 

// semantic domain
:: T_GLet  = T_GLet (Identity (T_GLet_s35 ))
:: T_GLet_s35  = C_GLet_s35 (T_GLet_v34 )
:: T_GLet_s36  = C_GLet_s36
:: T_GLet_v34  :== (T_GLet_vIn34 ) -> (T_GLet_vOut34 )
:: T_GLet_vIn34  = T_GLet_vIn34 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GLet_vOut34  = T_GLet_vOut34 (GLet) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_GLet_GLet  :: (T_GLetBinds ) (T_Expression ) -> T_GLet 

// GLetBind ----------------------------------------------------
// wrapper
:: Inh_GLetBind  = Inh_GLetBind (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GLetBind :: Inh_GLetBind -> (ModuleEnv)
mergeId_Inh_GLetBind :: Inh_GLetBind -> (Int)
graph_Inh_GLetBind :: Inh_GLetBind -> (GinGraph)
currTaskName_Inh_GLetBind :: Inh_GLetBind -> (String)
caseExpr_Inh_GLetBind :: Inh_GLetBind -> (Maybe Expression)
:: Syn_GLetBind  = Syn_GLetBind (GLetBind) (GinGraph) (Bool) (Maybe Expression) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_GLetBind :: Syn_GLetBind -> (Bool)
ppDebugs_Syn_GLetBind :: Syn_GLetBind -> ([Doc])
ppDebug_Syn_GLetBind :: Syn_GLetBind -> (Doc)
ppAgs_Syn_GLetBind :: Syn_GLetBind -> ([Doc])
ppAg_Syn_GLetBind :: Syn_GLetBind -> (Doc)
mExitId_Syn_GLetBind :: Syn_GLetBind -> (Maybe Int)
mEntryId_Syn_GLetBind :: Syn_GLetBind -> (Maybe Int)
mCaseVarExpr_Syn_GLetBind :: Syn_GLetBind -> (Maybe Expression)
hasRecs_Syn_GLetBind :: Syn_GLetBind -> (Bool)
graph_Syn_GLetBind :: Syn_GLetBind -> (GinGraph)
copy_Syn_GLetBind :: Syn_GLetBind -> (GLetBind)
wrap_GLetBind :: T_GLetBind  Inh_GLetBind  -> (Syn_GLetBind )

// cata
sem_GLetBind :: GLetBind  -> T_GLetBind 

// semantic domain
:: T_GLetBind  = T_GLetBind (Identity (T_GLetBind_s38 ))
:: T_GLetBind_s38  = C_GLetBind_s38 (T_GLetBind_v37 )
:: T_GLetBind_s39  = C_GLetBind_s39
:: T_GLetBind_v37  :== (T_GLetBind_vIn37 ) -> (T_GLetBind_vOut37 )
:: T_GLetBind_vIn37  = T_GLetBind_vIn37 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GLetBind_vOut37  = T_GLetBind_vOut37 (GLetBind) (GinGraph) (Bool) (Maybe Expression) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_GLetBind_GLetBind  :: (String) (T_Expression ) -> T_GLetBind 

// GLetBinds ---------------------------------------------------
// wrapper
:: Inh_GLetBinds  = Inh_GLetBinds (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GLetBinds :: Inh_GLetBinds -> (ModuleEnv)
mergeId_Inh_GLetBinds :: Inh_GLetBinds -> (Int)
graph_Inh_GLetBinds :: Inh_GLetBinds -> (GinGraph)
currTaskName_Inh_GLetBinds :: Inh_GLetBinds -> (String)
caseExpr_Inh_GLetBinds :: Inh_GLetBinds -> (Maybe Expression)
:: Syn_GLetBinds  = Syn_GLetBinds (GLetBinds) (GinGraph) (Bool) (Maybe Expression) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_GLetBinds :: Syn_GLetBinds -> (Bool)
ppDebugs_Syn_GLetBinds :: Syn_GLetBinds -> ([Doc])
ppDebug_Syn_GLetBinds :: Syn_GLetBinds -> (Doc)
ppAgs_Syn_GLetBinds :: Syn_GLetBinds -> ([Doc])
ppAg_Syn_GLetBinds :: Syn_GLetBinds -> (Doc)
mExitId_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Int)
mEntryId_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Int)
mCaseVarExpr_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Expression)
hasRecs_Syn_GLetBinds :: Syn_GLetBinds -> (Bool)
graph_Syn_GLetBinds :: Syn_GLetBinds -> (GinGraph)
copy_Syn_GLetBinds :: Syn_GLetBinds -> (GLetBinds)
wrap_GLetBinds :: T_GLetBinds  Inh_GLetBinds  -> (Syn_GLetBinds )

// cata
sem_GLetBinds :: GLetBinds  -> T_GLetBinds 

// semantic domain
:: T_GLetBinds  = T_GLetBinds (Identity (T_GLetBinds_s41 ))
:: T_GLetBinds_s41  = C_GLetBinds_s41 (T_GLetBinds_v40 )
:: T_GLetBinds_s42  = C_GLetBinds_s42
:: T_GLetBinds_v40  :== (T_GLetBinds_vIn40 ) -> (T_GLetBinds_vOut40 )
:: T_GLetBinds_vIn40  = T_GLetBinds_vIn40 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GLetBinds_vOut40  = T_GLetBinds_vOut40 (GLetBinds) (GinGraph) (Bool) (Maybe Expression) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_GLetBinds_Cons  :: (T_GLetBind ) (T_GLetBinds ) -> T_GLetBinds 
sem_GLetBinds_Nil  ::   T_GLetBinds 

// GlobalDefinedSymbol -----------------------------------------
// wrapper
:: Inh_GlobalDefinedSymbol  = Inh_GlobalDefinedSymbol (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (ModuleEnv)
mergeId_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (Int)
graph_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (GinGraph)
currTaskName_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (String)
caseExpr_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (Maybe Expression)
:: Syn_GlobalDefinedSymbol  = Syn_GlobalDefinedSymbol (GlobalDefinedSymbol) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Bool)
ppDebugs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> ([Doc])
ppDebug_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Doc)
ppAgs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> ([Doc])
ppAg_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Doc)
mExitId_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Maybe Int)
mEntryId_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Maybe Int)
hasRecs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Bool)
graph_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (GinGraph)
copy_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (GlobalDefinedSymbol)
wrap_GlobalDefinedSymbol :: T_GlobalDefinedSymbol  Inh_GlobalDefinedSymbol  -> (Syn_GlobalDefinedSymbol )

// cata
sem_GlobalDefinedSymbol :: GlobalDefinedSymbol  -> T_GlobalDefinedSymbol 

// semantic domain
:: T_GlobalDefinedSymbol  = T_GlobalDefinedSymbol (Identity (T_GlobalDefinedSymbol_s44 ))
:: T_GlobalDefinedSymbol_s44  = C_GlobalDefinedSymbol_s44 (T_GlobalDefinedSymbol_v43 )
:: T_GlobalDefinedSymbol_s45  = C_GlobalDefinedSymbol_s45
:: T_GlobalDefinedSymbol_v43  :== (T_GlobalDefinedSymbol_vIn43 ) -> (T_GlobalDefinedSymbol_vOut43 )
:: T_GlobalDefinedSymbol_vIn43  = T_GlobalDefinedSymbol_vIn43 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_GlobalDefinedSymbol_vOut43  = T_GlobalDefinedSymbol_vOut43 (GlobalDefinedSymbol) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_GlobalDefinedSymbol_Tuple  :: (Global DefinedSymbol) -> T_GlobalDefinedSymbol 

// Ident -------------------------------------------------------
// wrapper
:: Inh_Ident  = Inh_Ident (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Ident :: Inh_Ident -> (ModuleEnv)
mergeId_Inh_Ident :: Inh_Ident -> (Int)
graph_Inh_Ident :: Inh_Ident -> (GinGraph)
currTaskName_Inh_Ident :: Inh_Ident -> (String)
caseExpr_Inh_Ident :: Inh_Ident -> (Maybe Expression)
:: Syn_Ident  = Syn_Ident (Ident) (GinGraph) (Bool) (String) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_Ident :: Syn_Ident -> (Bool)
ppDebugs_Syn_Ident :: Syn_Ident -> ([Doc])
ppDebug_Syn_Ident :: Syn_Ident -> (Doc)
ppAgs_Syn_Ident :: Syn_Ident -> ([Doc])
ppAg_Syn_Ident :: Syn_Ident -> (Doc)
mExitId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mEntryId_Syn_Ident :: Syn_Ident -> (Maybe Int)
isCurrTask_Syn_Ident :: Syn_Ident -> (Bool)
ident_Syn_Ident :: Syn_Ident -> (String)
hasRecs_Syn_Ident :: Syn_Ident -> (Bool)
graph_Syn_Ident :: Syn_Ident -> (GinGraph)
copy_Syn_Ident :: Syn_Ident -> (Ident)
wrap_Ident :: T_Ident  Inh_Ident  -> (Syn_Ident )

// cata
sem_Ident :: Ident  -> T_Ident 

// semantic domain
:: T_Ident  = T_Ident (Identity (T_Ident_s47 ))
:: T_Ident_s47  = C_Ident_s47 (T_Ident_v46 )
:: T_Ident_s48  = C_Ident_s48
:: T_Ident_v46  :== (T_Ident_vIn46 ) -> (T_Ident_vOut46 )
:: T_Ident_vIn46  = T_Ident_vIn46 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Ident_vOut46  = T_Ident_vOut46 (Ident) (GinGraph) (Bool) (String) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_Ident_Ident  :: (String) (SymbolPtr) -> T_Ident 

// MaybeExpression ---------------------------------------------
// wrapper
:: Inh_MaybeExpression  = Inh_MaybeExpression (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_MaybeExpression :: Inh_MaybeExpression -> (ModuleEnv)
mergeId_Inh_MaybeExpression :: Inh_MaybeExpression -> (Int)
graph_Inh_MaybeExpression :: Inh_MaybeExpression -> (GinGraph)
currTaskName_Inh_MaybeExpression :: Inh_MaybeExpression -> (String)
caseExpr_Inh_MaybeExpression :: Inh_MaybeExpression -> (Maybe Expression)
:: Syn_MaybeExpression  = Syn_MaybeExpression (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
recNode_Syn_MaybeExpression :: Syn_MaybeExpression -> (Bool)
mExitId_Syn_MaybeExpression :: Syn_MaybeExpression -> (Maybe Int)
mEntryId_Syn_MaybeExpression :: Syn_MaybeExpression -> (Maybe Int)
hasRecs_Syn_MaybeExpression :: Syn_MaybeExpression -> (Bool)
graph_Syn_MaybeExpression :: Syn_MaybeExpression -> (GinGraph)
wrap_MaybeExpression :: T_MaybeExpression  Inh_MaybeExpression  -> (Syn_MaybeExpression )

// cata
sem_MaybeExpression :: MaybeExpression  -> T_MaybeExpression 

// semantic domain
:: T_MaybeExpression  = T_MaybeExpression (Identity (T_MaybeExpression_s50 ))
:: T_MaybeExpression_s50  = C_MaybeExpression_s50 (T_MaybeExpression_v49 )
:: T_MaybeExpression_s51  = C_MaybeExpression_s51
:: T_MaybeExpression_v49  :== (T_MaybeExpression_vIn49 ) -> (T_MaybeExpression_vOut49 )
:: T_MaybeExpression_vIn49  = T_MaybeExpression_vIn49 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_MaybeExpression_vOut49  = T_MaybeExpression_vOut49 (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Bool)
sem_MaybeExpression_Just  :: (T_Expression ) -> T_MaybeExpression 
sem_MaybeExpression_Nothing  ::   T_MaybeExpression 

// Priority ----------------------------------------------------
// wrapper
:: Inh_Priority  = Inh_Priority (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Priority :: Inh_Priority -> (ModuleEnv)
mergeId_Inh_Priority :: Inh_Priority -> (Int)
graph_Inh_Priority :: Inh_Priority -> (GinGraph)
currTaskName_Inh_Priority :: Inh_Priority -> (String)
caseExpr_Inh_Priority :: Inh_Priority -> (Maybe Expression)
:: Syn_Priority  = Syn_Priority (Priority) (GinGraph)
graph_Syn_Priority :: Syn_Priority -> (GinGraph)
copy_Syn_Priority :: Syn_Priority -> (Priority)
wrap_Priority :: T_Priority  Inh_Priority  -> (Syn_Priority )

// cata
sem_Priority :: Priority  -> T_Priority 

// semantic domain
:: T_Priority  = T_Priority (Identity (T_Priority_s53 ))
:: T_Priority_s53  = C_Priority_s53 (T_Priority_v52 )
:: T_Priority_s54  = C_Priority_s54
:: T_Priority_v52  :== (T_Priority_vIn52 ) -> (T_Priority_vOut52 )
:: T_Priority_vIn52  = T_Priority_vIn52 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Priority_vOut52  = T_Priority_vOut52 (Priority) (GinGraph)
sem_Priority_Prio  :: (Assoc) (Int) -> T_Priority 
sem_Priority_NoPrio  ::   T_Priority 

// Selection ---------------------------------------------------
// wrapper
:: Inh_Selection  = Inh_Selection (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Selection :: Inh_Selection -> (ModuleEnv)
mergeId_Inh_Selection :: Inh_Selection -> (Int)
graph_Inh_Selection :: Inh_Selection -> (GinGraph)
currTaskName_Inh_Selection :: Inh_Selection -> (String)
caseExpr_Inh_Selection :: Inh_Selection -> (Maybe Expression)
:: Syn_Selection  = Syn_Selection (Selection) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_Selection :: Syn_Selection -> (Bool)
ppDebugs_Syn_Selection :: Syn_Selection -> ([Doc])
ppDebug_Syn_Selection :: Syn_Selection -> (Doc)
ppAgs_Syn_Selection :: Syn_Selection -> ([Doc])
ppAg_Syn_Selection :: Syn_Selection -> (Doc)
mExitId_Syn_Selection :: Syn_Selection -> (Maybe Int)
mEntryId_Syn_Selection :: Syn_Selection -> (Maybe Int)
hasRecs_Syn_Selection :: Syn_Selection -> (Bool)
graph_Syn_Selection :: Syn_Selection -> (GinGraph)
copy_Syn_Selection :: Syn_Selection -> (Selection)
wrap_Selection :: T_Selection  Inh_Selection  -> (Syn_Selection )

// cata
sem_Selection :: Selection  -> T_Selection 

// semantic domain
:: T_Selection  = T_Selection (Identity (T_Selection_s56 ))
:: T_Selection_s56  = C_Selection_s56 (T_Selection_v55 )
:: T_Selection_s57  = C_Selection_s57
:: T_Selection_v55  :== (T_Selection_vIn55 ) -> (T_Selection_vOut55 )
:: T_Selection_vIn55  = T_Selection_vIn55 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Selection_vOut55  = T_Selection_vOut55 (Selection) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_Selection_RecordSelection  :: (T_GlobalDefinedSymbol ) (Int) -> T_Selection 
sem_Selection_ArraySelection  :: (T_GlobalDefinedSymbol ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_DictionarySelection  :: (T_BoundVar ) (T_Selections ) (ExprInfoPtr) (T_Expression ) -> T_Selection 

// Selections --------------------------------------------------
// wrapper
:: Inh_Selections  = Inh_Selections (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_Selections :: Inh_Selections -> (ModuleEnv)
mergeId_Inh_Selections :: Inh_Selections -> (Int)
graph_Inh_Selections :: Inh_Selections -> (GinGraph)
currTaskName_Inh_Selections :: Inh_Selections -> (String)
caseExpr_Inh_Selections :: Inh_Selections -> (Maybe Expression)
:: Syn_Selections  = Syn_Selections (Selections) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_Selections :: Syn_Selections -> (Bool)
ppDebugs_Syn_Selections :: Syn_Selections -> ([Doc])
ppDebug_Syn_Selections :: Syn_Selections -> (Doc)
ppAgs_Syn_Selections :: Syn_Selections -> ([Doc])
ppAg_Syn_Selections :: Syn_Selections -> (Doc)
mExitId_Syn_Selections :: Syn_Selections -> (Maybe Int)
mEntryId_Syn_Selections :: Syn_Selections -> (Maybe Int)
hasRecs_Syn_Selections :: Syn_Selections -> (Bool)
graph_Syn_Selections :: Syn_Selections -> (GinGraph)
copy_Syn_Selections :: Syn_Selections -> (Selections)
wrap_Selections :: T_Selections  Inh_Selections  -> (Syn_Selections )

// cata
sem_Selections :: Selections  -> T_Selections 

// semantic domain
:: T_Selections  = T_Selections (Identity (T_Selections_s59 ))
:: T_Selections_s59  = C_Selections_s59 (T_Selections_v58 )
:: T_Selections_s60  = C_Selections_s60
:: T_Selections_v58  :== (T_Selections_vIn58 ) -> (T_Selections_vOut58 )
:: T_Selections_vIn58  = T_Selections_vIn58 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_Selections_vOut58  = T_Selections_vOut58 (Selections) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_Selections_Cons  :: (T_Selection ) (T_Selections ) -> T_Selections 
sem_Selections_Nil  ::   T_Selections 

// SymbIdent ---------------------------------------------------
// wrapper
:: Inh_SymbIdent  = Inh_SymbIdent (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_SymbIdent :: Inh_SymbIdent -> (ModuleEnv)
mergeId_Inh_SymbIdent :: Inh_SymbIdent -> (Int)
graph_Inh_SymbIdent :: Inh_SymbIdent -> (GinGraph)
currTaskName_Inh_SymbIdent :: Inh_SymbIdent -> (String)
caseExpr_Inh_SymbIdent :: Inh_SymbIdent -> (Maybe Expression)
:: Syn_SymbIdent  = Syn_SymbIdent (SymbIdent) (GinGraph) (Bool) (String) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
ppDebugs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppDebug_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppAgs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppAg_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
mExitId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mEntryId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
isCurrTask_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
ident_Syn_SymbIdent :: Syn_SymbIdent -> (String)
hasRecs_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
graph_Syn_SymbIdent :: Syn_SymbIdent -> (GinGraph)
copy_Syn_SymbIdent :: Syn_SymbIdent -> (SymbIdent)
wrap_SymbIdent :: T_SymbIdent  Inh_SymbIdent  -> (Syn_SymbIdent )

// cata
sem_SymbIdent :: SymbIdent  -> T_SymbIdent 

// semantic domain
:: T_SymbIdent  = T_SymbIdent (Identity (T_SymbIdent_s62 ))
:: T_SymbIdent_s62  = C_SymbIdent_s62 (T_SymbIdent_v61 )
:: T_SymbIdent_s63  = C_SymbIdent_s63
:: T_SymbIdent_v61  :== (T_SymbIdent_vIn61 ) -> (T_SymbIdent_vOut61 )
:: T_SymbIdent_vIn61  = T_SymbIdent_vIn61 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_SymbIdent_vOut61  = T_SymbIdent_vOut61 (SymbIdent) (GinGraph) (Bool) (String) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_SymbIdent_SymbIdent  :: (T_Ident ) (SymbKind) -> T_SymbIdent 

// SymbolType --------------------------------------------------
// wrapper
:: Inh_SymbolType  = Inh_SymbolType (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
moduleEnv_Inh_SymbolType :: Inh_SymbolType -> (ModuleEnv)
mergeId_Inh_SymbolType :: Inh_SymbolType -> (Int)
graph_Inh_SymbolType :: Inh_SymbolType -> (GinGraph)
currTaskName_Inh_SymbolType :: Inh_SymbolType -> (String)
caseExpr_Inh_SymbolType :: Inh_SymbolType -> (Maybe Expression)
:: Syn_SymbolType  = Syn_SymbolType (SymbolType) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
recNode_Syn_SymbolType :: Syn_SymbolType -> (Bool)
ppDebugs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppDebug_Syn_SymbolType :: Syn_SymbolType -> (Doc)
ppAgs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppAg_Syn_SymbolType :: Syn_SymbolType -> (Doc)
mExitId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
mEntryId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
hasRecs_Syn_SymbolType :: Syn_SymbolType -> (Bool)
graph_Syn_SymbolType :: Syn_SymbolType -> (GinGraph)
copy_Syn_SymbolType :: Syn_SymbolType -> (SymbolType)
wrap_SymbolType :: T_SymbolType  Inh_SymbolType  -> (Syn_SymbolType )

// cata
sem_SymbolType :: SymbolType  -> T_SymbolType 

// semantic domain
:: T_SymbolType  = T_SymbolType (Identity (T_SymbolType_s65 ))
:: T_SymbolType_s65  = C_SymbolType_s65 (T_SymbolType_v64 )
:: T_SymbolType_s66  = C_SymbolType_s66
:: T_SymbolType_v64  :== (T_SymbolType_vIn64 ) -> (T_SymbolType_vOut64 )
:: T_SymbolType_vIn64  = T_SymbolType_vIn64 (Maybe Expression) (String) (GinGraph) (Int) (ModuleEnv)
:: T_SymbolType_vOut64  = T_SymbolType_vOut64 (SymbolType) (GinGraph) (Bool) (Maybe Int) (Maybe Int) (Doc) ([Doc]) (Doc) ([Doc]) (Bool)
sem_SymbolType_SymbolType  :: ([TypeVar]) ([AType]) (StrictnessList) (Int) (AType) ([TypeContext]) ([AttributeVar]) ([AttrInequality]) -> T_SymbolType 
