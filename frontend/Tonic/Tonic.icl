implementation module Tonic.Tonic

// 2 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag"

from StdClass import class + (..)
from StdOverloaded import class < (..)
from StdInt import instance + Int, instance < Int
from StdList import ++, foldr, map
from StdOverloaded import class +++ (..)
from StdString import instance +++ {#Char}, instance toString Int, instance == {#Char}
from StdFunc import o
from StdBool import ||
import StdMisc
import Data.Void
import Data.Func
import Data.List

import Data.Graph
import Data.Maybe
import Text.PPrint
import Tonic.AbsSyn
import Tonic.Util
from syntax import :: Optional (..), :: FunDef {..}, :: FunInfo, :: FunKind,
  :: FunctionBody {..}, :: TransformedBody {..}, :: CheckedBody, :: ParsedBody,
  :: AType {..}, :: TypeAttribute, :: Type {..}, :: TypeKind, :: TempVarId,
  :: ATypeVar, :: BasicType, :: ConsVariable, :: TypeSymbIdent {..},
  :: TypeSymbProperties
// 29 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"

// 2 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag"

from StdClass import class + (..)
from StdOverloaded import class < (..)
from StdInt import instance + Int, instance < Int
from StdList import ++, foldr, map
from StdOverloaded import class +++ (..)
from StdString import instance +++ {#Char}, instance toString Int
from StdFunc import o
import StdMisc
import Data.Void
import Data.Func
import Data.List

import Data.Graph
import Data.Maybe
import Text.PPrint
import Tonic.AbsSyn
import Tonic.Util
// 50 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"

// 2 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/ExprSyn.ag"

from syntax import
  :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let {..}, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..},
  :: SymbIdent {..}, :: SymbKind, :: Priority (..), :: Assoc (..), :: VarInfoPtr, :: DynamicExpr,
  :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index, :: Bind,
  :: Position, :: AType, :: Env, :: Ident {..}, :: SymbolPtr,
  :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..),
  :: FieldSymbol, :: IclModule, :: DclModule, :: FunDef, :: Optional,
  :: SymbolType {..}, :: LetBind, :: TypeVar {..}, :: StrictnessList (..),
  :: TypeContext {..}, :: AttributeVar {..}, :: AttrInequality {..},
  :: TypeVarInfoPtr {..}, :: AttrVarInfoPtr, :: Type, :: TCClass,
  :: TypeVarInfo, :: AttrVarInfo, :: FunType {..}, :: FunSpecials

import Tonic.AbsSyn
// 69 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"
from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// 265 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag"


(<>) infixr 5 :: (Maybe a) (Maybe a) -> Maybe a
(<>) Nothing  ma  = ma
(<>) ma       _   = ma

mkGinGraph :: Int String GinGraph ModuleEnv Expression -> GinGraph
mkGinGraph mid ctn gg menv expr =
  graph_Syn_Expression (wrap_Expression (sem_Expression expr)
                       (Inh_Expression Nothing ctn gg mid menv))

listExprToList :: Expression -> [Expression]
listExprToList (App app) =
  case app.app_symb.symb_ident.id_name of
    "_Cons" ->
      case app.app_args of
        [head:tail:_] -> [head : listExprToList tail]
        _             -> abort "listExprToList should not happen"
    "_Nil"  -> []
    _       -> abort "listExprToList: App is not a list"
listExprToList _ = []

nodeErr :: ModuleEnv (Maybe Int) Expression -> String
nodeErr menv mn expr = ppCompact (ppExpression menv expr) +++ "\n" +++
  maybe "for which its ID is unknown" (\n -> "with node ID " +++ toString n) mn

edgeErr :: ModuleEnv String (Maybe Int) Expression (Maybe Int) Expression -> a
edgeErr menv errmsg lid lexpr rid rexpr = abort ("Cannot create " +++ errmsg
  +++ " between left expression\n\t" +++ nodeErr menv lid lexpr
  +++ " and right expression\n\t" +++ nodeErr menv rid rexpr +++ "\n")

addEmptyEdge :: (Int, Int) GinGraph -> GinGraph
addEmptyEdge e g = addEdge emptyEdge e g

addNode` :: GNode GinGraph -> SynExpression
addNode` node graph
  # (n, g) = addNode node graph
  = mkSynExpr (Just n) g

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph
funToGraph {fun_ident=fun_ident, fun_body = TransformedBody tb} fun_defs icl_module dcl_modules
  = Yes $ GGraph mkBody
  where
  mkBody
    # (mergeId, g)  = addNode GMerge emptyGraph
    # inh           = mkInhExpr (mkModuleEnv fun_defs icl_module dcl_modules) g mergeId fun_ident.id_name Nothing
    # gram          = wrapExpr tb.tb_rhs inh
    # g             = graph_Syn_Expression gram
    # (initId, g)   = addNode GInit g
    # g             = if (hasRecs_Syn_Expression gram)
                        (mkRec (mEntryId_Syn_Expression gram) initId mergeId g)
                        (mkNonrec (mEntryId_Syn_Expression gram) initId mergeId g)
    = addStopEdges g

  addStopEdges g
    # leafs        = leafNodes g
    # (stopId, g)  = addNode GStop g
    = foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs

  mkRec mfirstId initId mergeId g
    # g = addEmptyEdge (initId, mergeId) g
    = maybe g (\firstId -> addEmptyEdge (mergeId, firstId) g) mfirstId

  mkNonrec mfirstId initId mergeId g
    # g = removeNode mergeId g
    = maybe g (\firstId -> addEmptyEdge (initId, firstId) g) mfirstId

  mkInhExpr menv g mid nm ce = Inh_Expression ce nm g mid menv

  wrapExpr expr inh = wrap_Expression (sem_Expression expr) inh

funToGraph _ _ _ _ = No

instance toString GNode where
  toString GInit = "GInit"
  toString GStop = "GStop"
  toString (GDecision _ _) = "GDecision"
  toString GMerge = "GMerge"
  toString (GLet _) = "GLet"
  toString GParallelSplit = "GParallelSplit"
  toString (GParallelJoin _) = "GParallelJoin"
  toString (GTaskApp _ _) = "GTaskApp"
  toString (GReturn _) = "GReturn"
  toString (GAssign _) = "GAssign"
  toString GStep = "GStep"
  toString GListComprehension = "GListComprehension"

/*
Task assignment drawing: Needs a stick.png with a stick figure (can be PDF?)
digraph G {
   rankdir=LR;

    subgraph clusterUser {label="User"; labelloc="b"; peripheries=0; user};
    user [shapefile="stick.png", peripheries=0, style=invis];

    login [label="Log In", shape=ellipse];

    user->login [arrowhead=none];
}
*/
// 180 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"

// 163 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag"

mkPrettyExpr :: ModuleEnv Expression -> String
mkPrettyExpr menv expr = ppCompact (ppExpression menv expr)

ppCompact :: (Doc -> String)
ppCompact = display o renderCompact

ppExpression :: ModuleEnv Expression -> Doc
ppExpression menv expr = ppAg_Syn_Expression (wrap_Expression (sem_Expression expr) (mkPPInhExpression menv))

ppGExpression :: ModuleEnv GExpression -> Doc
ppGExpression menv expr = ppAg_Syn_GExpression (wrap_GExpression (sem_GExpression expr) (mkPPInhGExpression menv))

ppGLetBind :: ModuleEnv GLetBind -> Doc
ppGLetBind menv expr = ppAg_Syn_GLetBind (wrap_GLetBind (sem_GLetBind expr) (mkPPInhGLetBind menv))

ppDebugExpression :: ModuleEnv Expression -> Doc
ppDebugExpression menv expr = ppDebug_Syn_Expression (wrap_Expression (sem_Expression expr) (mkPPInhExpression menv))

ppFreeVar :: ModuleEnv FreeVar -> Doc
ppFreeVar menv fv = ppAg_Syn_FreeVar (wrap_FreeVar (sem_FreeVar fv) (mkPPInhFreeVar menv))

mkPPInhExpression :: ModuleEnv -> Inh_Expression
mkPPInhExpression me = Inh_Expression Nothing "" emptyGraph 0 me

mkPPInhGExpression :: ModuleEnv -> Inh_GExpression
mkPPInhGExpression me = Inh_GExpression Nothing "" emptyGraph 0 me

mkPPInhGLetBind :: ModuleEnv -> Inh_GLetBind
mkPPInhGLetBind me = Inh_GLetBind Nothing "" emptyGraph 0 me

mkPPInhFreeVar :: ModuleEnv -> Inh_FreeVar
mkPPInhFreeVar me = Inh_FreeVar Nothing "" emptyGraph 0 me


mkTaskDot :: ModuleEnv String GGraph -> String
mkTaskDot menv funnm (GGraph g) = "subgraph cluster_" +++ funnm +++ " {\n label=\"" +++ funnm  +++ "\"  color=\"black\";\n" +++
  mkNodes +++ "\n" +++
  mkEdges +++ "\n}"
  where
  mkNodes = concatStrings (map (nodeToDot menv funnm g) (nodeIndices g))
  mkEdges = concatStrings (map edgeToDot (edgeIndices g))
  edgeToDot ei=:(l, r) = mkDotNodeLbl funnm l +++ " -> " +++ mkDotNodeLbl funnm r +++ mkDotArgs [mkDotAttrKV "label" edgeLbl] // TODO: Use different arrow for task assignment
    where edgeLbl = maybe "" (\e -> fromMaybe "" e.edge_pattern) $ getEdgeData ei g

mkDotAttrKV :: String String -> String
mkDotAttrKV k v = k +++ "=" +++ "\"" +++ v +++ "\""

mkDotArgs :: [String] -> String
mkDotArgs attrs = " [" +++ intercalateString ", " attrs +++ "];\n"

mkDotNodeLbl :: String Int -> String
mkDotNodeLbl funnm n = funnm +++ "_node_" +++ toString n

nodeToDot :: ModuleEnv String GinGraph Int -> String
nodeToDot menv funnm g currIdx =
  case currNode of
    GInit                 -> blackNode [shape "triangle", width ".25", height ".25", orientation "-90.0"]
    GStop                 -> blackNode [shape "box", width ".2", height ".2"]
    (GDecision _ expr)    -> whiteNode [shape "diamond", label expr]
    GMerge                -> blackNode [shape "diamond", width ".25", height ".25"]
    (GLet glt)            -> whiteNode [shape "box", label (intercalateString "\n" $ map (ppCompact o ppGLetBind menv) glt)] // TODO: Rounded corners
    GParallelSplit        -> whiteNode [shape "circle", label "Run in\nparallel"]
    (GParallelJoin jt)    -> whiteNode [shape "circle", label (mkJoinLbl jt)]
    (GTaskApp tid exprs)  -> whiteNode [shape "box", label tid] // TODO: complex contents with extra bar
    (GReturn expr)        -> whiteNode [shape "oval", label (ppCompact $ ppGExpression menv expr)]
    (GAssign usr)         -> let  idxStr = toString currIdx
                                  usrStr = "user" +++ idxStr
                             in   "subgraph cluster_user" +++ idxStr +++ "{ label=" +++ usr +++ "; labelloc=b; peripheries=0; " +++ usrStr +++ "}" +++
                                  usrStr +++ mkDotArgs [ mkDotAttrKV "shapefile" "\"stick.png\""
                                                       , mkDotAttrKV "peripheries" "0"
                                                       , style "invis" ]
    GStep                 -> whiteNode [shape "circle", label "Step"]
    GListComprehension    -> whiteNode [shape "box", style "rounded", label "for each in (listcomprehension)"]
  where
  currNode         = getNodeData` currIdx g
  whiteNode attrs  = mkDotNode [fontcolor "black", fillcolor "white", style "filled", label "" : attrs]
  blackNode attrs  = mkDotNode [fontcolor "white", fillcolor "black", style "filled", label "" : attrs]
  mkDotNode attrs  = mkDotNodeLbl funnm currIdx +++ mkDotArgs attrs
  shape v          = mkDotAttrKV "shape" v
  label v          = mkDotAttrKV "label" v
  color v          = mkDotAttrKV "color" v
  fillcolor v      = mkDotAttrKV "fillcolor" v
  fontcolor v      = mkDotAttrKV "fontcolor" v
  width v          = mkDotAttrKV "width" v
  height v         = mkDotAttrKV "height" v
  style v          = mkDotAttrKV "style" v
  orientation v    = mkDotAttrKV "orientation" v
  mkJoinLbl DisFirstBin   = "First\nfinished\ntask"
  mkJoinLbl DisFirstList  = "First\nfinished\ntask"
  mkJoinLbl DisLeft       = "Left\nresult"
  mkJoinLbl DisRight      = "Right\nresult"
  mkJoinLbl ConAll        = "All\nresults"
  mkJoinLbl ConPair       = "Pair\nof results"

getNodeData` :: Int GinGraph -> GNode
getNodeData` n g = fromMaybe err (getNodeData n g)
  where err = abort ("No data for node " +++ toString n)
// 281 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"
// App ---------------------------------------------------------
// wrapper
moduleEnv_Inh_App :: Inh_App -> (ModuleEnv)
moduleEnv_Inh_App (Inh_App _ _ _ _ x) = x
mergeId_Inh_App :: Inh_App -> (Int)
mergeId_Inh_App (Inh_App _ _ _ x _) = x
graph_Inh_App :: Inh_App -> (GinGraph)
graph_Inh_App (Inh_App _ _ x _ _) = x
currTaskName_Inh_App :: Inh_App -> (String)
currTaskName_Inh_App (Inh_App _ x _ _ _) = x
caseExpr_Inh_App :: Inh_App -> (Maybe Expression)
caseExpr_Inh_App (Inh_App x _ _ _ _) = x
reifySymbolType_Syn_App :: Syn_App -> (Maybe SymbolType)
reifySymbolType_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
reifyFunType_Syn_App :: Syn_App -> (Maybe FunType)
reifyFunType_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
reifyFunDef_Syn_App :: Syn_App -> (Maybe GFunDef)
reifyFunDef_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
recNode_Syn_App :: Syn_App -> (Bool)
recNode_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
ppDebugs_Syn_App :: Syn_App -> ([Doc])
ppDebugs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
ppDebug_Syn_App :: Syn_App -> (Doc)
ppDebug_Syn_App (Syn_App _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
ppAgs_Syn_App :: Syn_App -> ([Doc])
ppAgs_Syn_App (Syn_App _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
ppAg_Syn_App :: Syn_App -> (Doc)
ppAg_Syn_App (Syn_App _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
mExitId_Syn_App :: Syn_App -> (Maybe Int)
mExitId_Syn_App (Syn_App _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
mEntryId_Syn_App :: Syn_App -> (Maybe Int)
mEntryId_Syn_App (Syn_App _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
isTask_Syn_App :: Syn_App -> (Bool)
isTask_Syn_App (Syn_App _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_App :: Syn_App -> (Bool)
hasRecs_Syn_App (Syn_App _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_App :: Syn_App -> (GinGraph)
graph_Syn_App (Syn_App _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_App :: Syn_App -> (App)
copy_Syn_App (Syn_App x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_App :: T_App  Inh_App  -> (Syn_App )
wrap_App (T_App act) (Inh_App alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_App_s2 sem arg) >>= \ (T_App_vOut1 alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType) ->
     lift (Syn_App alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType)
   )

// cata
sem_App :: App  -> T_App 
sem_App { App | app_symb = app_symb_,app_args = app_args_,app_info_ptr = app_info_ptr_ } = sem_App_App ( sem_SymbIdent app_symb_ ) ( sem_Expressions app_args_ ) app_info_ptr_       

// semantic domain
attach_T_App (T_App t_App) = t_App
inv_App_s2 (C_App_s2 x) = x
sem_App_App  :: (T_SymbIdent ) (T_Expressions ) (ExprInfoPtr)        -> T_App 
sem_App_App arg_app_symb_ arg_app_args_ arg_app_info_ptr_        = T_App (lift st2) where
   st2 =
        let
            v1 (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          st_app_symbX53 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_app_symb_))
                          st_app_argsX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_app_args_))
                          st_appArg1ExprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression appArg1Expr_val_)))
                          st_appArg2ExprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression appArg2Expr_val_)))
                          st_bindRhsAppIX2 = 'Control.Monad.Identity'.runIdentity (attach_T_App ((sem_App bindRhsAppI_val_)))
                          st_bindRhsFunDefX29 = 'Control.Monad.Identity'.runIdentity (attach_T_GFunDef ((sem_GFunDef bindRhsFunDef_val_)))
                          st_bindRhsSymbolTypeIX56 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbolType ((sem_SymbolType bindRhsSymbolTypeI_val_)))
                          st_binAppArg2ExprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression binAppArg2Expr_val_)))
                          st_parBinAppArg2ExprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression parBinAppArg2Expr_val_)))
                          (T_SymbIdent_vOut52 aapp_symbIcopy aapp_symbIgraph aapp_symbIhasRecs aapp_symbIident aapp_symbIisCurrTask aapp_symbIisInfix aapp_symbIisTask aapp_symbImEntryId aapp_symbImExitId aapp_symbIppAg aapp_symbIppAgs aapp_symbIppDebug aapp_symbIppDebugs aapp_symbIrecNode aapp_symbIreifyFunDef aapp_symbIreifyFunType aapp_symbIreifySymbolType) = inv_SymbIdent_s53 st_app_symbX53 (T_SymbIdent_vIn52 aapp_symbOcaseExpr aapp_symbOcurrTaskName aapp_symbOgraph aapp_symbOmergeId aapp_symbOmoduleEnv)
                          (T_Expressions_vOut16 aapp_argsIcopy aapp_argsIgraph aapp_argsIhasRecs aapp_argsImEntryId aapp_argsImExitId aapp_argsIppAg aapp_argsIppAgs aapp_argsIppDebug aapp_argsIppDebugs aapp_argsIrecNode) = inv_Expressions_s17 st_app_argsX17 (T_Expressions_vIn16 aapp_argsOcaseExpr aapp_argsOcurrTaskName aapp_argsOgraph aapp_argsOmergeId aapp_argsOmoduleEnv)
                          (T_Expression_vOut13 aappArg1ExprIcopy aappArg1ExprIgraph aappArg1ExprIhasRecs aappArg1ExprImEntryId aappArg1ExprImExitId aappArg1ExprIppAg aappArg1ExprIppAgs aappArg1ExprIppDebug aappArg1ExprIppDebugs aappArg1ExprIrecNode) = inv_Expression_s14 st_appArg1ExprX14 (T_Expression_vIn13 aappArg1ExprOcaseExpr aappArg1ExprOcurrTaskName aappArg1ExprOgraph aappArg1ExprOmergeId aappArg1ExprOmoduleEnv)
                          (T_Expression_vOut13 aappArg2ExprIcopy aappArg2ExprIgraph aappArg2ExprIhasRecs aappArg2ExprImEntryId aappArg2ExprImExitId aappArg2ExprIppAg aappArg2ExprIppAgs aappArg2ExprIppDebug aappArg2ExprIppDebugs aappArg2ExprIrecNode) = inv_Expression_s14 st_appArg2ExprX14 (T_Expression_vIn13 aappArg2ExprOcaseExpr aappArg2ExprOcurrTaskName aappArg2ExprOgraph aappArg2ExprOmergeId aappArg2ExprOmoduleEnv)
                          (T_App_vOut1 abindRhsAppIIcopy abindRhsAppIIgraph abindRhsAppIIhasRecs abindRhsAppIIisTask abindRhsAppIImEntryId abindRhsAppIImExitId abindRhsAppIIppAg abindRhsAppIIppAgs abindRhsAppIIppDebug abindRhsAppIIppDebugs abindRhsAppIIrecNode abindRhsAppIIreifyFunDef abindRhsAppIIreifyFunType abindRhsAppIIreifySymbolType) = inv_App_s2 st_bindRhsAppIX2 (T_App_vIn1 abindRhsAppIOcaseExpr abindRhsAppIOcurrTaskName abindRhsAppIOgraph abindRhsAppIOmergeId abindRhsAppIOmoduleEnv)
                          (T_GFunDef_vOut28 abindRhsFunDefIcopy abindRhsFunDefIfunArgs abindRhsFunDefIfunRhs abindRhsFunDefIgraph abindRhsFunDefIhasRecs abindRhsFunDefImEntryId abindRhsFunDefImExitId abindRhsFunDefIrecNode) = inv_GFunDef_s29 st_bindRhsFunDefX29 (T_GFunDef_vIn28 abindRhsFunDefOcaseExpr abindRhsFunDefOcurrTaskName abindRhsFunDefOgraph abindRhsFunDefOmergeId abindRhsFunDefOmoduleEnv)
                          (T_SymbolType_vOut55 abindRhsSymbolTypeIIcopy abindRhsSymbolTypeIIgraph abindRhsSymbolTypeIIhasRecs abindRhsSymbolTypeIIisTask abindRhsSymbolTypeIImEntryId abindRhsSymbolTypeIImExitId abindRhsSymbolTypeIIppAg abindRhsSymbolTypeIIppAgs abindRhsSymbolTypeIIppDebug abindRhsSymbolTypeIIppDebugs abindRhsSymbolTypeIIrecNode) = inv_SymbolType_s56 st_bindRhsSymbolTypeIX56 (T_SymbolType_vIn55 abindRhsSymbolTypeIOcaseExpr abindRhsSymbolTypeIOcurrTaskName abindRhsSymbolTypeIOgraph abindRhsSymbolTypeIOmergeId abindRhsSymbolTypeIOmoduleEnv)
                          (T_Expression_vOut13 abinAppArg2ExprIcopy abinAppArg2ExprIgraph abinAppArg2ExprIhasRecs abinAppArg2ExprImEntryId abinAppArg2ExprImExitId abinAppArg2ExprIppAg abinAppArg2ExprIppAgs abinAppArg2ExprIppDebug abinAppArg2ExprIppDebugs abinAppArg2ExprIrecNode) = inv_Expression_s14 st_binAppArg2ExprX14 (T_Expression_vIn13 abinAppArg2ExprOcaseExpr abinAppArg2ExprOcurrTaskName abinAppArg2ExprOgraph abinAppArg2ExprOmergeId abinAppArg2ExprOmoduleEnv)
                          (T_Expression_vOut13 aparBinAppArg2ExprIcopy aparBinAppArg2ExprIgraph aparBinAppArg2ExprIhasRecs aparBinAppArg2ExprImEntryId aparBinAppArg2ExprImExitId aparBinAppArg2ExprIppAg aparBinAppArg2ExprIppAgs aparBinAppArg2ExprIppDebug aparBinAppArg2ExprIppDebugs aparBinAppArg2ExprIrecNode) = inv_Expression_s14 st_parBinAppArg2ExprX14 (T_Expression_vIn13 aparBinAppArg2ExprOcaseExpr aparBinAppArg2ExprOcurrTaskName aparBinAppArg2ExprOgraph aparBinAppArg2ExprOmergeId aparBinAppArg2ExprOmoduleEnv)
                          alhsOreifyFunDef = rule0 aapp_symbIreifyFunDef
                          alhsOreifySymbolType = rule1 aapp_symbIreifySymbolType
                          lnoContextArgs = rule2 aapp_argsIcopy aapp_symbIident aapp_symbIreifySymbolType lisListApp
                          lisListApp = rule3 aapp_symbIident
                          alhsOisTask = rule4 lisTask
                          lisTask = rule5 aapp_symbIisTask
                          alhsOgraph = rule6 aapp_symbIcopy alhsIgraph alhsImoduleEnv ltaskGraph
                          alhsOmEntryId = rule7 ltaskEntryId
                          alhsOmExitId = rule8 ltaskExitId
                          (ltaskGraph,ltaskEntryId,ltaskExitId) = rule9 aapp_symbIident lassignGraph lassignId lbinAppGraph lbindGraph lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId
                          (lappArg1,lmAppArg2) = rule10 aapp_symbIident lnoContextArgs
                          appArg1Expr_val_ = rule11 lappArg1
                          appArg2Expr_val_ = rule12 lmAppArg2
                          bindRhsAppI_val_ = rule13 lmAppArg2
                          lbindRhsSymbolType = rule14 abindRhsAppIIreifySymbolType
                          bindRhsFunDef_val_ = rule15 abindRhsAppIIreifyFunDef
                          bindRhsSymbolTypeI_val_ = rule16 lbindRhsSymbolType
                          abindRhsFunDefOgraph = rule17 aappArg1ExprIgraph
                          lbindGraph = rule18 aappArg1ExprImEntryId aappArg1ExprImExitId abindRhsFunDefIfunArgs abindRhsFunDefIfunRhs abindRhsFunDefImEntryId abindRhsFunDefImExitId alhsIgraph alhsImoduleEnv lappArg1 lbindRhsSymbolType
                          (lreturnId,lreturnGraph) = rule19 alhsIgraph lnoContextArgs
                          binAppArg2Expr_val_ = rule20 lmAppArg2
                          abinAppArg2ExprOgraph = rule21 aappArg1ExprIgraph
                          lbinAppGraph = rule22 aappArg1ExprIgraph aappArg1ExprImEntryId aappArg1ExprImExitId abinAppArg2ExprImEntryId abinAppArg2ExprImExitId
                          (lassignId,lassignGraph) = rule23 aappArg1ExprImEntryId alhsIgraph
                          lstepGraph = rule24  Void
                          lstepEntryId = rule25  Void
                          lstepExitId = rule26  Void
                          parBinAppArg2Expr_val_ = rule27 lmAppArg2
                          aparBinAppArg2ExprOgraph = rule28 aappArg1ExprIgraph
                          lparBinAppGraph = rule29 aappArg1ExprImEntryId aappArg1ExprImExitId aparBinAppArg2ExprIgraph aparBinAppArg2ExprImEntryId aparBinAppArg2ExprImExitId
                          lparListAppGraph = rule30  Void
                          lparListAppEntryId = rule31  Void
                          lparListAppExitId = rule32  Void
                          (ltaskAppId,ltaskAppGraph) = rule33 aapp_argsIppAgs aapp_symbIident aapp_symbIisCurrTask alhsIgraph
                          alhsOppDebug = rule34 aapp_argsIppAgs aapp_symbIppAg
                          alhsOppAg = rule35 aapp_argsIppAgs aapp_symbIisInfix aapp_symbIppAg alhsImoduleEnv lcopy
                          alhsOhasRecs = rule36 aappArg1ExprIhasRecs aappArg2ExprIhasRecs aapp_argsIhasRecs aapp_symbIhasRecs abinAppArg2ExprIhasRecs abindRhsAppIIhasRecs abindRhsFunDefIhasRecs abindRhsSymbolTypeIIhasRecs aparBinAppArg2ExprIhasRecs
                          alhsOppAgs = rule37 aappArg1ExprIppAgs aappArg2ExprIppAgs aapp_argsIppAgs aapp_symbIppAgs abinAppArg2ExprIppAgs abindRhsAppIIppAgs abindRhsSymbolTypeIIppAgs aparBinAppArg2ExprIppAgs
                          alhsOppDebugs = rule38 aappArg1ExprIppDebugs aappArg2ExprIppDebugs aapp_argsIppDebugs aapp_symbIppDebugs abinAppArg2ExprIppDebugs abindRhsAppIIppDebugs abindRhsSymbolTypeIIppDebugs aparBinAppArg2ExprIppDebugs
                          alhsOrecNode = rule39 aappArg1ExprIrecNode aappArg2ExprIrecNode aapp_argsIrecNode aapp_symbIrecNode abinAppArg2ExprIrecNode abindRhsAppIIrecNode abindRhsFunDefIrecNode abindRhsSymbolTypeIIrecNode aparBinAppArg2ExprIrecNode
                          lcopy = rule40 aapp_argsIcopy aapp_symbIcopy arg_app_info_ptr_
                          alhsOcopy = rule41 lcopy
                          alhsOreifyFunType = rule42 abindRhsAppIIreifyFunType
                          aapp_symbOcaseExpr = rule43 alhsIcaseExpr
                          aapp_symbOcurrTaskName = rule44 alhsIcurrTaskName
                          aapp_symbOgraph = rule45 alhsIgraph
                          aapp_symbOmergeId = rule46 alhsImergeId
                          aapp_symbOmoduleEnv = rule47 alhsImoduleEnv
                          aapp_argsOcaseExpr = rule48 alhsIcaseExpr
                          aapp_argsOcurrTaskName = rule49 alhsIcurrTaskName
                          aapp_argsOgraph = rule50 aapp_symbIgraph
                          aapp_argsOmergeId = rule51 alhsImergeId
                          aapp_argsOmoduleEnv = rule52 alhsImoduleEnv
                          aappArg1ExprOcaseExpr = rule53 alhsIcaseExpr
                          aappArg1ExprOcurrTaskName = rule54 alhsIcurrTaskName
                          aappArg1ExprOgraph = rule55 aapp_argsIgraph
                          aappArg1ExprOmergeId = rule56 alhsImergeId
                          aappArg1ExprOmoduleEnv = rule57 alhsImoduleEnv
                          aappArg2ExprOcaseExpr = rule58 alhsIcaseExpr
                          aappArg2ExprOcurrTaskName = rule59 alhsIcurrTaskName
                          aappArg2ExprOgraph = rule60 aappArg1ExprIgraph
                          aappArg2ExprOmergeId = rule61 alhsImergeId
                          aappArg2ExprOmoduleEnv = rule62 alhsImoduleEnv
                          abindRhsAppIOcaseExpr = rule63 alhsIcaseExpr
                          abindRhsAppIOcurrTaskName = rule64 alhsIcurrTaskName
                          abindRhsAppIOgraph = rule65 aappArg2ExprIgraph
                          abindRhsAppIOmergeId = rule66 alhsImergeId
                          abindRhsAppIOmoduleEnv = rule67 alhsImoduleEnv
                          abindRhsFunDefOcaseExpr = rule68 alhsIcaseExpr
                          abindRhsFunDefOcurrTaskName = rule69 alhsIcurrTaskName
                          abindRhsFunDefOmergeId = rule70 alhsImergeId
                          abindRhsFunDefOmoduleEnv = rule71 alhsImoduleEnv
                          abindRhsSymbolTypeIOcaseExpr = rule72 alhsIcaseExpr
                          abindRhsSymbolTypeIOcurrTaskName = rule73 alhsIcurrTaskName
                          abindRhsSymbolTypeIOgraph = rule74 abindRhsFunDefIgraph
                          abindRhsSymbolTypeIOmergeId = rule75 alhsImergeId
                          abindRhsSymbolTypeIOmoduleEnv = rule76 alhsImoduleEnv
                          abinAppArg2ExprOcaseExpr = rule77 alhsIcaseExpr
                          abinAppArg2ExprOcurrTaskName = rule78 alhsIcurrTaskName
                          abinAppArg2ExprOmergeId = rule79 alhsImergeId
                          abinAppArg2ExprOmoduleEnv = rule80 alhsImoduleEnv
                          aparBinAppArg2ExprOcaseExpr = rule81 alhsIcaseExpr
                          aparBinAppArg2ExprOcurrTaskName = rule82 alhsIcurrTaskName
                          aparBinAppArg2ExprOmergeId = rule83 alhsImergeId
                          aparBinAppArg2ExprOmoduleEnv = rule84 alhsImoduleEnv
                          ag__result_ = T_App_vOut1 alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType
                      in ag__result_
        in C_App_s2 v1
   /*# LINE 79 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule0 ((aapp_symbIreifyFunDef)) =
                          /*# LINE 79 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          aapp_symbIreifyFunDef
                          /*# LINE 454 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 80 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule1 ((aapp_symbIreifySymbolType)) =
                              /*# LINE 80 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              aapp_symbIreifySymbolType
                              /*# LINE 459 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 82 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule2 ((aapp_argsIcopy)) ((aapp_symbIident)) ((aapp_symbIreifySymbolType)) lisListApp =
                            /*# LINE 82 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                            if lisListApp
                               aapp_argsIcopy
                              (let funTy  = fromMaybe (abort err) aapp_symbIreifySymbolType
                                   err    = "noContextArgs : failed to find symbol type for " +++ aapp_symbIident
                               in  dropContexts funTy aapp_argsIcopy)
                            /*# LINE 468 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 88 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule3 ((aapp_symbIident)) =
                        /*# LINE 88 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        aapp_symbIident == "_Cons" || aapp_symbIident == "_Nil"
                        /*# LINE 473 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 89 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule4 lisTask =
                        /*# LINE 89 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        lisTask
                        /*# LINE 478 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 90 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule5 ((aapp_symbIisTask)) =
                        /*# LINE 90 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        aapp_symbIisTask
                        /*# LINE 483 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 119 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule6 ((aapp_symbIcopy)) ((alhsIgraph)) ((alhsImoduleEnv)) ltaskGraph =
                    /*# LINE 119 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                    if (symbIdentIsTask alhsImoduleEnv aapp_symbIcopy)
                      ltaskGraph
                      alhsIgraph
                    /*# LINE 490 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 122 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule7 ltaskEntryId =
                       /*# LINE 122 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                       ltaskEntryId
                       /*# LINE 495 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 123 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule8 ltaskExitId =
                       /*# LINE 123 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                       ltaskExitId
                       /*# LINE 500 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 125 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule9 ((aapp_symbIident)) lassignGraph lassignId lbinAppGraph lbindGraph lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId =
                                                   /*# LINE 125 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                                   case aapp_symbIident of
                                                     ">>="       -> (lbindGraph    ,                    Nothing,                            Nothing)
                                                     "return"    -> (lreturnGraph    ,                  Just lreturnId    ,                 Just lreturnId    )
                                                     ">>|"       -> (lbinAppGraph     Nothing,          Nothing,                            Nothing)
                                                     "@:"        -> (lassignGraph    ,                  Just lassignId    ,                 Just lassignId    )
                                                     ">>*"       -> (lstepGraph    ,                    lstepEntryId    ,                   lstepExitId    )
                                                     "-||-"      -> (lparBinAppGraph     DisFirstBin,   Nothing,                            Nothing)
                                                     "||-"       -> (lparBinAppGraph     DisRight,      Nothing,                            Nothing)
                                                     "-||"       -> (lparBinAppGraph     DisLeft,       Nothing,                            Nothing)
                                                     "-&&-"      -> (lparBinAppGraph     ConPair,       Nothing,                            Nothing)
                                                     "anyTask"   -> (lparListAppGraph     DisFirstList, lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                                                     "allTasks"  -> (lparListAppGraph     ConAll,       lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                                                     _           -> (ltaskAppGraph    ,                 ltaskAppId    ,                     ltaskAppId    )
                                                   /*# LINE 517 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 139 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule10 ((aapp_symbIident)) lnoContextArgs =
                                  /*# LINE 139 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                  case lnoContextArgs     of
                                    [e1:e2:_]  -> (e1, Just e2)
                                    [e1:_]     -> (e1, Nothing)
                                    _          -> abort ("App has no args: " +++ aapp_symbIident)
                                  /*# LINE 525 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 145 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule11 lappArg1 =
                           /*# LINE 145 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                           lappArg1
                           /*# LINE 530 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 148 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule12 lmAppArg2 =
                           /*# LINE 148 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                           fromMaybe (abort "No second argument to app") lmAppArg2
                           /*# LINE 535 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 151 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule13 lmAppArg2 =
                           /*# LINE 151 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                           case lmAppArg2     of
                             Just (App a)  -> a
                             _             -> abort "Invalid bind"
                           /*# LINE 542 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 155 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule14 ((abindRhsAppIIreifySymbolType)) =
                                /*# LINE 155 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                fromMaybe (abort "mkGraphAlg #2: failed to find symbol type")
                                abindRhsAppIIreifySymbolType
                                /*# LINE 548 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 159 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule15 ((abindRhsAppIIreifyFunDef)) =
                             /*# LINE 159 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                             fromMaybe (abort "mkGraphAlg #1: failed to find function definition")
                             abindRhsAppIIreifyFunDef
                             /*# LINE 554 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 163 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule16 lbindRhsSymbolType =
                                  /*# LINE 163 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                  lbindRhsSymbolType
                                  /*# LINE 559 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 165 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule17 ((aappArg1ExprIgraph)) =
                              /*# LINE 165 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              aappArg1ExprIgraph
                              /*# LINE 564 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 167 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule18 ((aappArg1ExprImEntryId)) ((aappArg1ExprImExitId)) ((abindRhsFunDefIfunArgs)) ((abindRhsFunDefIfunRhs)) ((abindRhsFunDefImEntryId)) ((abindRhsFunDefImExitId)) ((alhsIgraph)) ((alhsImoduleEnv)) lappArg1 lbindRhsSymbolType =
                        /*# LINE 167 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        case ( aappArg1ExprImEntryId, aappArg1ExprImExitId
                             , abindRhsFunDefImEntryId, abindRhsFunDefImExitId) of
                          (Just _, Just lx, Just rn, Just _)
                             # patid = withHead freeVarName (abort "Invalid bind")
                                     $ [x \\ x <- dropContexts lbindRhsSymbolType     abindRhsFunDefIfunArgs | x.fv_def_level == -1]
                             = addEdge (mkEdge patid) (lx, rn) alhsIgraph
                          (_, lid, rid, _)        = edgeErr alhsImoduleEnv "bind edge" lid lappArg1     rid abindRhsFunDefIfunRhs
                        /*# LINE 575 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 175 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule19 ((alhsIgraph)) lnoContextArgs =
                                      /*# LINE 175 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                      let node   = GReturn $ withHead f (abort "Invalid return") lnoContextArgs
                                          f _ = GCleanExpression "(return)"
                                      in  addNode node alhsIgraph
                                      /*# LINE 582 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 184 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule20 lmAppArg2 =
                              /*# LINE 184 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              fromMaybe (abort "No second argument to app") lmAppArg2
                              /*# LINE 587 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 186 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule21 ((aappArg1ExprIgraph)) =
                               /*# LINE 186 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                               aappArg1ExprIgraph
                               /*# LINE 592 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 188 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule22 ((aappArg1ExprIgraph)) ((aappArg1ExprImEntryId)) ((aappArg1ExprImExitId)) ((abinAppArg2ExprImEntryId)) ((abinAppArg2ExprImExitId)) =
                          /*# LINE 188 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          \mPat -> case ( aappArg1ExprImEntryId, aappArg1ExprImExitId
                                        , abinAppArg2ExprImEntryId, abinAppArg2ExprImExitId) of
                                     (Just _, Just lx, Just rn, Just _)  -> addEdge (maybe emptyEdge mkEdge mPat) (lx, rn) aappArg1ExprIgraph
                                     _                                   -> abort "binAppGraph"
                          /*# LINE 600 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 193 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule23 ((aappArg1ExprImEntryId)) ((alhsIgraph)) =
                                      /*# LINE 193 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                      let (n, g) = addNode (GAssign "Assign node") alhsIgraph
                                      in  case aappArg1ExprImEntryId of
                                            Just r -> (n, addEmptyEdge (n, r) g)
                                            _      -> abort "Illegal task assignment"
                                      /*# LINE 608 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 198 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule24  (_) =
                        /*# LINE 198 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        abort "Step not implemented yet"
                        /*# LINE 613 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 199 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule25  (_) =
                          /*# LINE 199 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          Nothing
                          /*# LINE 618 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 200 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule26  (_) =
                         /*# LINE 200 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                         Nothing
                         /*# LINE 623 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 203 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule27 lmAppArg2 =
                                 /*# LINE 203 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                 fromMaybe (abort "No second argument to app") lmAppArg2
                                 /*# LINE 628 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 205 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule28 ((aappArg1ExprIgraph)) =
                                  /*# LINE 205 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                  aappArg1ExprIgraph
                                  /*# LINE 633 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 207 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule29 ((aappArg1ExprImEntryId)) ((aappArg1ExprImExitId)) ((aparBinAppArg2ExprIgraph)) ((aparBinAppArg2ExprImEntryId)) ((aparBinAppArg2ExprImExitId)) =
                             /*# LINE 207 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                             \join -> let (sid, g1) = addNode GParallelSplit aparBinAppArg2ExprIgraph
                                          (jid, g2) = addNode (GParallelJoin join) g1
                                      in  case ( aappArg1ExprImEntryId, aappArg1ExprImExitId
                                               , aparBinAppArg2ExprImEntryId, aparBinAppArg2ExprImExitId) of
                                            (_, Just l, Just r, _)
                                              # g = addEmptyEdge (sid, l) g2
                                              # g = addEmptyEdge (sid, r) g
                                              # g = addEmptyEdge (l, jid) g
                                              = addEmptyEdge (r, jid) g
                                            (_, lid, rid, _) = abort "Illegal parBinApp"
                             /*# LINE 647 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 218 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule30  (_) =
                                /*# LINE 218 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 652 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 219 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule31  (_) =
                                /*# LINE 219 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 657 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 220 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule32  (_) =
                                /*# LINE 220 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 662 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 222 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule33 ((aapp_argsIppAgs)) ((aapp_symbIident)) ((aapp_symbIisCurrTask)) ((alhsIgraph)) =
                                        /*# LINE 222 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                        if aapp_symbIisCurrTask
                                          (Nothing, alhsIgraph)
                                          (let appArgs = map (GCleanExpression o ppCompact) aapp_argsIppAgs
                                               (n, g)  = addNode (GTaskApp aapp_symbIident appArgs) alhsIgraph
                                           in (Just n, g))
                                        /*# LINE 671 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 63 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule34 ((aapp_argsIppAgs)) ((aapp_symbIppAg)) =
                      /*# LINE 63 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      let argsPP = hcat $ intersperse (text ", ") aapp_argsIppAgs
                      in  text "<App>" <+> aapp_symbIppAg <+> brackets argsPP
                      /*# LINE 677 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 66 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule35 ((aapp_argsIppAgs)) ((aapp_symbIisInfix)) ((aapp_symbIppAg)) ((alhsImoduleEnv)) lcopy =
                      /*# LINE 66 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      let appc      = lcopy
                      in  case appc.app_args of
                            []     -> aapp_symbIppAg
                            [x:xs] -> if aapp_symbIisInfix
                                        (ppExpression alhsImoduleEnv x <+> aapp_symbIppAg <+> hcat (intersperse (text " ") (map (ppExpression alhsImoduleEnv) xs)))
                                        (aapp_symbIppAg <+> hcat (intersperse (text " ") aapp_argsIppAgs))
                      /*# LINE 687 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule36 ((aappArg1ExprIhasRecs)) ((aappArg2ExprIhasRecs)) ((aapp_argsIhasRecs)) ((aapp_symbIhasRecs)) ((abinAppArg2ExprIhasRecs)) ((abindRhsAppIIhasRecs)) ((abindRhsFunDefIhasRecs)) ((abindRhsSymbolTypeIIhasRecs)) ((aparBinAppArg2ExprIhasRecs)) =
     aapp_symbIhasRecs || aapp_argsIhasRecs || aappArg1ExprIhasRecs || aappArg2ExprIhasRecs || abindRhsAppIIhasRecs || abindRhsFunDefIhasRecs || abindRhsSymbolTypeIIhasRecs || abinAppArg2ExprIhasRecs || aparBinAppArg2ExprIhasRecs
   rule37 ((aappArg1ExprIppAgs)) ((aappArg2ExprIppAgs)) ((aapp_argsIppAgs)) ((aapp_symbIppAgs)) ((abinAppArg2ExprIppAgs)) ((abindRhsAppIIppAgs)) ((abindRhsSymbolTypeIIppAgs)) ((aparBinAppArg2ExprIppAgs)) =
     aapp_symbIppAgs ++ aapp_argsIppAgs ++ aappArg1ExprIppAgs ++ aappArg2ExprIppAgs ++ abindRhsAppIIppAgs ++ abindRhsSymbolTypeIIppAgs ++ abinAppArg2ExprIppAgs ++ aparBinAppArg2ExprIppAgs
   rule38 ((aappArg1ExprIppDebugs)) ((aappArg2ExprIppDebugs)) ((aapp_argsIppDebugs)) ((aapp_symbIppDebugs)) ((abinAppArg2ExprIppDebugs)) ((abindRhsAppIIppDebugs)) ((abindRhsSymbolTypeIIppDebugs)) ((aparBinAppArg2ExprIppDebugs)) =
     aapp_symbIppDebugs ++ aapp_argsIppDebugs ++ aappArg1ExprIppDebugs ++ aappArg2ExprIppDebugs ++ abindRhsAppIIppDebugs ++ abindRhsSymbolTypeIIppDebugs ++ abinAppArg2ExprIppDebugs ++ aparBinAppArg2ExprIppDebugs
   rule39 ((aappArg1ExprIrecNode)) ((aappArg2ExprIrecNode)) ((aapp_argsIrecNode)) ((aapp_symbIrecNode)) ((abinAppArg2ExprIrecNode)) ((abindRhsAppIIrecNode)) ((abindRhsFunDefIrecNode)) ((abindRhsSymbolTypeIIrecNode)) ((aparBinAppArg2ExprIrecNode)) =
     aapp_symbIrecNode || aapp_argsIrecNode || aappArg1ExprIrecNode || aappArg2ExprIrecNode || abindRhsAppIIrecNode || abindRhsFunDefIrecNode || abindRhsSymbolTypeIIrecNode || abinAppArg2ExprIrecNode || aparBinAppArg2ExprIrecNode
   rule40 ((aapp_argsIcopy)) ((aapp_symbIcopy)) app_info_ptr_ =
     {App|app_symb = aapp_symbIcopy , app_args = aapp_argsIcopy , app_info_ptr = app_info_ptr_}
   rule41 lcopy =
     lcopy
   rule42 ((abindRhsAppIIreifyFunType)) =
     abindRhsAppIIreifyFunType
   rule43 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule44 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule45 ((alhsIgraph)) =
     alhsIgraph
   rule46 ((alhsImergeId)) =
     alhsImergeId
   rule47 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule48 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule49 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule50 ((aapp_symbIgraph)) =
     aapp_symbIgraph
   rule51 ((alhsImergeId)) =
     alhsImergeId
   rule52 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule53 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule54 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule55 ((aapp_argsIgraph)) =
     aapp_argsIgraph
   rule56 ((alhsImergeId)) =
     alhsImergeId
   rule57 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule58 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule59 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule60 ((aappArg1ExprIgraph)) =
     aappArg1ExprIgraph
   rule61 ((alhsImergeId)) =
     alhsImergeId
   rule62 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule63 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule64 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule65 ((aappArg2ExprIgraph)) =
     aappArg2ExprIgraph
   rule66 ((alhsImergeId)) =
     alhsImergeId
   rule67 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule68 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule69 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule70 ((alhsImergeId)) =
     alhsImergeId
   rule71 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule72 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule73 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule74 ((abindRhsFunDefIgraph)) =
     abindRhsFunDefIgraph
   rule75 ((alhsImergeId)) =
     alhsImergeId
   rule76 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule77 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule78 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule79 ((alhsImergeId)) =
     alhsImergeId
   rule80 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule81 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule82 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule83 ((alhsImergeId)) =
     alhsImergeId
   rule84 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// BasicValue --------------------------------------------------
// wrapper
moduleEnv_Inh_BasicValue :: Inh_BasicValue -> (ModuleEnv)
moduleEnv_Inh_BasicValue (Inh_BasicValue _ _ _ _ x) = x
mergeId_Inh_BasicValue :: Inh_BasicValue -> (Int)
mergeId_Inh_BasicValue (Inh_BasicValue _ _ _ x _) = x
graph_Inh_BasicValue :: Inh_BasicValue -> (GinGraph)
graph_Inh_BasicValue (Inh_BasicValue _ _ x _ _) = x
currTaskName_Inh_BasicValue :: Inh_BasicValue -> (String)
currTaskName_Inh_BasicValue (Inh_BasicValue _ x _ _ _) = x
caseExpr_Inh_BasicValue :: Inh_BasicValue -> (Maybe Expression)
caseExpr_Inh_BasicValue (Inh_BasicValue x _ _ _ _) = x
recNode_Syn_BasicValue :: Syn_BasicValue -> (Bool)
recNode_Syn_BasicValue (Syn_BasicValue _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_BasicValue :: Syn_BasicValue -> ([Doc])
ppDebugs_Syn_BasicValue (Syn_BasicValue _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_BasicValue :: Syn_BasicValue -> (Doc)
ppDebug_Syn_BasicValue (Syn_BasicValue _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_BasicValue :: Syn_BasicValue -> ([Doc])
ppAgs_Syn_BasicValue (Syn_BasicValue _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_BasicValue :: Syn_BasicValue -> (Doc)
ppAg_Syn_BasicValue (Syn_BasicValue _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_BasicValue :: Syn_BasicValue -> (Maybe Int)
mExitId_Syn_BasicValue (Syn_BasicValue _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_BasicValue :: Syn_BasicValue -> (Maybe Int)
mEntryId_Syn_BasicValue (Syn_BasicValue _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_BasicValue :: Syn_BasicValue -> (Bool)
hasRecs_Syn_BasicValue (Syn_BasicValue _ _ x _ _ _ _ _ _ _) = x
graph_Syn_BasicValue :: Syn_BasicValue -> (GinGraph)
graph_Syn_BasicValue (Syn_BasicValue _ x _ _ _ _ _ _ _ _) = x
copy_Syn_BasicValue :: Syn_BasicValue -> (BasicValue)
copy_Syn_BasicValue (Syn_BasicValue x _ _ _ _ _ _ _ _ _) = x
wrap_BasicValue :: T_BasicValue  Inh_BasicValue  -> (Syn_BasicValue )
wrap_BasicValue (T_BasicValue act) (Inh_BasicValue alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_BasicValue_s5 sem arg) >>= \ (T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_BasicValue alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_BasicValue :: BasicValue  -> T_BasicValue 
sem_BasicValue ( BVI str_ ) = sem_BasicValue_BVI str_
sem_BasicValue ( BVInt i_ ) = sem_BasicValue_BVInt i_
sem_BasicValue ( BVC str_ ) = sem_BasicValue_BVC str_
sem_BasicValue ( BVB b_ ) = sem_BasicValue_BVB b_
sem_BasicValue ( BVR str_ ) = sem_BasicValue_BVR str_
sem_BasicValue ( BVS str_ ) = sem_BasicValue_BVS str_

// semantic domain
attach_T_BasicValue (T_BasicValue t_BasicValue) = t_BasicValue
inv_BasicValue_s5 (C_BasicValue_s5 x) = x
sem_BasicValue_BVI  :: (String) -> T_BasicValue 
sem_BasicValue_BVI arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule85 arg_str_
                          alhsOppAg = rule86 arg_str_
                          alhsOhasRecs = rule87  Void
                          alhsOmEntryId = rule88  Void
                          alhsOmExitId = rule89  Void
                          alhsOppAgs = rule90  Void
                          alhsOppDebugs = rule91  Void
                          alhsOrecNode = rule92  Void
                          lcopy = rule93 arg_str_
                          alhsOcopy = rule94 lcopy
                          alhsOgraph = rule95 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 120 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule85 str_ =
                        /*# LINE 120 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 864 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 121 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule86 str_ =
                        /*# LINE 121 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 869 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule87  (_) =
     False
   rule88  (_) =
     Nothing
   rule89  (_) =
     Nothing
   rule90  (_) =
     []
   rule91  (_) =
     []
   rule92  (_) =
     False
   rule93 str_ =
     BVI str_
   rule94 lcopy =
     lcopy
   rule95 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVInt  :: (Int) -> T_BasicValue 
sem_BasicValue_BVInt arg_i_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule96 arg_i_
                          alhsOppAg = rule97 arg_i_
                          alhsOhasRecs = rule98  Void
                          alhsOmEntryId = rule99  Void
                          alhsOmExitId = rule100  Void
                          alhsOppAgs = rule101  Void
                          alhsOppDebugs = rule102  Void
                          alhsOrecNode = rule103  Void
                          lcopy = rule104 arg_i_
                          alhsOcopy = rule105 lcopy
                          alhsOgraph = rule106 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 122 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule96 i_ =
                          /*# LINE 122 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 912 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 123 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule97 i_ =
                          /*# LINE 123 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 917 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule98  (_) =
     False
   rule99  (_) =
     Nothing
   rule100  (_) =
     Nothing
   rule101  (_) =
     []
   rule102  (_) =
     []
   rule103  (_) =
     False
   rule104 i_ =
     BVInt i_
   rule105 lcopy =
     lcopy
   rule106 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVC  :: (String) -> T_BasicValue 
sem_BasicValue_BVC arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule107 arg_str_
                          alhsOppAg = rule108 arg_str_
                          alhsOhasRecs = rule109  Void
                          alhsOmEntryId = rule110  Void
                          alhsOmExitId = rule111  Void
                          alhsOppAgs = rule112  Void
                          alhsOppDebugs = rule113  Void
                          alhsOrecNode = rule114  Void
                          lcopy = rule115 arg_str_
                          alhsOcopy = rule116 lcopy
                          alhsOgraph = rule117 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 124 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule107 str_ =
                        /*# LINE 124 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 960 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 125 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule108 str_ =
                        /*# LINE 125 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 965 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule109  (_) =
     False
   rule110  (_) =
     Nothing
   rule111  (_) =
     Nothing
   rule112  (_) =
     []
   rule113  (_) =
     []
   rule114  (_) =
     False
   rule115 str_ =
     BVC str_
   rule116 lcopy =
     lcopy
   rule117 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVB  :: (Bool) -> T_BasicValue 
sem_BasicValue_BVB arg_b_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule118 arg_b_
                          alhsOppAg = rule119 arg_b_
                          alhsOhasRecs = rule120  Void
                          alhsOmEntryId = rule121  Void
                          alhsOmExitId = rule122  Void
                          alhsOppAgs = rule123  Void
                          alhsOppDebugs = rule124  Void
                          alhsOrecNode = rule125  Void
                          lcopy = rule126 arg_b_
                          alhsOcopy = rule127 lcopy
                          alhsOgraph = rule128 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 126 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule118 b_ =
                        /*# LINE 126 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 1008 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 127 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule119 b_ =
                        /*# LINE 127 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 1013 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule120  (_) =
     False
   rule121  (_) =
     Nothing
   rule122  (_) =
     Nothing
   rule123  (_) =
     []
   rule124  (_) =
     []
   rule125  (_) =
     False
   rule126 b_ =
     BVB b_
   rule127 lcopy =
     lcopy
   rule128 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVR  :: (String) -> T_BasicValue 
sem_BasicValue_BVR arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule129 arg_str_
                          alhsOppAg = rule130 arg_str_
                          alhsOhasRecs = rule131  Void
                          alhsOmEntryId = rule132  Void
                          alhsOmExitId = rule133  Void
                          alhsOppAgs = rule134  Void
                          alhsOppDebugs = rule135  Void
                          alhsOrecNode = rule136  Void
                          lcopy = rule137 arg_str_
                          alhsOcopy = rule138 lcopy
                          alhsOgraph = rule139 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 128 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule129 str_ =
                        /*# LINE 128 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1056 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 129 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule130 str_ =
                        /*# LINE 129 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1061 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule131  (_) =
     False
   rule132  (_) =
     Nothing
   rule133  (_) =
     Nothing
   rule134  (_) =
     []
   rule135  (_) =
     []
   rule136  (_) =
     False
   rule137 str_ =
     BVR str_
   rule138 lcopy =
     lcopy
   rule139 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVS  :: (String) -> T_BasicValue 
sem_BasicValue_BVS arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule140 arg_str_
                          alhsOppAg = rule141 arg_str_
                          alhsOhasRecs = rule142  Void
                          alhsOmEntryId = rule143  Void
                          alhsOmExitId = rule144  Void
                          alhsOppAgs = rule145  Void
                          alhsOppDebugs = rule146  Void
                          alhsOrecNode = rule147  Void
                          lcopy = rule148 arg_str_
                          alhsOcopy = rule149 lcopy
                          alhsOgraph = rule150 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 130 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule140 str_ =
                        /*# LINE 130 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1104 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 131 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule141 str_ =
                        /*# LINE 131 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1109 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule142  (_) =
     False
   rule143  (_) =
     Nothing
   rule144  (_) =
     Nothing
   rule145  (_) =
     []
   rule146  (_) =
     []
   rule147  (_) =
     False
   rule148 str_ =
     BVS str_
   rule149 lcopy =
     lcopy
   rule150 ((alhsIgraph)) =
     alhsIgraph

// BoundVar ----------------------------------------------------
// wrapper
moduleEnv_Inh_BoundVar :: Inh_BoundVar -> (ModuleEnv)
moduleEnv_Inh_BoundVar (Inh_BoundVar _ _ _ _ x) = x
mergeId_Inh_BoundVar :: Inh_BoundVar -> (Int)
mergeId_Inh_BoundVar (Inh_BoundVar _ _ _ x _) = x
graph_Inh_BoundVar :: Inh_BoundVar -> (GinGraph)
graph_Inh_BoundVar (Inh_BoundVar _ _ x _ _) = x
currTaskName_Inh_BoundVar :: Inh_BoundVar -> (String)
currTaskName_Inh_BoundVar (Inh_BoundVar _ x _ _ _) = x
caseExpr_Inh_BoundVar :: Inh_BoundVar -> (Maybe Expression)
caseExpr_Inh_BoundVar (Inh_BoundVar x _ _ _ _) = x
recNode_Syn_BoundVar :: Syn_BoundVar -> (Bool)
recNode_Syn_BoundVar (Syn_BoundVar _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_BoundVar :: Syn_BoundVar -> ([Doc])
ppDebugs_Syn_BoundVar (Syn_BoundVar _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_BoundVar :: Syn_BoundVar -> (Doc)
ppDebug_Syn_BoundVar (Syn_BoundVar _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_BoundVar :: Syn_BoundVar -> ([Doc])
ppAgs_Syn_BoundVar (Syn_BoundVar _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_BoundVar :: Syn_BoundVar -> (Doc)
ppAg_Syn_BoundVar (Syn_BoundVar _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_BoundVar :: Syn_BoundVar -> (Maybe Int)
mExitId_Syn_BoundVar (Syn_BoundVar _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_BoundVar :: Syn_BoundVar -> (Maybe Int)
mEntryId_Syn_BoundVar (Syn_BoundVar _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_BoundVar :: Syn_BoundVar -> (Bool)
hasRecs_Syn_BoundVar (Syn_BoundVar _ _ x _ _ _ _ _ _ _) = x
graph_Syn_BoundVar :: Syn_BoundVar -> (GinGraph)
graph_Syn_BoundVar (Syn_BoundVar _ x _ _ _ _ _ _ _ _) = x
copy_Syn_BoundVar :: Syn_BoundVar -> (BoundVar)
copy_Syn_BoundVar (Syn_BoundVar x _ _ _ _ _ _ _ _ _) = x
wrap_BoundVar :: T_BoundVar  Inh_BoundVar  -> (Syn_BoundVar )
wrap_BoundVar (T_BoundVar act) (Inh_BoundVar alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_BoundVar_vIn7 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_BoundVar_s8 sem arg) >>= \ (T_BoundVar_vOut7 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_BoundVar alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_BoundVar :: BoundVar  -> T_BoundVar 
sem_BoundVar { BoundVar | var_ident = var_ident_,var_info_ptr = var_info_ptr_,var_expr_ptr = var_expr_ptr_ } = sem_BoundVar_BoundVar ( sem_Ident var_ident_ ) var_info_ptr_ var_expr_ptr_

// semantic domain
attach_T_BoundVar (T_BoundVar t_BoundVar) = t_BoundVar
inv_BoundVar_s8 (C_BoundVar_s8 x) = x
sem_BoundVar_BoundVar  :: (T_Ident ) (VarInfoPtr) (ExprInfoPtr) -> T_BoundVar 
sem_BoundVar_BoundVar arg_var_ident_ arg_var_info_ptr_ arg_var_expr_ptr_ = T_BoundVar (lift st8) where
   st8 =
        let
            v7 (T_BoundVar_vIn7 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          st_var_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_var_ident_))
                          (T_Ident_vOut43 avar_identIcopy avar_identIgraph avar_identIhasRecs avar_identIident avar_identIisTask avar_identImEntryId avar_identImExitId avar_identIppAg avar_identIppAgs avar_identIppDebug avar_identIppDebugs avar_identIrecNode avar_identIreifyFunDef avar_identIreifyFunType avar_identIreifySymbolType) = inv_Ident_s44 st_var_identX44 (T_Ident_vIn43 avar_identOcaseExpr avar_identOcurrTaskName avar_identOgraph avar_identOmergeId avar_identOmoduleEnv)
                          alhsOppDebug = rule151 avar_identIppDebug
                          alhsOppAg = rule152 avar_identIppAg
                          alhsOhasRecs = rule153 avar_identIhasRecs
                          alhsOmEntryId = rule154 avar_identImEntryId
                          alhsOmExitId = rule155 avar_identImExitId
                          alhsOppAgs = rule156 avar_identIppAgs
                          alhsOppDebugs = rule157 avar_identIppDebugs
                          alhsOrecNode = rule158 avar_identIrecNode
                          lcopy = rule159 avar_identIcopy arg_var_expr_ptr_ arg_var_info_ptr_
                          alhsOcopy = rule160 lcopy
                          alhsOgraph = rule161 avar_identIgraph
                          avar_identOcaseExpr = rule162 alhsIcaseExpr
                          avar_identOcurrTaskName = rule163 alhsIcurrTaskName
                          avar_identOgraph = rule164 alhsIgraph
                          avar_identOmergeId = rule165 alhsImergeId
                          avar_identOmoduleEnv = rule166 alhsImoduleEnv
                          ag__result_ = T_BoundVar_vOut7 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BoundVar_s8 v7
   /*# LINE 108 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule151 ((avar_identIppDebug)) =
                             /*# LINE 108 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                             avar_identIppDebug
                             /*# LINE 1208 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 109 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule152 ((avar_identIppAg)) =
                             /*# LINE 109 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                             avar_identIppAg
                             /*# LINE 1213 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule153 ((avar_identIhasRecs)) =
     avar_identIhasRecs
   rule154 ((avar_identImEntryId)) =
     avar_identImEntryId
   rule155 ((avar_identImExitId)) =
     avar_identImExitId
   rule156 ((avar_identIppAgs)) =
     avar_identIppAgs
   rule157 ((avar_identIppDebugs)) =
     avar_identIppDebugs
   rule158 ((avar_identIrecNode)) =
     avar_identIrecNode
   rule159 ((avar_identIcopy)) var_expr_ptr_ var_info_ptr_ =
     {BoundVar|var_ident = avar_identIcopy , var_info_ptr = var_info_ptr_ , var_expr_ptr = var_expr_ptr_}
   rule160 lcopy =
     lcopy
   rule161 ((avar_identIgraph)) =
     avar_identIgraph
   rule162 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule163 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule164 ((alhsIgraph)) =
     alhsIgraph
   rule165 ((alhsImergeId)) =
     alhsImergeId
   rule166 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// DefinedSymbol -----------------------------------------------
// wrapper
moduleEnv_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (ModuleEnv)
moduleEnv_Inh_DefinedSymbol (Inh_DefinedSymbol _ _ _ _ x) = x
mergeId_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (Int)
mergeId_Inh_DefinedSymbol (Inh_DefinedSymbol _ _ _ x _) = x
graph_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (GinGraph)
graph_Inh_DefinedSymbol (Inh_DefinedSymbol _ _ x _ _) = x
currTaskName_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (String)
currTaskName_Inh_DefinedSymbol (Inh_DefinedSymbol _ x _ _ _) = x
caseExpr_Inh_DefinedSymbol :: Inh_DefinedSymbol -> (Maybe Expression)
caseExpr_Inh_DefinedSymbol (Inh_DefinedSymbol x _ _ _ _) = x
recNode_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Bool)
recNode_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> ([Doc])
ppDebugs_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Doc)
ppDebug_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> ([Doc])
ppAgs_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Doc)
ppAg_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Maybe Int)
mExitId_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Maybe Int)
mEntryId_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (Bool)
hasRecs_Syn_DefinedSymbol (Syn_DefinedSymbol _ _ x _ _ _ _ _ _ _) = x
graph_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (GinGraph)
graph_Syn_DefinedSymbol (Syn_DefinedSymbol _ x _ _ _ _ _ _ _ _) = x
copy_Syn_DefinedSymbol :: Syn_DefinedSymbol -> (DefinedSymbol)
copy_Syn_DefinedSymbol (Syn_DefinedSymbol x _ _ _ _ _ _ _ _ _) = x
wrap_DefinedSymbol :: T_DefinedSymbol  Inh_DefinedSymbol  -> (Syn_DefinedSymbol )
wrap_DefinedSymbol (T_DefinedSymbol act) (Inh_DefinedSymbol alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_DefinedSymbol_vIn10 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_DefinedSymbol_s11 sem arg) >>= \ (T_DefinedSymbol_vOut10 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_DefinedSymbol alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_DefinedSymbol :: DefinedSymbol  -> T_DefinedSymbol 
sem_DefinedSymbol { DefinedSymbol | ds_ident = ds_ident_,ds_arity = ds_arity_,ds_index = ds_index_ } = sem_DefinedSymbol_DefinedSymbol ( sem_Ident ds_ident_ ) ds_arity_ ds_index_

// semantic domain
attach_T_DefinedSymbol (T_DefinedSymbol t_DefinedSymbol) = t_DefinedSymbol
inv_DefinedSymbol_s11 (C_DefinedSymbol_s11 x) = x
sem_DefinedSymbol_DefinedSymbol  :: (T_Ident ) (Int) (Index) -> T_DefinedSymbol 
sem_DefinedSymbol_DefinedSymbol arg_ds_ident_ arg_ds_arity_ arg_ds_index_ = T_DefinedSymbol (lift st11) where
   st11 =
         let
             v10 (T_DefinedSymbol_vIn10 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_ds_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ds_ident_))
                           (T_Ident_vOut43 ads_identIcopy ads_identIgraph ads_identIhasRecs ads_identIident ads_identIisTask ads_identImEntryId ads_identImExitId ads_identIppAg ads_identIppAgs ads_identIppDebug ads_identIppDebugs ads_identIrecNode ads_identIreifyFunDef ads_identIreifyFunType ads_identIreifySymbolType) = inv_Ident_s44 st_ds_identX44 (T_Ident_vIn43 ads_identOcaseExpr ads_identOcurrTaskName ads_identOgraph ads_identOmergeId ads_identOmoduleEnv)
                           alhsOppDebug = rule167 ads_identIppDebug
                           alhsOppAg = rule168 ads_identIppAg
                           alhsOhasRecs = rule169 ads_identIhasRecs
                           alhsOmEntryId = rule170 ads_identImEntryId
                           alhsOmExitId = rule171 ads_identImExitId
                           alhsOppAgs = rule172 ads_identIppAgs
                           alhsOppDebugs = rule173 ads_identIppDebugs
                           alhsOrecNode = rule174 ads_identIrecNode
                           lcopy = rule175 ads_identIcopy arg_ds_arity_ arg_ds_index_
                           alhsOcopy = rule176 lcopy
                           alhsOgraph = rule177 ads_identIgraph
                           ads_identOcaseExpr = rule178 alhsIcaseExpr
                           ads_identOcurrTaskName = rule179 alhsIcurrTaskName
                           ads_identOgraph = rule180 alhsIgraph
                           ads_identOmergeId = rule181 alhsImergeId
                           ads_identOmoduleEnv = rule182 alhsImoduleEnv
                           ag__result_ = T_DefinedSymbol_vOut10 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_DefinedSymbol_s11 v10
   /*# LINE 134 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule167 ((ads_identIppDebug)) =
                                  /*# LINE 134 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppDebug
                                  /*# LINE 1322 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 135 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule168 ((ads_identIppAg)) =
                                  /*# LINE 135 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppAg
                                  /*# LINE 1327 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule169 ((ads_identIhasRecs)) =
     ads_identIhasRecs
   rule170 ((ads_identImEntryId)) =
     ads_identImEntryId
   rule171 ((ads_identImExitId)) =
     ads_identImExitId
   rule172 ((ads_identIppAgs)) =
     ads_identIppAgs
   rule173 ((ads_identIppDebugs)) =
     ads_identIppDebugs
   rule174 ((ads_identIrecNode)) =
     ads_identIrecNode
   rule175 ((ads_identIcopy)) ds_arity_ ds_index_ =
     {DefinedSymbol|ds_ident = ads_identIcopy , ds_arity = ds_arity_ , ds_index = ds_index_}
   rule176 lcopy =
     lcopy
   rule177 ((ads_identIgraph)) =
     ads_identIgraph
   rule178 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule179 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule180 ((alhsIgraph)) =
     alhsIgraph
   rule181 ((alhsImergeId)) =
     alhsImergeId
   rule182 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// Expression --------------------------------------------------
// wrapper
moduleEnv_Inh_Expression :: Inh_Expression -> (ModuleEnv)
moduleEnv_Inh_Expression (Inh_Expression _ _ _ _ x) = x
mergeId_Inh_Expression :: Inh_Expression -> (Int)
mergeId_Inh_Expression (Inh_Expression _ _ _ x _) = x
graph_Inh_Expression :: Inh_Expression -> (GinGraph)
graph_Inh_Expression (Inh_Expression _ _ x _ _) = x
currTaskName_Inh_Expression :: Inh_Expression -> (String)
currTaskName_Inh_Expression (Inh_Expression _ x _ _ _) = x
caseExpr_Inh_Expression :: Inh_Expression -> (Maybe Expression)
caseExpr_Inh_Expression (Inh_Expression x _ _ _ _) = x
recNode_Syn_Expression :: Syn_Expression -> (Bool)
recNode_Syn_Expression (Syn_Expression _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Expression :: Syn_Expression -> ([Doc])
ppDebugs_Syn_Expression (Syn_Expression _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppDebug_Syn_Expression (Syn_Expression _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Expression :: Syn_Expression -> ([Doc])
ppAgs_Syn_Expression (Syn_Expression _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Expression :: Syn_Expression -> (Doc)
ppAg_Syn_Expression (Syn_Expression _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Expression :: Syn_Expression -> (Maybe Int)
mExitId_Syn_Expression (Syn_Expression _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Expression :: Syn_Expression -> (Maybe Int)
mEntryId_Syn_Expression (Syn_Expression _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_Expression :: Syn_Expression -> (Bool)
hasRecs_Syn_Expression (Syn_Expression _ _ x _ _ _ _ _ _ _) = x
graph_Syn_Expression :: Syn_Expression -> (GinGraph)
graph_Syn_Expression (Syn_Expression _ x _ _ _ _ _ _ _ _) = x
copy_Syn_Expression :: Syn_Expression -> (Expression)
copy_Syn_Expression (Syn_Expression x _ _ _ _ _ _ _ _ _) = x
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expression_s14 sem arg) >>= \ (T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Expression alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Var bv_ ) = sem_Expression_Var ( sem_BoundVar bv_ )
sem_Expression ( App app_ ) = sem_Expression_App ( sem_App app_ )
sem_Expression ( At expr_ exprs_ ) = sem_Expression_At ( sem_Expression expr_ ) ( sem_Expressions exprs_ )
sem_Expression ( Let let__  ) = sem_Expression_Let let__ 
sem_Expression ( Case case__ ) = sem_Expression_Case case__
sem_Expression ( Selection skind_ expr_ sels_ ) = sem_Expression_Selection skind_ ( sem_Expression expr_ ) ( sem_Selections sels_ )
sem_Expression ( Update exprl_ sels_ exprr_ ) = sem_Expression_Update ( sem_Expression exprl_ ) ( sem_Selections sels_ ) ( sem_Expression exprr_ )
sem_Expression ( RecordUpdate gdsym_ expr_ binds_ ) = sem_Expression_RecordUpdate ( sem_GlobalDefinedSymbol gdsym_ ) ( sem_Expression expr_ ) binds_
sem_Expression ( TupleSelect dsym_ n_ expr_ ) = sem_Expression_TupleSelect ( sem_DefinedSymbol dsym_ ) n_ ( sem_Expression expr_ )
sem_Expression ( BasicExpr bv_ ) = sem_Expression_BasicExpr ( sem_BasicValue bv_ )
sem_Expression ( Conditional cond_ ) = sem_Expression_Conditional cond_
sem_Expression ( AnyCodeExpr cbbv_ cbfv_ ss_ ) = sem_Expression_AnyCodeExpr cbbv_ cbfv_ ss_
sem_Expression ( ABCCodeExpr ss_ bl_ ) = sem_Expression_ABCCodeExpr ss_ bl_
sem_Expression ( MatchExpr gdfs_ expr_ ) = sem_Expression_MatchExpr gdfs_ ( sem_Expression expr_ )
sem_Expression ( IsConstructor expr_ gdfs_ arity_ gidx_ ident_ pos_ ) = sem_Expression_IsConstructor ( sem_Expression expr_ ) ( sem_GlobalDefinedSymbol gdfs_ ) arity_ gidx_ ident_ pos_
sem_Expression ( FreeVar fv_ ) = sem_Expression_FreeVar ( sem_FreeVar fv_ )
sem_Expression ( DictionariesFunction fvat_ expr_ aty_ ) = sem_Expression_DictionariesFunction fvat_ ( sem_Expression expr_ ) aty_
sem_Expression ( Constant symid_ n_ prio_ ) = sem_Expression_Constant ( sem_SymbIdent symid_ ) n_ prio_
sem_Expression ( ClassVariable varinfptr_ ) = sem_Expression_ClassVariable varinfptr_
sem_Expression ( DynamicExpr dynexpr_ ) = sem_Expression_DynamicExpr dynexpr_
sem_Expression ( TypeCodeExpression tycodeexpr_ ) = sem_Expression_TypeCodeExpression tycodeexpr_
sem_Expression ( TypeSignature sigfun_ expr_ ) = sem_Expression_TypeSignature sigfun_ ( sem_Expression expr_ )
sem_Expression ( EE  ) = sem_Expression_EE 
sem_Expression ( NoBind exprinfoptr_ ) = sem_Expression_NoBind exprinfoptr_
sem_Expression ( FailExpr ident_ ) = sem_Expression_FailExpr ( sem_Ident ident_ )

// semantic domain
attach_T_Expression (T_Expression t_Expression) = t_Expression
inv_Expression_s14 (C_Expression_s14 x) = x
sem_Expression_Var  :: (T_BoundVar ) -> T_Expression 
sem_Expression_Var arg_bv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_bvX8 = 'Control.Monad.Identity'.runIdentity (attach_T_BoundVar (arg_bv_))
                           (T_BoundVar_vOut7 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BoundVar_s8 st_bvX8 (T_BoundVar_vIn7 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           alhsOppDebug = rule183 abvIppDebug
                           alhsOppAg = rule184 abvIppAg
                           alhsOhasRecs = rule185 abvIhasRecs
                           alhsOmEntryId = rule186 abvImEntryId
                           alhsOmExitId = rule187 abvImExitId
                           alhsOppAgs = rule188 abvIppAgs
                           alhsOppDebugs = rule189 abvIppDebugs
                           alhsOrecNode = rule190 abvIrecNode
                           lcopy = rule191 abvIcopy
                           alhsOcopy = rule192 lcopy
                           alhsOgraph = rule193 abvIgraph
                           abvOcaseExpr = rule194 alhsIcaseExpr
                           abvOcurrTaskName = rule195 alhsIcurrTaskName
                           abvOgraph = rule196 alhsIgraph
                           abvOmergeId = rule197 alhsImergeId
                           abvOmoduleEnv = rule198 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 75 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule183 ((abvIppDebug)) =
                      /*# LINE 75 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<Var>" <+> abvIppDebug
                      /*# LINE 1460 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 76 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule184 ((abvIppAg)) =
                      /*# LINE 76 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 1465 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule185 ((abvIhasRecs)) =
     abvIhasRecs
   rule186 ((abvImEntryId)) =
     abvImEntryId
   rule187 ((abvImExitId)) =
     abvImExitId
   rule188 ((abvIppAgs)) =
     abvIppAgs
   rule189 ((abvIppDebugs)) =
     abvIppDebugs
   rule190 ((abvIrecNode)) =
     abvIrecNode
   rule191 ((abvIcopy)) =
     Var abvIcopy
   rule192 lcopy =
     lcopy
   rule193 ((abvIgraph)) =
     abvIgraph
   rule194 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule195 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule196 ((alhsIgraph)) =
     alhsIgraph
   rule197 ((alhsImergeId)) =
     alhsImergeId
   rule198 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_App  :: (T_App ) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_appX2 = 'Control.Monad.Identity'.runIdentity (attach_T_App (arg_app_))
                           (T_App_vOut1 aappIcopy aappIgraph aappIhasRecs aappIisTask aappImEntryId aappImExitId aappIppAg aappIppAgs aappIppDebug aappIppDebugs aappIrecNode aappIreifyFunDef aappIreifyFunType aappIreifySymbolType) = inv_App_s2 st_appX2 (T_App_vIn1 aappOcaseExpr aappOcurrTaskName aappOgraph aappOmergeId aappOmoduleEnv)
                           alhsOgraph = rule199 aappIgraph
                           alhsOppDebug = rule200 aappIppDebug
                           alhsOppAg = rule201 aappIppAg
                           alhsOhasRecs = rule202 aappIhasRecs
                           alhsOmEntryId = rule203 aappImEntryId
                           alhsOmExitId = rule204 aappImExitId
                           alhsOppAgs = rule205 aappIppAgs
                           alhsOppDebugs = rule206 aappIppDebugs
                           alhsOrecNode = rule207 aappIrecNode
                           lcopy = rule208 aappIcopy
                           alhsOcopy = rule209 lcopy
                           aappOcaseExpr = rule210 alhsIcaseExpr
                           aappOcurrTaskName = rule211 alhsIcurrTaskName
                           aappOgraph = rule212 alhsIgraph
                           aappOmergeId = rule213 alhsImergeId
                           aappOmoduleEnv = rule214 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 230 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule199 ((aappIgraph)) =
                    /*# LINE 230 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                    aappIgraph
                    /*# LINE 1525 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 78 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule200 ((aappIppDebug)) =
                        /*# LINE 78 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        aappIppDebug
                        /*# LINE 1530 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 79 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule201 ((aappIppAg)) =
                        /*# LINE 79 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                        aappIppAg
                        /*# LINE 1535 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule202 ((aappIhasRecs)) =
     aappIhasRecs
   rule203 ((aappImEntryId)) =
     aappImEntryId
   rule204 ((aappImExitId)) =
     aappImExitId
   rule205 ((aappIppAgs)) =
     aappIppAgs
   rule206 ((aappIppDebugs)) =
     aappIppDebugs
   rule207 ((aappIrecNode)) =
     aappIrecNode
   rule208 ((aappIcopy)) =
     App aappIcopy
   rule209 lcopy =
     lcopy
   rule210 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule211 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule212 ((alhsIgraph)) =
     alhsIgraph
   rule213 ((alhsImergeId)) =
     alhsImergeId
   rule214 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_At arg_expr_ arg_exprs_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_exprsX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_exprs_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_Expressions_vOut16 aexprsIcopy aexprsIgraph aexprsIhasRecs aexprsImEntryId aexprsImExitId aexprsIppAg aexprsIppAgs aexprsIppDebug aexprsIppDebugs aexprsIrecNode) = inv_Expressions_s17 st_exprsX17 (T_Expressions_vIn16 aexprsOcaseExpr aexprsOcurrTaskName aexprsOgraph aexprsOmergeId aexprsOmoduleEnv)
                           alhsOhasRecs = rule215 aexprIhasRecs aexprsIhasRecs
                           alhsOmEntryId = rule216 aexprImEntryId aexprsImEntryId
                           alhsOmExitId = rule217 aexprImExitId aexprsImExitId
                           alhsOppAg = rule218 aexprIppAg aexprsIppAg
                           alhsOppAgs = rule219 aexprIppAgs aexprsIppAgs
                           alhsOppDebug = rule220 aexprIppDebug aexprsIppDebug
                           alhsOppDebugs = rule221 aexprIppDebugs aexprsIppDebugs
                           alhsOrecNode = rule222 aexprIrecNode aexprsIrecNode
                           lcopy = rule223 aexprIcopy aexprsIcopy
                           alhsOcopy = rule224 lcopy
                           alhsOgraph = rule225 aexprsIgraph
                           aexprOcaseExpr = rule226 alhsIcaseExpr
                           aexprOcurrTaskName = rule227 alhsIcurrTaskName
                           aexprOgraph = rule228 alhsIgraph
                           aexprOmergeId = rule229 alhsImergeId
                           aexprOmoduleEnv = rule230 alhsImoduleEnv
                           aexprsOcaseExpr = rule231 alhsIcaseExpr
                           aexprsOcurrTaskName = rule232 alhsIcurrTaskName
                           aexprsOgraph = rule233 aexprIgraph
                           aexprsOmergeId = rule234 alhsImergeId
                           aexprsOmoduleEnv = rule235 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule215 ((aexprIhasRecs)) ((aexprsIhasRecs)) =
     aexprIhasRecs || aexprsIhasRecs
   rule216 ((aexprImEntryId)) ((aexprsImEntryId)) =
     aexprImEntryId <> aexprsImEntryId
   rule217 ((aexprImExitId)) ((aexprsImExitId)) =
     aexprImExitId <> aexprsImExitId
   rule218 ((aexprIppAg)) ((aexprsIppAg)) =
     aexprIppAg <$$> aexprsIppAg
   rule219 ((aexprIppAgs)) ((aexprsIppAgs)) =
     aexprIppAgs ++ aexprsIppAgs
   rule220 ((aexprIppDebug)) ((aexprsIppDebug)) =
     aexprIppDebug <$$> aexprsIppDebug
   rule221 ((aexprIppDebugs)) ((aexprsIppDebugs)) =
     aexprIppDebugs ++ aexprsIppDebugs
   rule222 ((aexprIrecNode)) ((aexprsIrecNode)) =
     aexprIrecNode || aexprsIrecNode
   rule223 ((aexprIcopy)) ((aexprsIcopy)) =
     At aexprIcopy aexprsIcopy
   rule224 lcopy =
     lcopy
   rule225 ((aexprsIgraph)) =
     aexprsIgraph
   rule226 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule227 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule228 ((alhsIgraph)) =
     alhsIgraph
   rule229 ((alhsImergeId)) =
     alhsImergeId
   rule230 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule231 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule232 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule233 ((aexprIgraph)) =
     aexprIgraph
   rule234 ((alhsImergeId)) =
     alhsImergeId
   rule235 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Let arg_let__  = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gletX32 = 'Control.Monad.Identity'.runIdentity (attach_T_GLet ((sem_GLet glet_val_)))
                           (T_GLet_vOut31 agletIcopy agletIgraph agletIhasRecs agletImEntryId agletImExitId agletIppAg agletIppAgs agletIppDebug agletIppDebugs agletIrecNode) = inv_GLet_s32 st_gletX32 (T_GLet_vIn31 agletOcaseExpr agletOcurrTaskName agletOgraph agletOmergeId agletOmoduleEnv)
                           alhsOgraph = rule236 agletIgraph
                           glet_val_ = rule237 alhsImoduleEnv arg_let__
                           alhsOhasRecs = rule238 agletIhasRecs
                           alhsOmEntryId = rule239 agletImEntryId
                           alhsOmExitId = rule240 agletImExitId
                           alhsOppAg = rule241 agletIppAg
                           alhsOppAgs = rule242 agletIppAgs
                           alhsOppDebug = rule243 agletIppDebug
                           alhsOppDebugs = rule244 agletIppDebugs
                           alhsOrecNode = rule245 agletIrecNode
                           lcopy = rule246 arg_let__
                           alhsOcopy = rule247 lcopy
                           agletOcaseExpr = rule248 alhsIcaseExpr
                           agletOcurrTaskName = rule249 alhsIcurrTaskName
                           agletOgraph = rule250 alhsIgraph
                           agletOmergeId = rule251 alhsImergeId
                           agletOmoduleEnv = rule252 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 233 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule236 ((agletIgraph)) =
                    /*# LINE 233 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                    agletIgraph
                    /*# LINE 1670 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 236 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule237 ((alhsImoduleEnv)) let__ =
                    /*# LINE 236 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                    mkGLet alhsImoduleEnv let__
                    /*# LINE 1675 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule238 ((agletIhasRecs)) =
     agletIhasRecs
   rule239 ((agletImEntryId)) =
     agletImEntryId
   rule240 ((agletImExitId)) =
     agletImExitId
   rule241 ((agletIppAg)) =
     agletIppAg
   rule242 ((agletIppAgs)) =
     agletIppAgs
   rule243 ((agletIppDebug)) =
     agletIppDebug
   rule244 ((agletIppDebugs)) =
     agletIppDebugs
   rule245 ((agletIrecNode)) =
     agletIrecNode
   rule246 let__ =
     Let let__
   rule247 lcopy =
     lcopy
   rule248 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule249 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule250 ((alhsIgraph)) =
     alhsIgraph
   rule251 ((alhsImergeId)) =
     alhsImergeId
   rule252 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Case arg_case__ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule253  Void
                           alhsOmEntryId = rule254  Void
                           alhsOmExitId = rule255  Void
                           alhsOppAg = rule256  Void
                           alhsOppAgs = rule257  Void
                           alhsOppDebug = rule258  Void
                           alhsOppDebugs = rule259  Void
                           alhsOrecNode = rule260  Void
                           lcopy = rule261 arg_case__
                           alhsOcopy = rule262 lcopy
                           alhsOgraph = rule263 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule253  (_) =
     False
   rule254  (_) =
     Nothing
   rule255  (_) =
     Nothing
   rule256  (_) =
     empty
   rule257  (_) =
     []
   rule258  (_) =
     empty
   rule259  (_) =
     []
   rule260  (_) =
     False
   rule261 case__ =
     Case case__
   rule262 lcopy =
     lcopy
   rule263 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) (T_Selections ) -> T_Expression 
sem_Expression_Selection arg_skind_ arg_expr_ arg_sels_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           alhsOppDebug = rule264 aexprIppDebug lrecsel
                           alhsOppAg = rule265 aexprIppAg lrecsel
                           lrecsel = rule266 aselsIppAgs
                           alhsOhasRecs = rule267 aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule268 aexprImEntryId aselsImEntryId
                           alhsOmExitId = rule269 aexprImExitId aselsImExitId
                           alhsOppAgs = rule270 aexprIppAgs aselsIppAgs
                           alhsOppDebugs = rule271 aexprIppDebugs aselsIppDebugs
                           alhsOrecNode = rule272 aexprIrecNode aselsIrecNode
                           lcopy = rule273 aexprIcopy aselsIcopy arg_skind_
                           alhsOcopy = rule274 lcopy
                           alhsOgraph = rule275 aselsIgraph
                           aexprOcaseExpr = rule276 alhsIcaseExpr
                           aexprOcurrTaskName = rule277 alhsIcurrTaskName
                           aexprOgraph = rule278 alhsIgraph
                           aexprOmergeId = rule279 alhsImergeId
                           aexprOmoduleEnv = rule280 alhsImoduleEnv
                           aselsOcaseExpr = rule281 alhsIcaseExpr
                           aselsOcurrTaskName = rule282 alhsIcurrTaskName
                           aselsOgraph = rule283 aexprIgraph
                           aselsOmergeId = rule284 alhsImergeId
                           aselsOmoduleEnv = rule285 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 82 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule264 ((aexprIppDebug)) lrecsel =
                      /*# LINE 82 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<Selection>" <+> aexprIppDebug <-> lrecsel
                      /*# LINE 1787 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 84 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule265 ((aexprIppAg)) lrecsel =
                      /*# LINE 84 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      aexprIppAg <-> lrecsel
                      /*# LINE 1792 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 85 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule266 ((aselsIppAgs)) =
                      /*# LINE 85 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      char '.' <-> hcat (intersperse (char '.') $ aselsIppAgs)
                      /*# LINE 1797 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule267 ((aexprIhasRecs)) ((aselsIhasRecs)) =
     aexprIhasRecs || aselsIhasRecs
   rule268 ((aexprImEntryId)) ((aselsImEntryId)) =
     aexprImEntryId <> aselsImEntryId
   rule269 ((aexprImExitId)) ((aselsImExitId)) =
     aexprImExitId <> aselsImExitId
   rule270 ((aexprIppAgs)) ((aselsIppAgs)) =
     aexprIppAgs ++ aselsIppAgs
   rule271 ((aexprIppDebugs)) ((aselsIppDebugs)) =
     aexprIppDebugs ++ aselsIppDebugs
   rule272 ((aexprIrecNode)) ((aselsIrecNode)) =
     aexprIrecNode || aselsIrecNode
   rule273 ((aexprIcopy)) ((aselsIcopy)) skind_ =
     Selection skind_ aexprIcopy aselsIcopy
   rule274 lcopy =
     lcopy
   rule275 ((aselsIgraph)) =
     aselsIgraph
   rule276 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule277 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule278 ((alhsIgraph)) =
     alhsIgraph
   rule279 ((alhsImergeId)) =
     alhsImergeId
   rule280 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule281 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule282 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule283 ((aexprIgraph)) =
     aexprIgraph
   rule284 ((alhsImergeId)) =
     alhsImergeId
   rule285 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Update  :: (T_Expression ) (T_Selections ) (T_Expression ) -> T_Expression 
sem_Expression_Update arg_exprl_ arg_sels_ arg_exprr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprlX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprl_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprrX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprr_))
                           (T_Expression_vOut13 aexprlIcopy aexprlIgraph aexprlIhasRecs aexprlImEntryId aexprlImExitId aexprlIppAg aexprlIppAgs aexprlIppDebug aexprlIppDebugs aexprlIrecNode) = inv_Expression_s14 st_exprlX14 (T_Expression_vIn13 aexprlOcaseExpr aexprlOcurrTaskName aexprlOgraph aexprlOmergeId aexprlOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprrIcopy aexprrIgraph aexprrIhasRecs aexprrImEntryId aexprrImExitId aexprrIppAg aexprrIppAgs aexprrIppDebug aexprrIppDebugs aexprrIrecNode) = inv_Expression_s14 st_exprrX14 (T_Expression_vIn13 aexprrOcaseExpr aexprrOcurrTaskName aexprrOgraph aexprrOmergeId aexprrOmoduleEnv)
                           alhsOppDebug = rule286  Void
                           alhsOppAg = rule287  Void
                           alhsOhasRecs = rule288 aexprlIhasRecs aexprrIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule289 aexprlImEntryId aexprrImEntryId aselsImEntryId
                           alhsOmExitId = rule290 aexprlImExitId aexprrImExitId aselsImExitId
                           alhsOppAgs = rule291 aexprlIppAgs aexprrIppAgs aselsIppAgs
                           alhsOppDebugs = rule292 aexprlIppDebugs aexprrIppDebugs aselsIppDebugs
                           alhsOrecNode = rule293 aexprlIrecNode aexprrIrecNode aselsIrecNode
                           lcopy = rule294 aexprlIcopy aexprrIcopy aselsIcopy
                           alhsOcopy = rule295 lcopy
                           alhsOgraph = rule296 aexprrIgraph
                           aexprlOcaseExpr = rule297 alhsIcaseExpr
                           aexprlOcurrTaskName = rule298 alhsIcurrTaskName
                           aexprlOgraph = rule299 alhsIgraph
                           aexprlOmergeId = rule300 alhsImergeId
                           aexprlOmoduleEnv = rule301 alhsImoduleEnv
                           aselsOcaseExpr = rule302 alhsIcaseExpr
                           aselsOcurrTaskName = rule303 alhsIcurrTaskName
                           aselsOgraph = rule304 aexprlIgraph
                           aselsOmergeId = rule305 alhsImergeId
                           aselsOmoduleEnv = rule306 alhsImoduleEnv
                           aexprrOcaseExpr = rule307 alhsIcaseExpr
                           aexprrOcurrTaskName = rule308 alhsIcurrTaskName
                           aexprrOgraph = rule309 aselsIgraph
                           aexprrOmergeId = rule310 alhsImergeId
                           aexprrOmoduleEnv = rule311 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 88 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule286  (_) =
                      /*# LINE 88 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1881 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 89 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule287  (_) =
                      /*# LINE 89 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1886 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule288 ((aexprlIhasRecs)) ((aexprrIhasRecs)) ((aselsIhasRecs)) =
     aexprlIhasRecs || aselsIhasRecs || aexprrIhasRecs
   rule289 ((aexprlImEntryId)) ((aexprrImEntryId)) ((aselsImEntryId)) =
     aexprlImEntryId <> aselsImEntryId <> aexprrImEntryId
   rule290 ((aexprlImExitId)) ((aexprrImExitId)) ((aselsImExitId)) =
     aexprlImExitId <> aselsImExitId <> aexprrImExitId
   rule291 ((aexprlIppAgs)) ((aexprrIppAgs)) ((aselsIppAgs)) =
     aexprlIppAgs ++ aselsIppAgs ++ aexprrIppAgs
   rule292 ((aexprlIppDebugs)) ((aexprrIppDebugs)) ((aselsIppDebugs)) =
     aexprlIppDebugs ++ aselsIppDebugs ++ aexprrIppDebugs
   rule293 ((aexprlIrecNode)) ((aexprrIrecNode)) ((aselsIrecNode)) =
     aexprlIrecNode || aselsIrecNode || aexprrIrecNode
   rule294 ((aexprlIcopy)) ((aexprrIcopy)) ((aselsIcopy)) =
     Update aexprlIcopy aselsIcopy aexprrIcopy
   rule295 lcopy =
     lcopy
   rule296 ((aexprrIgraph)) =
     aexprrIgraph
   rule297 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule298 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule299 ((alhsIgraph)) =
     alhsIgraph
   rule300 ((alhsImergeId)) =
     alhsImergeId
   rule301 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule302 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule303 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule304 ((aexprlIgraph)) =
     aexprlIgraph
   rule305 ((alhsImergeId)) =
     alhsImergeId
   rule306 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule307 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule308 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule309 ((aselsIgraph)) =
     aselsIgraph
   rule310 ((alhsImergeId)) =
     alhsImergeId
   rule311 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_RecordUpdate  :: (T_GlobalDefinedSymbol ) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate arg_gdsym_ arg_expr_ arg_binds_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsymX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdsym_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut40 agdsymIcopy agdsymIgraph agdsymIhasRecs agdsymImEntryId agdsymImExitId agdsymIppAg agdsymIppAgs agdsymIppDebug agdsymIppDebugs agdsymIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsymX41 (T_GlobalDefinedSymbol_vIn40 agdsymOcaseExpr agdsymOcurrTaskName agdsymOgraph agdsymOmergeId agdsymOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule312  Void
                           alhsOppAg = rule313  Void
                           alhsOhasRecs = rule314 aexprIhasRecs agdsymIhasRecs
                           alhsOmEntryId = rule315 aexprImEntryId agdsymImEntryId
                           alhsOmExitId = rule316 aexprImExitId agdsymImExitId
                           alhsOppAgs = rule317 aexprIppAgs agdsymIppAgs
                           alhsOppDebugs = rule318 aexprIppDebugs agdsymIppDebugs
                           alhsOrecNode = rule319 aexprIrecNode agdsymIrecNode
                           lcopy = rule320 aexprIcopy agdsymIcopy arg_binds_
                           alhsOcopy = rule321 lcopy
                           alhsOgraph = rule322 aexprIgraph
                           agdsymOcaseExpr = rule323 alhsIcaseExpr
                           agdsymOcurrTaskName = rule324 alhsIcurrTaskName
                           agdsymOgraph = rule325 alhsIgraph
                           agdsymOmergeId = rule326 alhsImergeId
                           agdsymOmoduleEnv = rule327 alhsImoduleEnv
                           aexprOcaseExpr = rule328 alhsIcaseExpr
                           aexprOcurrTaskName = rule329 alhsIcurrTaskName
                           aexprOgraph = rule330 agdsymIgraph
                           aexprOmergeId = rule331 alhsImergeId
                           aexprOmoduleEnv = rule332 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 92 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule312  (_) =
                      /*# LINE 92 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 1973 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 93 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule313  (_) =
                      /*# LINE 93 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 1978 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule314 ((aexprIhasRecs)) ((agdsymIhasRecs)) =
     agdsymIhasRecs || aexprIhasRecs
   rule315 ((aexprImEntryId)) ((agdsymImEntryId)) =
     agdsymImEntryId <> aexprImEntryId
   rule316 ((aexprImExitId)) ((agdsymImExitId)) =
     agdsymImExitId <> aexprImExitId
   rule317 ((aexprIppAgs)) ((agdsymIppAgs)) =
     agdsymIppAgs ++ aexprIppAgs
   rule318 ((aexprIppDebugs)) ((agdsymIppDebugs)) =
     agdsymIppDebugs ++ aexprIppDebugs
   rule319 ((aexprIrecNode)) ((agdsymIrecNode)) =
     agdsymIrecNode || aexprIrecNode
   rule320 ((aexprIcopy)) ((agdsymIcopy)) binds_ =
     RecordUpdate agdsymIcopy aexprIcopy binds_
   rule321 lcopy =
     lcopy
   rule322 ((aexprIgraph)) =
     aexprIgraph
   rule323 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule324 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule325 ((alhsIgraph)) =
     alhsIgraph
   rule326 ((alhsImergeId)) =
     alhsImergeId
   rule327 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule328 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule329 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule330 ((agdsymIgraph)) =
     agdsymIgraph
   rule331 ((alhsImergeId)) =
     alhsImergeId
   rule332 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_TupleSelect  :: (T_DefinedSymbol ) (Int) (T_Expression ) -> T_Expression 
sem_Expression_TupleSelect arg_dsym_ arg_n_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_dsymX11 = 'Control.Monad.Identity'.runIdentity (attach_T_DefinedSymbol (arg_dsym_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_DefinedSymbol_vOut10 adsymIcopy adsymIgraph adsymIhasRecs adsymImEntryId adsymImExitId adsymIppAg adsymIppAgs adsymIppDebug adsymIppDebugs adsymIrecNode) = inv_DefinedSymbol_s11 st_dsymX11 (T_DefinedSymbol_vIn10 adsymOcaseExpr adsymOcurrTaskName adsymOgraph adsymOmergeId adsymOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule333  Void
                           alhsOppAg = rule334  Void
                           alhsOhasRecs = rule335 adsymIhasRecs aexprIhasRecs
                           alhsOmEntryId = rule336 adsymImEntryId aexprImEntryId
                           alhsOmExitId = rule337 adsymImExitId aexprImExitId
                           alhsOppAgs = rule338 adsymIppAgs aexprIppAgs
                           alhsOppDebugs = rule339 adsymIppDebugs aexprIppDebugs
                           alhsOrecNode = rule340 adsymIrecNode aexprIrecNode
                           lcopy = rule341 adsymIcopy aexprIcopy arg_n_
                           alhsOcopy = rule342 lcopy
                           alhsOgraph = rule343 aexprIgraph
                           adsymOcaseExpr = rule344 alhsIcaseExpr
                           adsymOcurrTaskName = rule345 alhsIcurrTaskName
                           adsymOgraph = rule346 alhsIgraph
                           adsymOmergeId = rule347 alhsImergeId
                           adsymOmoduleEnv = rule348 alhsImoduleEnv
                           aexprOcaseExpr = rule349 alhsIcaseExpr
                           aexprOcurrTaskName = rule350 alhsIcurrTaskName
                           aexprOgraph = rule351 adsymIgraph
                           aexprOmergeId = rule352 alhsImergeId
                           aexprOmoduleEnv = rule353 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 96 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule333  (_) =
                      /*# LINE 96 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 2055 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 97 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule334  (_) =
                      /*# LINE 97 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 2060 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule335 ((adsymIhasRecs)) ((aexprIhasRecs)) =
     adsymIhasRecs || aexprIhasRecs
   rule336 ((adsymImEntryId)) ((aexprImEntryId)) =
     adsymImEntryId <> aexprImEntryId
   rule337 ((adsymImExitId)) ((aexprImExitId)) =
     adsymImExitId <> aexprImExitId
   rule338 ((adsymIppAgs)) ((aexprIppAgs)) =
     adsymIppAgs ++ aexprIppAgs
   rule339 ((adsymIppDebugs)) ((aexprIppDebugs)) =
     adsymIppDebugs ++ aexprIppDebugs
   rule340 ((adsymIrecNode)) ((aexprIrecNode)) =
     adsymIrecNode || aexprIrecNode
   rule341 ((adsymIcopy)) ((aexprIcopy)) n_ =
     TupleSelect adsymIcopy n_ aexprIcopy
   rule342 lcopy =
     lcopy
   rule343 ((aexprIgraph)) =
     aexprIgraph
   rule344 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule345 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule346 ((alhsIgraph)) =
     alhsIgraph
   rule347 ((alhsImergeId)) =
     alhsImergeId
   rule348 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule349 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule350 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule351 ((adsymIgraph)) =
     adsymIgraph
   rule352 ((alhsImergeId)) =
     alhsImergeId
   rule353 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_BasicExpr  :: (T_BasicValue ) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_bvX5 = 'Control.Monad.Identity'.runIdentity (attach_T_BasicValue (arg_bv_))
                           (T_BasicValue_vOut4 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BasicValue_s5 st_bvX5 (T_BasicValue_vIn4 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           alhsOppDebug = rule354 abvIppDebug
                           alhsOppAg = rule355 abvIppAg
                           alhsOhasRecs = rule356 abvIhasRecs
                           alhsOmEntryId = rule357 abvImEntryId
                           alhsOmExitId = rule358 abvImExitId
                           alhsOppAgs = rule359 abvIppAgs
                           alhsOppDebugs = rule360 abvIppDebugs
                           alhsOrecNode = rule361 abvIrecNode
                           lcopy = rule362 abvIcopy
                           alhsOcopy = rule363 lcopy
                           alhsOgraph = rule364 abvIgraph
                           abvOcaseExpr = rule365 alhsIcaseExpr
                           abvOcurrTaskName = rule366 alhsIcurrTaskName
                           abvOgraph = rule367 alhsIgraph
                           abvOmergeId = rule368 alhsImergeId
                           abvOmoduleEnv = rule369 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 100 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule354 ((abvIppDebug)) =
                      /*# LINE 100 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      text "<BasicValue>" <+> abvIppDebug
                      /*# LINE 2130 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 101 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule355 ((abvIppAg)) =
                      /*# LINE 101 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 2135 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule356 ((abvIhasRecs)) =
     abvIhasRecs
   rule357 ((abvImEntryId)) =
     abvImEntryId
   rule358 ((abvImExitId)) =
     abvImExitId
   rule359 ((abvIppAgs)) =
     abvIppAgs
   rule360 ((abvIppDebugs)) =
     abvIppDebugs
   rule361 ((abvIrecNode)) =
     abvIrecNode
   rule362 ((abvIcopy)) =
     BasicExpr abvIcopy
   rule363 lcopy =
     lcopy
   rule364 ((abvIgraph)) =
     abvIgraph
   rule365 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule366 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule367 ((alhsIgraph)) =
     alhsIgraph
   rule368 ((alhsImergeId)) =
     alhsImergeId
   rule369 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_Conditional arg_cond_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule370  Void
                           alhsOmEntryId = rule371  Void
                           alhsOmExitId = rule372  Void
                           alhsOppAg = rule373  Void
                           alhsOppAgs = rule374  Void
                           alhsOppDebug = rule375  Void
                           alhsOppDebugs = rule376  Void
                           alhsOrecNode = rule377  Void
                           lcopy = rule378 arg_cond_
                           alhsOcopy = rule379 lcopy
                           alhsOgraph = rule380 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule370  (_) =
     False
   rule371  (_) =
     Nothing
   rule372  (_) =
     Nothing
   rule373  (_) =
     empty
   rule374  (_) =
     []
   rule375  (_) =
     empty
   rule376  (_) =
     []
   rule377  (_) =
     False
   rule378 cond_ =
     Conditional cond_
   rule379 lcopy =
     lcopy
   rule380 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr arg_cbbv_ arg_cbfv_ arg_ss_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule381  Void
                           alhsOmEntryId = rule382  Void
                           alhsOmExitId = rule383  Void
                           alhsOppAg = rule384  Void
                           alhsOppAgs = rule385  Void
                           alhsOppDebug = rule386  Void
                           alhsOppDebugs = rule387  Void
                           alhsOrecNode = rule388  Void
                           lcopy = rule389 arg_cbbv_ arg_cbfv_ arg_ss_
                           alhsOcopy = rule390 lcopy
                           alhsOgraph = rule391 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule381  (_) =
     False
   rule382  (_) =
     Nothing
   rule383  (_) =
     Nothing
   rule384  (_) =
     empty
   rule385  (_) =
     []
   rule386  (_) =
     empty
   rule387  (_) =
     []
   rule388  (_) =
     False
   rule389 cbbv_ cbfv_ ss_ =
     AnyCodeExpr cbbv_ cbfv_ ss_
   rule390 lcopy =
     lcopy
   rule391 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr arg_ss_ arg_bl_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule392  Void
                           alhsOmEntryId = rule393  Void
                           alhsOmExitId = rule394  Void
                           alhsOppAg = rule395  Void
                           alhsOppAgs = rule396  Void
                           alhsOppDebug = rule397  Void
                           alhsOppDebugs = rule398  Void
                           alhsOrecNode = rule399  Void
                           lcopy = rule400 arg_bl_ arg_ss_
                           alhsOcopy = rule401 lcopy
                           alhsOgraph = rule402 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule392  (_) =
     False
   rule393  (_) =
     Nothing
   rule394  (_) =
     Nothing
   rule395  (_) =
     empty
   rule396  (_) =
     []
   rule397  (_) =
     empty
   rule398  (_) =
     []
   rule399  (_) =
     False
   rule400 bl_ ss_ =
     ABCCodeExpr ss_ bl_
   rule401 lcopy =
     lcopy
   rule402 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr arg_gdfs_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule403 aexprIhasRecs
                           alhsOmEntryId = rule404 aexprImEntryId
                           alhsOmExitId = rule405 aexprImExitId
                           alhsOppAg = rule406 aexprIppAg
                           alhsOppAgs = rule407 aexprIppAgs
                           alhsOppDebug = rule408 aexprIppDebug
                           alhsOppDebugs = rule409 aexprIppDebugs
                           alhsOrecNode = rule410 aexprIrecNode
                           lcopy = rule411 aexprIcopy arg_gdfs_
                           alhsOcopy = rule412 lcopy
                           alhsOgraph = rule413 aexprIgraph
                           aexprOcaseExpr = rule414 alhsIcaseExpr
                           aexprOcurrTaskName = rule415 alhsIcurrTaskName
                           aexprOgraph = rule416 alhsIgraph
                           aexprOmergeId = rule417 alhsImergeId
                           aexprOmoduleEnv = rule418 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule403 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule404 ((aexprImEntryId)) =
     aexprImEntryId
   rule405 ((aexprImExitId)) =
     aexprImExitId
   rule406 ((aexprIppAg)) =
     aexprIppAg
   rule407 ((aexprIppAgs)) =
     aexprIppAgs
   rule408 ((aexprIppDebug)) =
     aexprIppDebug
   rule409 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule410 ((aexprIrecNode)) =
     aexprIrecNode
   rule411 ((aexprIcopy)) gdfs_ =
     MatchExpr gdfs_ aexprIcopy
   rule412 lcopy =
     lcopy
   rule413 ((aexprIgraph)) =
     aexprIgraph
   rule414 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule415 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule416 ((alhsIgraph)) =
     alhsIgraph
   rule417 ((alhsImergeId)) =
     alhsImergeId
   rule418 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_IsConstructor  :: (T_Expression ) (T_GlobalDefinedSymbol ) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ arg_gdfs_ arg_arity_ arg_gidx_ arg_ident_ arg_pos_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_gdfsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdfs_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_GlobalDefinedSymbol_vOut40 agdfsIcopy agdfsIgraph agdfsIhasRecs agdfsImEntryId agdfsImExitId agdfsIppAg agdfsIppAgs agdfsIppDebug agdfsIppDebugs agdfsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdfsX41 (T_GlobalDefinedSymbol_vIn40 agdfsOcaseExpr agdfsOcurrTaskName agdfsOgraph agdfsOmergeId agdfsOmoduleEnv)
                           alhsOhasRecs = rule419 aexprIhasRecs agdfsIhasRecs
                           alhsOmEntryId = rule420 aexprImEntryId agdfsImEntryId
                           alhsOmExitId = rule421 aexprImExitId agdfsImExitId
                           alhsOppAg = rule422 aexprIppAg agdfsIppAg
                           alhsOppAgs = rule423 aexprIppAgs agdfsIppAgs
                           alhsOppDebug = rule424 aexprIppDebug agdfsIppDebug
                           alhsOppDebugs = rule425 aexprIppDebugs agdfsIppDebugs
                           alhsOrecNode = rule426 aexprIrecNode agdfsIrecNode
                           lcopy = rule427 aexprIcopy agdfsIcopy arg_arity_ arg_gidx_ arg_ident_ arg_pos_
                           alhsOcopy = rule428 lcopy
                           alhsOgraph = rule429 agdfsIgraph
                           aexprOcaseExpr = rule430 alhsIcaseExpr
                           aexprOcurrTaskName = rule431 alhsIcurrTaskName
                           aexprOgraph = rule432 alhsIgraph
                           aexprOmergeId = rule433 alhsImergeId
                           aexprOmoduleEnv = rule434 alhsImoduleEnv
                           agdfsOcaseExpr = rule435 alhsIcaseExpr
                           agdfsOcurrTaskName = rule436 alhsIcurrTaskName
                           agdfsOgraph = rule437 aexprIgraph
                           agdfsOmergeId = rule438 alhsImergeId
                           agdfsOmoduleEnv = rule439 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule419 ((aexprIhasRecs)) ((agdfsIhasRecs)) =
     aexprIhasRecs || agdfsIhasRecs
   rule420 ((aexprImEntryId)) ((agdfsImEntryId)) =
     aexprImEntryId <> agdfsImEntryId
   rule421 ((aexprImExitId)) ((agdfsImExitId)) =
     aexprImExitId <> agdfsImExitId
   rule422 ((aexprIppAg)) ((agdfsIppAg)) =
     aexprIppAg <$$> agdfsIppAg
   rule423 ((aexprIppAgs)) ((agdfsIppAgs)) =
     aexprIppAgs ++ agdfsIppAgs
   rule424 ((aexprIppDebug)) ((agdfsIppDebug)) =
     aexprIppDebug <$$> agdfsIppDebug
   rule425 ((aexprIppDebugs)) ((agdfsIppDebugs)) =
     aexprIppDebugs ++ agdfsIppDebugs
   rule426 ((aexprIrecNode)) ((agdfsIrecNode)) =
     aexprIrecNode || agdfsIrecNode
   rule427 ((aexprIcopy)) ((agdfsIcopy)) arity_ gidx_ ident_ pos_ =
     IsConstructor aexprIcopy agdfsIcopy arity_ gidx_ ident_ pos_
   rule428 lcopy =
     lcopy
   rule429 ((agdfsIgraph)) =
     agdfsIgraph
   rule430 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule431 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule432 ((alhsIgraph)) =
     alhsIgraph
   rule433 ((alhsImergeId)) =
     alhsImergeId
   rule434 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule435 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule436 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule437 ((aexprIgraph)) =
     aexprIgraph
   rule438 ((alhsImergeId)) =
     alhsImergeId
   rule439 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_FreeVar  :: (T_FreeVar ) -> T_Expression 
sem_Expression_FreeVar arg_fv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_fvX20 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVar (arg_fv_))
                           (T_FreeVar_vOut19 afvIcopy afvIgraph afvIhasRecs afvImEntryId afvImExitId afvIppAg afvIppAgs afvIppDebug afvIppDebugs afvIrecNode) = inv_FreeVar_s20 st_fvX20 (T_FreeVar_vIn19 afvOcaseExpr afvOcurrTaskName afvOgraph afvOmergeId afvOmoduleEnv)
                           alhsOhasRecs = rule440 afvIhasRecs
                           alhsOmEntryId = rule441 afvImEntryId
                           alhsOmExitId = rule442 afvImExitId
                           alhsOppAg = rule443 afvIppAg
                           alhsOppAgs = rule444 afvIppAgs
                           alhsOppDebug = rule445 afvIppDebug
                           alhsOppDebugs = rule446 afvIppDebugs
                           alhsOrecNode = rule447 afvIrecNode
                           lcopy = rule448 afvIcopy
                           alhsOcopy = rule449 lcopy
                           alhsOgraph = rule450 afvIgraph
                           afvOcaseExpr = rule451 alhsIcaseExpr
                           afvOcurrTaskName = rule452 alhsIcurrTaskName
                           afvOgraph = rule453 alhsIgraph
                           afvOmergeId = rule454 alhsImergeId
                           afvOmoduleEnv = rule455 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule440 ((afvIhasRecs)) =
     afvIhasRecs
   rule441 ((afvImEntryId)) =
     afvImEntryId
   rule442 ((afvImExitId)) =
     afvImExitId
   rule443 ((afvIppAg)) =
     afvIppAg
   rule444 ((afvIppAgs)) =
     afvIppAgs
   rule445 ((afvIppDebug)) =
     afvIppDebug
   rule446 ((afvIppDebugs)) =
     afvIppDebugs
   rule447 ((afvIrecNode)) =
     afvIrecNode
   rule448 ((afvIcopy)) =
     FreeVar afvIcopy
   rule449 lcopy =
     lcopy
   rule450 ((afvIgraph)) =
     afvIgraph
   rule451 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule452 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule453 ((alhsIgraph)) =
     alhsIgraph
   rule454 ((alhsImergeId)) =
     alhsImergeId
   rule455 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction arg_fvat_ arg_expr_ arg_aty_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule456 aexprIhasRecs
                           alhsOmEntryId = rule457 aexprImEntryId
                           alhsOmExitId = rule458 aexprImExitId
                           alhsOppAg = rule459 aexprIppAg
                           alhsOppAgs = rule460 aexprIppAgs
                           alhsOppDebug = rule461 aexprIppDebug
                           alhsOppDebugs = rule462 aexprIppDebugs
                           alhsOrecNode = rule463 aexprIrecNode
                           lcopy = rule464 aexprIcopy arg_aty_ arg_fvat_
                           alhsOcopy = rule465 lcopy
                           alhsOgraph = rule466 aexprIgraph
                           aexprOcaseExpr = rule467 alhsIcaseExpr
                           aexprOcurrTaskName = rule468 alhsIcurrTaskName
                           aexprOgraph = rule469 alhsIgraph
                           aexprOmergeId = rule470 alhsImergeId
                           aexprOmoduleEnv = rule471 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule456 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule457 ((aexprImEntryId)) =
     aexprImEntryId
   rule458 ((aexprImExitId)) =
     aexprImExitId
   rule459 ((aexprIppAg)) =
     aexprIppAg
   rule460 ((aexprIppAgs)) =
     aexprIppAgs
   rule461 ((aexprIppDebug)) =
     aexprIppDebug
   rule462 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule463 ((aexprIrecNode)) =
     aexprIrecNode
   rule464 ((aexprIcopy)) aty_ fvat_ =
     DictionariesFunction fvat_ aexprIcopy aty_
   rule465 lcopy =
     lcopy
   rule466 ((aexprIgraph)) =
     aexprIgraph
   rule467 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule468 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule469 ((alhsIgraph)) =
     alhsIgraph
   rule470 ((alhsImergeId)) =
     alhsImergeId
   rule471 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Constant  :: (T_SymbIdent ) (Int) (Priority) -> T_Expression 
sem_Expression_Constant arg_symid_ arg_n_ arg_prio_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_symidX53 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_symid_))
                           (T_SymbIdent_vOut52 asymidIcopy asymidIgraph asymidIhasRecs asymidIident asymidIisCurrTask asymidIisInfix asymidIisTask asymidImEntryId asymidImExitId asymidIppAg asymidIppAgs asymidIppDebug asymidIppDebugs asymidIrecNode asymidIreifyFunDef asymidIreifyFunType asymidIreifySymbolType) = inv_SymbIdent_s53 st_symidX53 (T_SymbIdent_vIn52 asymidOcaseExpr asymidOcurrTaskName asymidOgraph asymidOmergeId asymidOmoduleEnv)
                           alhsOhasRecs = rule472 asymidIhasRecs
                           alhsOmEntryId = rule473 asymidImEntryId
                           alhsOmExitId = rule474 asymidImExitId
                           alhsOppAg = rule475 asymidIppAg
                           alhsOppAgs = rule476 asymidIppAgs
                           alhsOppDebug = rule477 asymidIppDebug
                           alhsOppDebugs = rule478 asymidIppDebugs
                           alhsOrecNode = rule479 asymidIrecNode
                           lcopy = rule480 asymidIcopy arg_n_ arg_prio_
                           alhsOcopy = rule481 lcopy
                           alhsOgraph = rule482 asymidIgraph
                           asymidOcaseExpr = rule483 alhsIcaseExpr
                           asymidOcurrTaskName = rule484 alhsIcurrTaskName
                           asymidOgraph = rule485 alhsIgraph
                           asymidOmergeId = rule486 alhsImergeId
                           asymidOmoduleEnv = rule487 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule472 ((asymidIhasRecs)) =
     asymidIhasRecs
   rule473 ((asymidImEntryId)) =
     asymidImEntryId
   rule474 ((asymidImExitId)) =
     asymidImExitId
   rule475 ((asymidIppAg)) =
     asymidIppAg
   rule476 ((asymidIppAgs)) =
     asymidIppAgs
   rule477 ((asymidIppDebug)) =
     asymidIppDebug
   rule478 ((asymidIppDebugs)) =
     asymidIppDebugs
   rule479 ((asymidIrecNode)) =
     asymidIrecNode
   rule480 ((asymidIcopy)) n_ prio_ =
     Constant asymidIcopy n_ prio_
   rule481 lcopy =
     lcopy
   rule482 ((asymidIgraph)) =
     asymidIgraph
   rule483 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule484 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule485 ((alhsIgraph)) =
     alhsIgraph
   rule486 ((alhsImergeId)) =
     alhsImergeId
   rule487 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable arg_varinfptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule488  Void
                           alhsOmEntryId = rule489  Void
                           alhsOmExitId = rule490  Void
                           alhsOppAg = rule491  Void
                           alhsOppAgs = rule492  Void
                           alhsOppDebug = rule493  Void
                           alhsOppDebugs = rule494  Void
                           alhsOrecNode = rule495  Void
                           lcopy = rule496 arg_varinfptr_
                           alhsOcopy = rule497 lcopy
                           alhsOgraph = rule498 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule488  (_) =
     False
   rule489  (_) =
     Nothing
   rule490  (_) =
     Nothing
   rule491  (_) =
     empty
   rule492  (_) =
     []
   rule493  (_) =
     empty
   rule494  (_) =
     []
   rule495  (_) =
     False
   rule496 varinfptr_ =
     ClassVariable varinfptr_
   rule497 lcopy =
     lcopy
   rule498 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr arg_dynexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule499  Void
                           alhsOmEntryId = rule500  Void
                           alhsOmExitId = rule501  Void
                           alhsOppAg = rule502  Void
                           alhsOppAgs = rule503  Void
                           alhsOppDebug = rule504  Void
                           alhsOppDebugs = rule505  Void
                           alhsOrecNode = rule506  Void
                           lcopy = rule507 arg_dynexpr_
                           alhsOcopy = rule508 lcopy
                           alhsOgraph = rule509 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule499  (_) =
     False
   rule500  (_) =
     Nothing
   rule501  (_) =
     Nothing
   rule502  (_) =
     empty
   rule503  (_) =
     []
   rule504  (_) =
     empty
   rule505  (_) =
     []
   rule506  (_) =
     False
   rule507 dynexpr_ =
     DynamicExpr dynexpr_
   rule508 lcopy =
     lcopy
   rule509 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression arg_tycodeexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule510  Void
                           alhsOmEntryId = rule511  Void
                           alhsOmExitId = rule512  Void
                           alhsOppAg = rule513  Void
                           alhsOppAgs = rule514  Void
                           alhsOppDebug = rule515  Void
                           alhsOppDebugs = rule516  Void
                           alhsOrecNode = rule517  Void
                           lcopy = rule518 arg_tycodeexpr_
                           alhsOcopy = rule519 lcopy
                           alhsOgraph = rule520 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule510  (_) =
     False
   rule511  (_) =
     Nothing
   rule512  (_) =
     Nothing
   rule513  (_) =
     empty
   rule514  (_) =
     []
   rule515  (_) =
     empty
   rule516  (_) =
     []
   rule517  (_) =
     False
   rule518 tycodeexpr_ =
     TypeCodeExpression tycodeexpr_
   rule519 lcopy =
     lcopy
   rule520 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature arg_sigfun_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule521 aexprIhasRecs
                           alhsOmEntryId = rule522 aexprImEntryId
                           alhsOmExitId = rule523 aexprImExitId
                           alhsOppAg = rule524 aexprIppAg
                           alhsOppAgs = rule525 aexprIppAgs
                           alhsOppDebug = rule526 aexprIppDebug
                           alhsOppDebugs = rule527 aexprIppDebugs
                           alhsOrecNode = rule528 aexprIrecNode
                           lcopy = rule529 aexprIcopy arg_sigfun_
                           alhsOcopy = rule530 lcopy
                           alhsOgraph = rule531 aexprIgraph
                           aexprOcaseExpr = rule532 alhsIcaseExpr
                           aexprOcurrTaskName = rule533 alhsIcurrTaskName
                           aexprOgraph = rule534 alhsIgraph
                           aexprOmergeId = rule535 alhsImergeId
                           aexprOmoduleEnv = rule536 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule521 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule522 ((aexprImEntryId)) =
     aexprImEntryId
   rule523 ((aexprImExitId)) =
     aexprImExitId
   rule524 ((aexprIppAg)) =
     aexprIppAg
   rule525 ((aexprIppAgs)) =
     aexprIppAgs
   rule526 ((aexprIppDebug)) =
     aexprIppDebug
   rule527 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule528 ((aexprIrecNode)) =
     aexprIrecNode
   rule529 ((aexprIcopy)) sigfun_ =
     TypeSignature sigfun_ aexprIcopy
   rule530 lcopy =
     lcopy
   rule531 ((aexprIgraph)) =
     aexprIgraph
   rule532 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule533 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule534 ((alhsIgraph)) =
     alhsIgraph
   rule535 ((alhsImergeId)) =
     alhsImergeId
   rule536 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_EE  ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule537  Void
                           alhsOmEntryId = rule538  Void
                           alhsOmExitId = rule539  Void
                           alhsOppAg = rule540  Void
                           alhsOppAgs = rule541  Void
                           alhsOppDebug = rule542  Void
                           alhsOppDebugs = rule543  Void
                           alhsOrecNode = rule544  Void
                           lcopy = rule545  Void
                           alhsOcopy = rule546 lcopy
                           alhsOgraph = rule547 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule537  (_) =
     False
   rule538  (_) =
     Nothing
   rule539  (_) =
     Nothing
   rule540  (_) =
     empty
   rule541  (_) =
     []
   rule542  (_) =
     empty
   rule543  (_) =
     []
   rule544  (_) =
     False
   rule545  (_) =
     EE
   rule546 lcopy =
     lcopy
   rule547 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind arg_exprinfoptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule548  Void
                           alhsOmEntryId = rule549  Void
                           alhsOmExitId = rule550  Void
                           alhsOppAg = rule551  Void
                           alhsOppAgs = rule552  Void
                           alhsOppDebug = rule553  Void
                           alhsOppDebugs = rule554  Void
                           alhsOrecNode = rule555  Void
                           lcopy = rule556 arg_exprinfoptr_
                           alhsOcopy = rule557 lcopy
                           alhsOgraph = rule558 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule548  (_) =
     False
   rule549  (_) =
     Nothing
   rule550  (_) =
     Nothing
   rule551  (_) =
     empty
   rule552  (_) =
     []
   rule553  (_) =
     empty
   rule554  (_) =
     []
   rule555  (_) =
     False
   rule556 exprinfoptr_ =
     NoBind exprinfoptr_
   rule557 lcopy =
     lcopy
   rule558 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_FailExpr  :: (T_Ident ) -> T_Expression 
sem_Expression_FailExpr arg_ident_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ident_))
                           (T_Ident_vOut43 aidentIcopy aidentIgraph aidentIhasRecs aidentIident aidentIisTask aidentImEntryId aidentImExitId aidentIppAg aidentIppAgs aidentIppDebug aidentIppDebugs aidentIrecNode aidentIreifyFunDef aidentIreifyFunType aidentIreifySymbolType) = inv_Ident_s44 st_identX44 (T_Ident_vIn43 aidentOcaseExpr aidentOcurrTaskName aidentOgraph aidentOmergeId aidentOmoduleEnv)
                           alhsOhasRecs = rule559 aidentIhasRecs
                           alhsOmEntryId = rule560 aidentImEntryId
                           alhsOmExitId = rule561 aidentImExitId
                           alhsOppAg = rule562 aidentIppAg
                           alhsOppAgs = rule563 aidentIppAgs
                           alhsOppDebug = rule564 aidentIppDebug
                           alhsOppDebugs = rule565 aidentIppDebugs
                           alhsOrecNode = rule566 aidentIrecNode
                           lcopy = rule567 aidentIcopy
                           alhsOcopy = rule568 lcopy
                           alhsOgraph = rule569 aidentIgraph
                           aidentOcaseExpr = rule570 alhsIcaseExpr
                           aidentOcurrTaskName = rule571 alhsIcurrTaskName
                           aidentOgraph = rule572 alhsIgraph
                           aidentOmergeId = rule573 alhsImergeId
                           aidentOmoduleEnv = rule574 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule559 ((aidentIhasRecs)) =
     aidentIhasRecs
   rule560 ((aidentImEntryId)) =
     aidentImEntryId
   rule561 ((aidentImExitId)) =
     aidentImExitId
   rule562 ((aidentIppAg)) =
     aidentIppAg
   rule563 ((aidentIppAgs)) =
     aidentIppAgs
   rule564 ((aidentIppDebug)) =
     aidentIppDebug
   rule565 ((aidentIppDebugs)) =
     aidentIppDebugs
   rule566 ((aidentIrecNode)) =
     aidentIrecNode
   rule567 ((aidentIcopy)) =
     FailExpr aidentIcopy
   rule568 lcopy =
     lcopy
   rule569 ((aidentIgraph)) =
     aidentIgraph
   rule570 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule571 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule572 ((alhsIgraph)) =
     alhsIgraph
   rule573 ((alhsImergeId)) =
     alhsImergeId
   rule574 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// Expressions -------------------------------------------------
// wrapper
moduleEnv_Inh_Expressions :: Inh_Expressions -> (ModuleEnv)
moduleEnv_Inh_Expressions (Inh_Expressions _ _ _ _ x) = x
mergeId_Inh_Expressions :: Inh_Expressions -> (Int)
mergeId_Inh_Expressions (Inh_Expressions _ _ _ x _) = x
graph_Inh_Expressions :: Inh_Expressions -> (GinGraph)
graph_Inh_Expressions (Inh_Expressions _ _ x _ _) = x
currTaskName_Inh_Expressions :: Inh_Expressions -> (String)
currTaskName_Inh_Expressions (Inh_Expressions _ x _ _ _) = x
caseExpr_Inh_Expressions :: Inh_Expressions -> (Maybe Expression)
caseExpr_Inh_Expressions (Inh_Expressions x _ _ _ _) = x
recNode_Syn_Expressions :: Syn_Expressions -> (Bool)
recNode_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppDebugs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebug_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppAgs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAg_Syn_Expressions (Syn_Expressions _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mExitId_Syn_Expressions (Syn_Expressions _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mEntryId_Syn_Expressions (Syn_Expressions _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
hasRecs_Syn_Expressions (Syn_Expressions _ _ x _ _ _ _ _ _ _) = x
graph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
graph_Syn_Expressions (Syn_Expressions _ x _ _ _ _ _ _ _ _) = x
copy_Syn_Expressions :: Syn_Expressions -> (Expressions)
copy_Syn_Expressions (Syn_Expressions x _ _ _ _ _ _ _ _ _) = x
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expressions_vIn16 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expressions_s17 sem arg) >>= \ (T_Expressions_vOut16 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Expressions alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = foldr sem_Expressions_Cons sem_Expressions_Nil (map sem_Expression list)

// semantic domain
attach_T_Expressions (T_Expressions t_Expressions) = t_Expressions
inv_Expressions_s17 (C_Expressions_s17 x) = x
sem_Expressions_Cons  :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (lift st17) where
   st17 =
         let
             v16 (T_Expressions_vIn16 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_hd_))
                           st_tlX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_tl_))
                           (T_Expression_vOut13 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Expression_s14 st_hdX14 (T_Expression_vIn13 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Expressions_vOut16 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_Expressions_s17 st_tlX17 (T_Expressions_vIn16 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs = rule575 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule576 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule577 ahdImExitId atlImExitId
                           alhsOppAg = rule578 ahdIppAg atlIppAg
                           alhsOppAgs = rule579 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule580 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule581 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule582 ahdIrecNode atlIrecNode
                           lcopy = rule583 ahdIcopy atlIcopy
                           alhsOcopy = rule584 lcopy
                           alhsOgraph = rule585 atlIgraph
                           ahdOcaseExpr = rule586 alhsIcaseExpr
                           ahdOcurrTaskName = rule587 alhsIcurrTaskName
                           ahdOgraph = rule588 alhsIgraph
                           ahdOmergeId = rule589 alhsImergeId
                           ahdOmoduleEnv = rule590 alhsImoduleEnv
                           atlOcaseExpr = rule591 alhsIcaseExpr
                           atlOcurrTaskName = rule592 alhsIcurrTaskName
                           atlOgraph = rule593 ahdIgraph
                           atlOmergeId = rule594 alhsImergeId
                           atlOmoduleEnv = rule595 alhsImoduleEnv
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expressions_s17 v16
   rule575 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule576 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule577 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule578 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule579 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule580 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule581 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule582 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule583 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule584 lcopy =
     lcopy
   rule585 ((atlIgraph)) =
     atlIgraph
   rule586 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule587 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule588 ((alhsIgraph)) =
     alhsIgraph
   rule589 ((alhsImergeId)) =
     alhsImergeId
   rule590 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule591 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule592 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule593 ((ahdIgraph)) =
     ahdIgraph
   rule594 ((alhsImergeId)) =
     alhsImergeId
   rule595 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expressions_Nil  ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st17) where
   st17 =
         let
             v16 (T_Expressions_vIn16 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule596  Void
                           alhsOmEntryId = rule597  Void
                           alhsOmExitId = rule598  Void
                           alhsOppAg = rule599  Void
                           alhsOppAgs = rule600  Void
                           alhsOppDebug = rule601  Void
                           alhsOppDebugs = rule602  Void
                           alhsOrecNode = rule603  Void
                           lcopy = rule604  Void
                           alhsOcopy = rule605 lcopy
                           alhsOgraph = rule606 alhsIgraph
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expressions_s17 v16
   rule596  (_) =
     False
   rule597  (_) =
     Nothing
   rule598  (_) =
     Nothing
   rule599  (_) =
     empty
   rule600  (_) =
     []
   rule601  (_) =
     empty
   rule602  (_) =
     []
   rule603  (_) =
     False
   rule604  (_) =
     []
   rule605 lcopy =
     lcopy
   rule606 ((alhsIgraph)) =
     alhsIgraph

// FreeVar -----------------------------------------------------
// wrapper
moduleEnv_Inh_FreeVar :: Inh_FreeVar -> (ModuleEnv)
moduleEnv_Inh_FreeVar (Inh_FreeVar _ _ _ _ x) = x
mergeId_Inh_FreeVar :: Inh_FreeVar -> (Int)
mergeId_Inh_FreeVar (Inh_FreeVar _ _ _ x _) = x
graph_Inh_FreeVar :: Inh_FreeVar -> (GinGraph)
graph_Inh_FreeVar (Inh_FreeVar _ _ x _ _) = x
currTaskName_Inh_FreeVar :: Inh_FreeVar -> (String)
currTaskName_Inh_FreeVar (Inh_FreeVar _ x _ _ _) = x
caseExpr_Inh_FreeVar :: Inh_FreeVar -> (Maybe Expression)
caseExpr_Inh_FreeVar (Inh_FreeVar x _ _ _ _) = x
recNode_Syn_FreeVar :: Syn_FreeVar -> (Bool)
recNode_Syn_FreeVar (Syn_FreeVar _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_FreeVar :: Syn_FreeVar -> ([Doc])
ppDebugs_Syn_FreeVar (Syn_FreeVar _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_FreeVar :: Syn_FreeVar -> (Doc)
ppDebug_Syn_FreeVar (Syn_FreeVar _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_FreeVar :: Syn_FreeVar -> ([Doc])
ppAgs_Syn_FreeVar (Syn_FreeVar _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_FreeVar :: Syn_FreeVar -> (Doc)
ppAg_Syn_FreeVar (Syn_FreeVar _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_FreeVar :: Syn_FreeVar -> (Maybe Int)
mExitId_Syn_FreeVar (Syn_FreeVar _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_FreeVar :: Syn_FreeVar -> (Maybe Int)
mEntryId_Syn_FreeVar (Syn_FreeVar _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_FreeVar :: Syn_FreeVar -> (Bool)
hasRecs_Syn_FreeVar (Syn_FreeVar _ _ x _ _ _ _ _ _ _) = x
graph_Syn_FreeVar :: Syn_FreeVar -> (GinGraph)
graph_Syn_FreeVar (Syn_FreeVar _ x _ _ _ _ _ _ _ _) = x
copy_Syn_FreeVar :: Syn_FreeVar -> (FreeVar)
copy_Syn_FreeVar (Syn_FreeVar x _ _ _ _ _ _ _ _ _) = x
wrap_FreeVar :: T_FreeVar  Inh_FreeVar  -> (Syn_FreeVar )
wrap_FreeVar (T_FreeVar act) (Inh_FreeVar alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_FreeVar_vIn19 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_FreeVar_s20 sem arg) >>= \ (T_FreeVar_vOut19 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_FreeVar alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_FreeVar :: FreeVar  -> T_FreeVar 
sem_FreeVar { FreeVar | fv_def_level = fv_def_level_,fv_ident = fv_ident_,fv_info_ptr = fv_info_ptr_,fv_count = fv_count_ } = sem_FreeVar_FreeVar fv_def_level_ ( sem_Ident fv_ident_ ) fv_info_ptr_ fv_count_

// semantic domain
attach_T_FreeVar (T_FreeVar t_FreeVar) = t_FreeVar
inv_FreeVar_s20 (C_FreeVar_s20 x) = x
sem_FreeVar_FreeVar  :: (Level) (T_Ident ) (VarInfoPtr) (Int) -> T_FreeVar 
sem_FreeVar_FreeVar arg_fv_def_level_ arg_fv_ident_ arg_fv_info_ptr_ arg_fv_count_ = T_FreeVar (lift st20) where
   st20 =
         let
             v19 (T_FreeVar_vIn19 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_fv_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_fv_ident_))
                           (T_Ident_vOut43 afv_identIcopy afv_identIgraph afv_identIhasRecs afv_identIident afv_identIisTask afv_identImEntryId afv_identImExitId afv_identIppAg afv_identIppAgs afv_identIppDebug afv_identIppDebugs afv_identIrecNode afv_identIreifyFunDef afv_identIreifyFunType afv_identIreifySymbolType) = inv_Ident_s44 st_fv_identX44 (T_Ident_vIn43 afv_identOcaseExpr afv_identOcurrTaskName afv_identOgraph afv_identOmergeId afv_identOmoduleEnv)
                           alhsOppDebug = rule607 afv_identIppDebug
                           alhsOppAg = rule608 afv_identIppAg
                           alhsOhasRecs = rule609 afv_identIhasRecs
                           alhsOmEntryId = rule610 afv_identImEntryId
                           alhsOmExitId = rule611 afv_identImExitId
                           alhsOppAgs = rule612 afv_identIppAgs
                           alhsOppDebugs = rule613 afv_identIppDebugs
                           alhsOrecNode = rule614 afv_identIrecNode
                           lcopy = rule615 afv_identIcopy arg_fv_count_ arg_fv_def_level_ arg_fv_info_ptr_
                           alhsOcopy = rule616 lcopy
                           alhsOgraph = rule617 afv_identIgraph
                           afv_identOcaseExpr = rule618 alhsIcaseExpr
                           afv_identOcurrTaskName = rule619 alhsIcurrTaskName
                           afv_identOgraph = rule620 alhsIgraph
                           afv_identOmergeId = rule621 alhsImergeId
                           afv_identOmoduleEnv = rule622 alhsImoduleEnv
                           ag__result_ = T_FreeVar_vOut19 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_FreeVar_s20 v19
   /*# LINE 112 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule607 ((afv_identIppDebug)) =
                            /*# LINE 112 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                            afv_identIppDebug
                            /*# LINE 3177 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 113 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule608 ((afv_identIppAg)) =
                            /*# LINE 113 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                            afv_identIppAg
                            /*# LINE 3182 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule609 ((afv_identIhasRecs)) =
     afv_identIhasRecs
   rule610 ((afv_identImEntryId)) =
     afv_identImEntryId
   rule611 ((afv_identImExitId)) =
     afv_identImExitId
   rule612 ((afv_identIppAgs)) =
     afv_identIppAgs
   rule613 ((afv_identIppDebugs)) =
     afv_identIppDebugs
   rule614 ((afv_identIrecNode)) =
     afv_identIrecNode
   rule615 ((afv_identIcopy)) fv_count_ fv_def_level_ fv_info_ptr_ =
     {FreeVar|fv_def_level = fv_def_level_ , fv_ident = afv_identIcopy , fv_info_ptr = fv_info_ptr_ , fv_count = fv_count_}
   rule616 lcopy =
     lcopy
   rule617 ((afv_identIgraph)) =
     afv_identIgraph
   rule618 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule619 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule620 ((alhsIgraph)) =
     alhsIgraph
   rule621 ((alhsImergeId)) =
     alhsImergeId
   rule622 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// FreeVars ----------------------------------------------------
// wrapper
moduleEnv_Inh_FreeVars :: Inh_FreeVars -> (ModuleEnv)
moduleEnv_Inh_FreeVars (Inh_FreeVars _ _ _ _ x) = x
mergeId_Inh_FreeVars :: Inh_FreeVars -> (Int)
mergeId_Inh_FreeVars (Inh_FreeVars _ _ _ x _) = x
graph_Inh_FreeVars :: Inh_FreeVars -> (GinGraph)
graph_Inh_FreeVars (Inh_FreeVars _ _ x _ _) = x
currTaskName_Inh_FreeVars :: Inh_FreeVars -> (String)
currTaskName_Inh_FreeVars (Inh_FreeVars _ x _ _ _) = x
caseExpr_Inh_FreeVars :: Inh_FreeVars -> (Maybe Expression)
caseExpr_Inh_FreeVars (Inh_FreeVars x _ _ _ _) = x
recNode_Syn_FreeVars :: Syn_FreeVars -> (Bool)
recNode_Syn_FreeVars (Syn_FreeVars _ _ _ _ _ x) = x
mExitId_Syn_FreeVars :: Syn_FreeVars -> (Maybe Int)
mExitId_Syn_FreeVars (Syn_FreeVars _ _ _ _ x _) = x
mEntryId_Syn_FreeVars :: Syn_FreeVars -> (Maybe Int)
mEntryId_Syn_FreeVars (Syn_FreeVars _ _ _ x _ _) = x
hasRecs_Syn_FreeVars :: Syn_FreeVars -> (Bool)
hasRecs_Syn_FreeVars (Syn_FreeVars _ _ x _ _ _) = x
graph_Syn_FreeVars :: Syn_FreeVars -> (GinGraph)
graph_Syn_FreeVars (Syn_FreeVars _ x _ _ _ _) = x
copy_Syn_FreeVars :: Syn_FreeVars -> (FreeVars)
copy_Syn_FreeVars (Syn_FreeVars x _ _ _ _ _) = x
wrap_FreeVars :: T_FreeVars  Inh_FreeVars  -> (Syn_FreeVars )
wrap_FreeVars (T_FreeVars act) (Inh_FreeVars alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_FreeVars_s23 sem arg) >>= \ (T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode) ->
     lift (Syn_FreeVars alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode)
   )

// cata
sem_FreeVars :: FreeVars  -> T_FreeVars 
sem_FreeVars list = foldr sem_FreeVars_Cons sem_FreeVars_Nil (map sem_FreeVar list)

// semantic domain
attach_T_FreeVars (T_FreeVars t_FreeVars) = t_FreeVars
inv_FreeVars_s23 (C_FreeVars_s23 x) = x
sem_FreeVars_Cons  :: (T_FreeVar ) (T_FreeVars ) -> T_FreeVars 
sem_FreeVars_Cons arg_hd_ arg_tl_ = T_FreeVars (lift st23) where
   st23 =
         let
             v22 (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX20 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVar (arg_hd_))
                           st_tlX23 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVars (arg_tl_))
                           (T_FreeVar_vOut19 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_FreeVar_s20 st_hdX20 (T_FreeVar_vIn19 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_FreeVars_vOut22 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIrecNode) = inv_FreeVars_s23 st_tlX23 (T_FreeVars_vIn22 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs = rule623 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule624 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule625 ahdImExitId atlImExitId
                           alhsOrecNode = rule626 ahdIrecNode atlIrecNode
                           lcopy = rule627 ahdIcopy atlIcopy
                           alhsOcopy = rule628 lcopy
                           alhsOgraph = rule629 atlIgraph
                           ahdOcaseExpr = rule630 alhsIcaseExpr
                           ahdOcurrTaskName = rule631 alhsIcurrTaskName
                           ahdOgraph = rule632 alhsIgraph
                           ahdOmergeId = rule633 alhsImergeId
                           ahdOmoduleEnv = rule634 alhsImoduleEnv
                           atlOcaseExpr = rule635 alhsIcaseExpr
                           atlOcurrTaskName = rule636 alhsIcurrTaskName
                           atlOgraph = rule637 ahdIgraph
                           atlOmergeId = rule638 alhsImergeId
                           atlOmoduleEnv = rule639 alhsImoduleEnv
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_FreeVars_s23 v22
   rule623 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule624 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule625 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule626 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule627 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule628 lcopy =
     lcopy
   rule629 ((atlIgraph)) =
     atlIgraph
   rule630 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule631 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule632 ((alhsIgraph)) =
     alhsIgraph
   rule633 ((alhsImergeId)) =
     alhsImergeId
   rule634 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule635 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule636 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule637 ((ahdIgraph)) =
     ahdIgraph
   rule638 ((alhsImergeId)) =
     alhsImergeId
   rule639 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_FreeVars_Nil  ::   T_FreeVars 
sem_FreeVars_Nil  = T_FreeVars (lift st23) where
   st23 =
         let
             v22 (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule640  Void
                           alhsOmEntryId = rule641  Void
                           alhsOmExitId = rule642  Void
                           alhsOrecNode = rule643  Void
                           lcopy = rule644  Void
                           alhsOcopy = rule645 lcopy
                           alhsOgraph = rule646 alhsIgraph
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_FreeVars_s23 v22
   rule640  (_) =
     False
   rule641  (_) =
     Nothing
   rule642  (_) =
     Nothing
   rule643  (_) =
     False
   rule644  (_) =
     []
   rule645 lcopy =
     lcopy
   rule646 ((alhsIgraph)) =
     alhsIgraph

// GExpression -------------------------------------------------
// wrapper
moduleEnv_Inh_GExpression :: Inh_GExpression -> (ModuleEnv)
moduleEnv_Inh_GExpression (Inh_GExpression _ _ _ _ x) = x
mergeId_Inh_GExpression :: Inh_GExpression -> (Int)
mergeId_Inh_GExpression (Inh_GExpression _ _ _ x _) = x
graph_Inh_GExpression :: Inh_GExpression -> (GinGraph)
graph_Inh_GExpression (Inh_GExpression _ _ x _ _) = x
currTaskName_Inh_GExpression :: Inh_GExpression -> (String)
currTaskName_Inh_GExpression (Inh_GExpression _ x _ _ _) = x
caseExpr_Inh_GExpression :: Inh_GExpression -> (Maybe Expression)
caseExpr_Inh_GExpression (Inh_GExpression x _ _ _ _) = x
recNode_Syn_GExpression :: Syn_GExpression -> (Bool)
recNode_Syn_GExpression (Syn_GExpression _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_GExpression :: Syn_GExpression -> ([Doc])
ppDebugs_Syn_GExpression (Syn_GExpression _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_GExpression :: Syn_GExpression -> (Doc)
ppDebug_Syn_GExpression (Syn_GExpression _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_GExpression :: Syn_GExpression -> ([Doc])
ppAgs_Syn_GExpression (Syn_GExpression _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_GExpression :: Syn_GExpression -> (Doc)
ppAg_Syn_GExpression (Syn_GExpression _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_GExpression :: Syn_GExpression -> (Maybe Int)
mExitId_Syn_GExpression (Syn_GExpression _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_GExpression :: Syn_GExpression -> (Maybe Int)
mEntryId_Syn_GExpression (Syn_GExpression _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_GExpression :: Syn_GExpression -> (Bool)
hasRecs_Syn_GExpression (Syn_GExpression _ _ x _ _ _ _ _ _ _) = x
graph_Syn_GExpression :: Syn_GExpression -> (GinGraph)
graph_Syn_GExpression (Syn_GExpression _ x _ _ _ _ _ _ _ _) = x
copy_Syn_GExpression :: Syn_GExpression -> (GExpression)
copy_Syn_GExpression (Syn_GExpression x _ _ _ _ _ _ _ _ _) = x
wrap_GExpression :: T_GExpression  Inh_GExpression  -> (Syn_GExpression )
wrap_GExpression (T_GExpression act) (Inh_GExpression alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GExpression_s26 sem arg) >>= \ (T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GExpression alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GExpression :: GExpression  -> T_GExpression 
sem_GExpression ( GUndefinedExpression  ) = sem_GExpression_GUndefinedExpression 
sem_GExpression ( GGraphExpression gg_ ) = sem_GExpression_GGraphExpression gg_
sem_GExpression ( GListExpression gexprs_ ) = sem_GExpression_GListExpression gexprs_
sem_GExpression ( GCleanExpression gcexpr_ ) = sem_GExpression_GCleanExpression gcexpr_

// semantic domain
attach_T_GExpression (T_GExpression t_GExpression) = t_GExpression
inv_GExpression_s26 (C_GExpression_s26 x) = x
sem_GExpression_GUndefinedExpression  ::   T_GExpression 
sem_GExpression_GUndefinedExpression  = T_GExpression (lift st26) where
   st26 =
         let
             v25 (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule647  Void
                           alhsOppAg = rule648  Void
                           alhsOhasRecs = rule649  Void
                           alhsOmEntryId = rule650  Void
                           alhsOmExitId = rule651  Void
                           alhsOppAgs = rule652  Void
                           alhsOppDebugs = rule653  Void
                           alhsOrecNode = rule654  Void
                           lcopy = rule655  Void
                           alhsOcopy = rule656 lcopy
                           alhsOgraph = rule657 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s26 v25
   /*# LINE 146 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule647  (_) =
                                          /*# LINE 146 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3422 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 147 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule648  (_) =
                                          /*# LINE 147 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3427 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule649  (_) =
     False
   rule650  (_) =
     Nothing
   rule651  (_) =
     Nothing
   rule652  (_) =
     []
   rule653  (_) =
     []
   rule654  (_) =
     False
   rule655  (_) =
     GUndefinedExpression
   rule656 lcopy =
     lcopy
   rule657 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GGraphExpression  :: (GGraph) -> T_GExpression 
sem_GExpression_GGraphExpression arg_gg_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule658  Void
                           alhsOppAg = rule659  Void
                           alhsOhasRecs = rule660  Void
                           alhsOmEntryId = rule661  Void
                           alhsOmExitId = rule662  Void
                           alhsOppAgs = rule663  Void
                           alhsOppDebugs = rule664  Void
                           alhsOrecNode = rule665  Void
                           lcopy = rule666 arg_gg_
                           alhsOcopy = rule667 lcopy
                           alhsOgraph = rule668 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s26 v25
   /*# LINE 148 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule658  (_) =
                                          /*# LINE 148 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3470 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 149 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule659  (_) =
                                          /*# LINE 149 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3475 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule660  (_) =
     False
   rule661  (_) =
     Nothing
   rule662  (_) =
     Nothing
   rule663  (_) =
     []
   rule664  (_) =
     []
   rule665  (_) =
     False
   rule666 gg_ =
     GGraphExpression gg_
   rule667 lcopy =
     lcopy
   rule668 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GListExpression  :: ([GExpression]) -> T_GExpression 
sem_GExpression_GListExpression arg_gexprs_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule669  Void
                           alhsOppAg = rule670  Void
                           alhsOhasRecs = rule671  Void
                           alhsOmEntryId = rule672  Void
                           alhsOmExitId = rule673  Void
                           alhsOppAgs = rule674  Void
                           alhsOppDebugs = rule675  Void
                           alhsOrecNode = rule676  Void
                           lcopy = rule677 arg_gexprs_
                           alhsOcopy = rule678 lcopy
                           alhsOgraph = rule679 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s26 v25
   /*# LINE 150 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule669  (_) =
                                          /*# LINE 150 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3518 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 151 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule670  (_) =
                                          /*# LINE 151 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3523 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule671  (_) =
     False
   rule672  (_) =
     Nothing
   rule673  (_) =
     Nothing
   rule674  (_) =
     []
   rule675  (_) =
     []
   rule676  (_) =
     False
   rule677 gexprs_ =
     GListExpression gexprs_
   rule678 lcopy =
     lcopy
   rule679 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GCleanExpression  :: (GCleanExpression) -> T_GExpression 
sem_GExpression_GCleanExpression arg_gcexpr_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule680 arg_gcexpr_
                           alhsOppAg = rule681 arg_gcexpr_
                           alhsOhasRecs = rule682  Void
                           alhsOmEntryId = rule683  Void
                           alhsOmExitId = rule684  Void
                           alhsOppAgs = rule685  Void
                           alhsOppDebugs = rule686  Void
                           alhsOrecNode = rule687  Void
                           lcopy = rule688 arg_gcexpr_
                           alhsOcopy = rule689 lcopy
                           alhsOgraph = rule690 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s26 v25
   /*# LINE 152 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule680 gcexpr_ =
                                          /*# LINE 152 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3566 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 153 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule681 gcexpr_ =
                                          /*# LINE 153 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3571 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule682  (_) =
     False
   rule683  (_) =
     Nothing
   rule684  (_) =
     Nothing
   rule685  (_) =
     []
   rule686  (_) =
     []
   rule687  (_) =
     False
   rule688 gcexpr_ =
     GCleanExpression gcexpr_
   rule689 lcopy =
     lcopy
   rule690 ((alhsIgraph)) =
     alhsIgraph

// GFunDef -----------------------------------------------------
// wrapper
moduleEnv_Inh_GFunDef :: Inh_GFunDef -> (ModuleEnv)
moduleEnv_Inh_GFunDef (Inh_GFunDef _ _ _ _ x) = x
mergeId_Inh_GFunDef :: Inh_GFunDef -> (Int)
mergeId_Inh_GFunDef (Inh_GFunDef _ _ _ x _) = x
graph_Inh_GFunDef :: Inh_GFunDef -> (GinGraph)
graph_Inh_GFunDef (Inh_GFunDef _ _ x _ _) = x
currTaskName_Inh_GFunDef :: Inh_GFunDef -> (String)
currTaskName_Inh_GFunDef (Inh_GFunDef _ x _ _ _) = x
caseExpr_Inh_GFunDef :: Inh_GFunDef -> (Maybe Expression)
caseExpr_Inh_GFunDef (Inh_GFunDef x _ _ _ _) = x
recNode_Syn_GFunDef :: Syn_GFunDef -> (Bool)
recNode_Syn_GFunDef (Syn_GFunDef _ _ _ _ _ _ _ x) = x
mExitId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
mExitId_Syn_GFunDef (Syn_GFunDef _ _ _ _ _ _ x _) = x
mEntryId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
mEntryId_Syn_GFunDef (Syn_GFunDef _ _ _ _ _ x _ _) = x
hasRecs_Syn_GFunDef :: Syn_GFunDef -> (Bool)
hasRecs_Syn_GFunDef (Syn_GFunDef _ _ _ _ x _ _ _) = x
graph_Syn_GFunDef :: Syn_GFunDef -> (GinGraph)
graph_Syn_GFunDef (Syn_GFunDef _ _ _ x _ _ _ _) = x
funRhs_Syn_GFunDef :: Syn_GFunDef -> (Expression)
funRhs_Syn_GFunDef (Syn_GFunDef _ _ x _ _ _ _ _) = x
funArgs_Syn_GFunDef :: Syn_GFunDef -> ([FreeVar])
funArgs_Syn_GFunDef (Syn_GFunDef _ x _ _ _ _ _ _) = x
copy_Syn_GFunDef :: Syn_GFunDef -> (GFunDef)
copy_Syn_GFunDef (Syn_GFunDef x _ _ _ _ _ _ _) = x
wrap_GFunDef :: T_GFunDef  Inh_GFunDef  -> (Syn_GFunDef )
wrap_GFunDef (T_GFunDef act) (Inh_GFunDef alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GFunDef_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GFunDef_s29 sem arg) >>= \ (T_GFunDef_vOut28 alhsOcopy alhsOfunArgs alhsOfunRhs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode) ->
     lift (Syn_GFunDef alhsOcopy alhsOfunArgs alhsOfunRhs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode)
   )

// cata
sem_GFunDef :: GFunDef  -> T_GFunDef 
sem_GFunDef { GFunDef | gfd_name = gfd_name_,gfd_args = gfd_args_,gfd_rhs = gfd_rhs_,gfd_type = gfd_type_,gfd_priority = gfd_priority_ } = sem_GFunDef_GFunDef gfd_name_ ( sem_FreeVars gfd_args_ ) ( sem_Expression gfd_rhs_ ) gfd_type_ gfd_priority_

// semantic domain
attach_T_GFunDef (T_GFunDef t_GFunDef) = t_GFunDef
inv_GFunDef_s29 (C_GFunDef_s29 x) = x
sem_GFunDef_GFunDef  :: (String) (T_FreeVars ) (T_Expression ) (Optional SymbolType) (Priority) -> T_GFunDef 
sem_GFunDef_GFunDef arg_gfd_name_ arg_gfd_args_ arg_gfd_rhs_ arg_gfd_type_ arg_gfd_priority_ = T_GFunDef (lift st29) where
   st29 =
         let
             v28 (T_GFunDef_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gfd_argsX23 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVars (arg_gfd_args_))
                           st_gfd_rhsX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_gfd_rhs_))
                           (T_FreeVars_vOut22 agfd_argsIcopy agfd_argsIgraph agfd_argsIhasRecs agfd_argsImEntryId agfd_argsImExitId agfd_argsIrecNode) = inv_FreeVars_s23 st_gfd_argsX23 (T_FreeVars_vIn22 agfd_argsOcaseExpr agfd_argsOcurrTaskName agfd_argsOgraph agfd_argsOmergeId agfd_argsOmoduleEnv)
                           (T_Expression_vOut13 agfd_rhsIcopy agfd_rhsIgraph agfd_rhsIhasRecs agfd_rhsImEntryId agfd_rhsImExitId agfd_rhsIppAg agfd_rhsIppAgs agfd_rhsIppDebug agfd_rhsIppDebugs agfd_rhsIrecNode) = inv_Expression_s14 st_gfd_rhsX14 (T_Expression_vIn13 agfd_rhsOcaseExpr agfd_rhsOcurrTaskName agfd_rhsOgraph agfd_rhsOmergeId agfd_rhsOmoduleEnv)
                           alhsOfunArgs = rule691 agfd_argsIcopy
                           alhsOfunRhs = rule692 agfd_rhsIcopy
                           alhsOmEntryId = rule693 agfd_rhsImEntryId
                           alhsOmExitId = rule694 agfd_rhsImExitId
                           agfd_rhsOgraph = rule695 alhsIgraph
                           alhsOgraph = rule696 agfd_rhsIgraph
                           alhsOhasRecs = rule697 agfd_argsIhasRecs agfd_rhsIhasRecs
                           alhsOrecNode = rule698 agfd_argsIrecNode agfd_rhsIrecNode
                           lcopy = rule699 agfd_argsIcopy agfd_rhsIcopy arg_gfd_name_ arg_gfd_priority_ arg_gfd_type_
                           alhsOcopy = rule700 lcopy
                           agfd_argsOcaseExpr = rule701 alhsIcaseExpr
                           agfd_argsOcurrTaskName = rule702 alhsIcurrTaskName
                           agfd_argsOgraph = rule703 alhsIgraph
                           agfd_argsOmergeId = rule704 alhsImergeId
                           agfd_argsOmoduleEnv = rule705 alhsImoduleEnv
                           agfd_rhsOcaseExpr = rule706 alhsIcaseExpr
                           agfd_rhsOcurrTaskName = rule707 alhsIcurrTaskName
                           agfd_rhsOmergeId = rule708 alhsImergeId
                           agfd_rhsOmoduleEnv = rule709 alhsImoduleEnv
                           ag__result_ = T_GFunDef_vOut28 alhsOcopy alhsOfunArgs alhsOfunRhs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_GFunDef_s29 v28
   /*# LINE 108 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule691 ((agfd_argsIcopy)) =
                      /*# LINE 108 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                      agfd_argsIcopy
                      /*# LINE 3671 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 109 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule692 ((agfd_rhsIcopy)) =
                      /*# LINE 109 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                      agfd_rhsIcopy
                      /*# LINE 3676 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 111 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule693 ((agfd_rhsImEntryId)) =
                       /*# LINE 111 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImEntryId
                       /*# LINE 3681 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 112 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule694 ((agfd_rhsImExitId)) =
                       /*# LINE 112 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImExitId
                       /*# LINE 3686 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 114 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule695 ((alhsIgraph)) =
                        /*# LINE 114 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        alhsIgraph
                        /*# LINE 3691 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 115 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule696 ((agfd_rhsIgraph)) =
                        /*# LINE 115 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                        agfd_rhsIgraph
                        /*# LINE 3696 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule697 ((agfd_argsIhasRecs)) ((agfd_rhsIhasRecs)) =
     agfd_argsIhasRecs || agfd_rhsIhasRecs
   rule698 ((agfd_argsIrecNode)) ((agfd_rhsIrecNode)) =
     agfd_argsIrecNode || agfd_rhsIrecNode
   rule699 ((agfd_argsIcopy)) ((agfd_rhsIcopy)) gfd_name_ gfd_priority_ gfd_type_ =
     {GFunDef|gfd_name = gfd_name_ , gfd_args = agfd_argsIcopy , gfd_rhs = agfd_rhsIcopy , gfd_type = gfd_type_ , gfd_priority = gfd_priority_}
   rule700 lcopy =
     lcopy
   rule701 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule702 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule703 ((alhsIgraph)) =
     alhsIgraph
   rule704 ((alhsImergeId)) =
     alhsImergeId
   rule705 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule706 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule707 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule708 ((alhsImergeId)) =
     alhsImergeId
   rule709 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// GLet --------------------------------------------------------
// wrapper
moduleEnv_Inh_GLet :: Inh_GLet -> (ModuleEnv)
moduleEnv_Inh_GLet (Inh_GLet _ _ _ _ x) = x
mergeId_Inh_GLet :: Inh_GLet -> (Int)
mergeId_Inh_GLet (Inh_GLet _ _ _ x _) = x
graph_Inh_GLet :: Inh_GLet -> (GinGraph)
graph_Inh_GLet (Inh_GLet _ _ x _ _) = x
currTaskName_Inh_GLet :: Inh_GLet -> (String)
currTaskName_Inh_GLet (Inh_GLet _ x _ _ _) = x
caseExpr_Inh_GLet :: Inh_GLet -> (Maybe Expression)
caseExpr_Inh_GLet (Inh_GLet x _ _ _ _) = x
recNode_Syn_GLet :: Syn_GLet -> (Bool)
recNode_Syn_GLet (Syn_GLet _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_GLet :: Syn_GLet -> ([Doc])
ppDebugs_Syn_GLet (Syn_GLet _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_GLet :: Syn_GLet -> (Doc)
ppDebug_Syn_GLet (Syn_GLet _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_GLet :: Syn_GLet -> ([Doc])
ppAgs_Syn_GLet (Syn_GLet _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_GLet :: Syn_GLet -> (Doc)
ppAg_Syn_GLet (Syn_GLet _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_GLet :: Syn_GLet -> (Maybe Int)
mExitId_Syn_GLet (Syn_GLet _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_GLet :: Syn_GLet -> (Maybe Int)
mEntryId_Syn_GLet (Syn_GLet _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_GLet :: Syn_GLet -> (Bool)
hasRecs_Syn_GLet (Syn_GLet _ _ x _ _ _ _ _ _ _) = x
graph_Syn_GLet :: Syn_GLet -> (GinGraph)
graph_Syn_GLet (Syn_GLet _ x _ _ _ _ _ _ _ _) = x
copy_Syn_GLet :: Syn_GLet -> (GLet)
copy_Syn_GLet (Syn_GLet x _ _ _ _ _ _ _ _ _) = x
wrap_GLet :: T_GLet  Inh_GLet  -> (Syn_GLet )
wrap_GLet (T_GLet act) (Inh_GLet alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GLet_vIn31 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLet_s32 sem arg) >>= \ (T_GLet_vOut31 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLet alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLet :: GLet  -> T_GLet 
sem_GLet { GLet | glet_binds = glet_binds_,glet_expr = glet_expr_ } = sem_GLet_GLet ( sem_GLetBinds glet_binds_ ) ( sem_Expression glet_expr_ )

// semantic domain
attach_T_GLet (T_GLet t_GLet) = t_GLet
inv_GLet_s32 (C_GLet_s32 x) = x
sem_GLet_GLet  :: (T_GLetBinds ) (T_Expression ) -> T_GLet 
sem_GLet_GLet arg_glet_binds_ arg_glet_expr_ = T_GLet (lift st32) where
   st32 =
         let
             v31 (T_GLet_vIn31 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_glet_bindsX38 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_glet_binds_))
                           st_glet_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glet_expr_))
                           (T_GLetBinds_vOut37 aglet_bindsIcopy aglet_bindsIgraph aglet_bindsIhasRecs aglet_bindsImCaseVarExpr aglet_bindsImEntryId aglet_bindsImExitId aglet_bindsIppAg aglet_bindsIppAgs aglet_bindsIppDebug aglet_bindsIppDebugs aglet_bindsIrecNode) = inv_GLetBinds_s38 st_glet_bindsX38 (T_GLetBinds_vIn37 aglet_bindsOcaseExpr aglet_bindsOcurrTaskName aglet_bindsOgraph aglet_bindsOmergeId aglet_bindsOmoduleEnv)
                           (T_Expression_vOut13 aglet_exprIcopy aglet_exprIgraph aglet_exprIhasRecs aglet_exprImEntryId aglet_exprImExitId aglet_exprIppAg aglet_exprIppAgs aglet_exprIppDebug aglet_exprIppDebugs aglet_exprIrecNode) = inv_Expression_s14 st_glet_exprX14 (T_Expression_vIn13 aglet_exprOcaseExpr aglet_exprOcurrTaskName aglet_exprOgraph aglet_exprOmergeId aglet_exprOmoduleEnv)
                           alhsOgraph = rule710 aglet_bindsIcopy aglet_exprIgraph lconnId lmCaseVarExpr
                           lmCaseVarExpr = rule711 aglet_bindsImCaseVarExpr
                           aglet_exprOcaseExpr = rule712 lmCaseVarExpr
                           alhsOrecNode = rule713  Void
                           lconnId = rule714 aglet_exprImEntryId aglet_exprIrecNode alhsImergeId
                           alhsOppDebug = rule715 aglet_bindsIppDebugs
                           alhsOppAg = rule716 aglet_bindsIppAgs
                           alhsOhasRecs = rule717 aglet_bindsIhasRecs aglet_exprIhasRecs
                           alhsOmEntryId = rule718 aglet_bindsImEntryId aglet_exprImEntryId
                           alhsOmExitId = rule719 aglet_bindsImExitId aglet_exprImExitId
                           alhsOppAgs = rule720 aglet_bindsIppAgs aglet_exprIppAgs
                           alhsOppDebugs = rule721 aglet_bindsIppDebugs aglet_exprIppDebugs
                           lcopy = rule722 aglet_bindsIcopy aglet_exprIcopy
                           alhsOcopy = rule723 lcopy
                           aglet_bindsOcaseExpr = rule724 alhsIcaseExpr
                           aglet_bindsOcurrTaskName = rule725 alhsIcurrTaskName
                           aglet_bindsOgraph = rule726 alhsIgraph
                           aglet_bindsOmergeId = rule727 alhsImergeId
                           aglet_bindsOmoduleEnv = rule728 alhsImoduleEnv
                           aglet_exprOcurrTaskName = rule729 alhsIcurrTaskName
                           aglet_exprOgraph = rule730 aglet_bindsIgraph
                           aglet_exprOmergeId = rule731 alhsImergeId
                           aglet_exprOmoduleEnv = rule732 alhsImoduleEnv
                           ag__result_ = T_GLet_vOut31 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLet_s32 v31
   /*# LINE 240 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule710 ((aglet_bindsIcopy)) ((aglet_exprIgraph)) lconnId lmCaseVarExpr =
                    /*# LINE 240 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                    case lmCaseVarExpr     of
                      Just e  -> aglet_exprIgraph
                      _       -> let (lid, g)  = addNode (GLet aglet_bindsIcopy) aglet_exprIgraph
                                     err       = abort "Failed to add let edge; no synthesized ID from let body"
                                 in maybe err (\n -> addEmptyEdge (lid, n) g) lconnId
                    /*# LINE 3816 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 247 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule711 ((aglet_bindsImCaseVarExpr)) =
                           /*# LINE 247 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                           aglet_bindsImCaseVarExpr
                           /*# LINE 3821 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 249 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule712 lmCaseVarExpr =
                             /*# LINE 249 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                             lmCaseVarExpr
                             /*# LINE 3826 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 251 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule713  (_) =
                      /*# LINE 251 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                      False
                      /*# LINE 3831 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 253 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule714 ((aglet_exprImEntryId)) ((aglet_exprIrecNode)) ((alhsImergeId)) =
                     /*# LINE 253 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                     if aglet_exprIrecNode (Just alhsImergeId) aglet_exprImEntryId
                     /*# LINE 3836 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 156 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule715 ((aglet_bindsIppDebugs)) =
                         /*# LINE 156 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppDebugs
                         /*# LINE 3841 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 157 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule716 ((aglet_bindsIppAgs)) =
                         /*# LINE 157 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppAgs
                         /*# LINE 3846 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule717 ((aglet_bindsIhasRecs)) ((aglet_exprIhasRecs)) =
     aglet_bindsIhasRecs || aglet_exprIhasRecs
   rule718 ((aglet_bindsImEntryId)) ((aglet_exprImEntryId)) =
     aglet_bindsImEntryId <> aglet_exprImEntryId
   rule719 ((aglet_bindsImExitId)) ((aglet_exprImExitId)) =
     aglet_bindsImExitId <> aglet_exprImExitId
   rule720 ((aglet_bindsIppAgs)) ((aglet_exprIppAgs)) =
     aglet_bindsIppAgs ++ aglet_exprIppAgs
   rule721 ((aglet_bindsIppDebugs)) ((aglet_exprIppDebugs)) =
     aglet_bindsIppDebugs ++ aglet_exprIppDebugs
   rule722 ((aglet_bindsIcopy)) ((aglet_exprIcopy)) =
     {GLet|glet_binds = aglet_bindsIcopy , glet_expr = aglet_exprIcopy}
   rule723 lcopy =
     lcopy
   rule724 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule725 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule726 ((alhsIgraph)) =
     alhsIgraph
   rule727 ((alhsImergeId)) =
     alhsImergeId
   rule728 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule729 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule730 ((aglet_bindsIgraph)) =
     aglet_bindsIgraph
   rule731 ((alhsImergeId)) =
     alhsImergeId
   rule732 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// GLetBind ----------------------------------------------------
// wrapper
moduleEnv_Inh_GLetBind :: Inh_GLetBind -> (ModuleEnv)
moduleEnv_Inh_GLetBind (Inh_GLetBind _ _ _ _ x) = x
mergeId_Inh_GLetBind :: Inh_GLetBind -> (Int)
mergeId_Inh_GLetBind (Inh_GLetBind _ _ _ x _) = x
graph_Inh_GLetBind :: Inh_GLetBind -> (GinGraph)
graph_Inh_GLetBind (Inh_GLetBind _ _ x _ _) = x
currTaskName_Inh_GLetBind :: Inh_GLetBind -> (String)
currTaskName_Inh_GLetBind (Inh_GLetBind _ x _ _ _) = x
caseExpr_Inh_GLetBind :: Inh_GLetBind -> (Maybe Expression)
caseExpr_Inh_GLetBind (Inh_GLetBind x _ _ _ _) = x
recNode_Syn_GLetBind :: Syn_GLetBind -> (Bool)
recNode_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_GLetBind :: Syn_GLetBind -> ([Doc])
ppDebugs_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_GLetBind :: Syn_GLetBind -> (Doc)
ppDebug_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_GLetBind :: Syn_GLetBind -> ([Doc])
ppAgs_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_GLetBind :: Syn_GLetBind -> (Doc)
ppAg_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_GLetBind :: Syn_GLetBind -> (Maybe Int)
mExitId_Syn_GLetBind (Syn_GLetBind _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_GLetBind :: Syn_GLetBind -> (Maybe Int)
mEntryId_Syn_GLetBind (Syn_GLetBind _ _ _ _ x _ _ _ _ _ _) = x
mCaseVarExpr_Syn_GLetBind :: Syn_GLetBind -> (Maybe Expression)
mCaseVarExpr_Syn_GLetBind (Syn_GLetBind _ _ _ x _ _ _ _ _ _ _) = x
hasRecs_Syn_GLetBind :: Syn_GLetBind -> (Bool)
hasRecs_Syn_GLetBind (Syn_GLetBind _ _ x _ _ _ _ _ _ _ _) = x
graph_Syn_GLetBind :: Syn_GLetBind -> (GinGraph)
graph_Syn_GLetBind (Syn_GLetBind _ x _ _ _ _ _ _ _ _ _) = x
copy_Syn_GLetBind :: Syn_GLetBind -> (GLetBind)
copy_Syn_GLetBind (Syn_GLetBind x _ _ _ _ _ _ _ _ _ _) = x
wrap_GLetBind :: T_GLetBind  Inh_GLetBind  -> (Syn_GLetBind )
wrap_GLetBind (T_GLetBind act) (Inh_GLetBind alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GLetBind_vIn34 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLetBind_s35 sem arg) >>= \ (T_GLetBind_vOut34 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLetBind alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLetBind :: GLetBind  -> T_GLetBind 
sem_GLetBind { GLetBind | glb_dst = glb_dst_,glb_src = glb_src_ } = sem_GLetBind_GLetBind glb_dst_ ( sem_Expression glb_src_ )

// semantic domain
attach_T_GLetBind (T_GLetBind t_GLetBind) = t_GLetBind
inv_GLetBind_s35 (C_GLetBind_s35 x) = x
sem_GLetBind_GLetBind  :: (String) (T_Expression ) -> T_GLetBind 
sem_GLetBind_GLetBind arg_glb_dst_ arg_glb_src_ = T_GLetBind (lift st35) where
   st35 =
         let
             v34 (T_GLetBind_vIn34 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_glb_srcX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glb_src_))
                           (T_Expression_vOut13 aglb_srcIcopy aglb_srcIgraph aglb_srcIhasRecs aglb_srcImEntryId aglb_srcImExitId aglb_srcIppAg aglb_srcIppAgs aglb_srcIppDebug aglb_srcIppDebugs aglb_srcIrecNode) = inv_Expression_s14 st_glb_srcX14 (T_Expression_vIn13 aglb_srcOcaseExpr aglb_srcOcurrTaskName aglb_srcOgraph aglb_srcOmergeId aglb_srcOmoduleEnv)
                           alhsOmCaseVarExpr = rule733 aglb_srcIcopy arg_glb_dst_
                           alhsOppDebug = rule734 aglb_srcIppDebug arg_glb_dst_
                           alhsOppAg = rule735 aglb_srcIppAg arg_glb_dst_
                           alhsOhasRecs = rule736 aglb_srcIhasRecs
                           alhsOmEntryId = rule737 aglb_srcImEntryId
                           alhsOmExitId = rule738 aglb_srcImExitId
                           alhsOppAgs = rule739 aglb_srcIppAgs
                           alhsOppDebugs = rule740 aglb_srcIppDebugs
                           alhsOrecNode = rule741 aglb_srcIrecNode
                           lcopy = rule742 aglb_srcIcopy arg_glb_dst_
                           alhsOcopy = rule743 lcopy
                           alhsOgraph = rule744 aglb_srcIgraph
                           aglb_srcOcaseExpr = rule745 alhsIcaseExpr
                           aglb_srcOcurrTaskName = rule746 alhsIcurrTaskName
                           aglb_srcOgraph = rule747 alhsIgraph
                           aglb_srcOmergeId = rule748 alhsImergeId
                           aglb_srcOmoduleEnv = rule749 alhsImoduleEnv
                           ag__result_ = T_GLetBind_vOut34 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBind_s35 v34
   /*# LINE 263 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule733 ((aglb_srcIcopy)) glb_dst_ =
                                  /*# LINE 263 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                                  if (glb_dst_ == "_case_var") (Just aglb_srcIcopy) Nothing
                                  /*# LINE 3962 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 160 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule734 ((aglb_srcIppDebug)) glb_dst_ =
                             /*# LINE 160 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppDebug
                             /*# LINE 3967 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 161 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule735 ((aglb_srcIppAg)) glb_dst_ =
                             /*# LINE 161 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppAg
                             /*# LINE 3972 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule736 ((aglb_srcIhasRecs)) =
     aglb_srcIhasRecs
   rule737 ((aglb_srcImEntryId)) =
     aglb_srcImEntryId
   rule738 ((aglb_srcImExitId)) =
     aglb_srcImExitId
   rule739 ((aglb_srcIppAgs)) =
     aglb_srcIppAgs
   rule740 ((aglb_srcIppDebugs)) =
     aglb_srcIppDebugs
   rule741 ((aglb_srcIrecNode)) =
     aglb_srcIrecNode
   rule742 ((aglb_srcIcopy)) glb_dst_ =
     {GLetBind|glb_dst = glb_dst_ , glb_src = aglb_srcIcopy}
   rule743 lcopy =
     lcopy
   rule744 ((aglb_srcIgraph)) =
     aglb_srcIgraph
   rule745 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule746 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule747 ((alhsIgraph)) =
     alhsIgraph
   rule748 ((alhsImergeId)) =
     alhsImergeId
   rule749 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// GLetBinds ---------------------------------------------------
// wrapper
moduleEnv_Inh_GLetBinds :: Inh_GLetBinds -> (ModuleEnv)
moduleEnv_Inh_GLetBinds (Inh_GLetBinds _ _ _ _ x) = x
mergeId_Inh_GLetBinds :: Inh_GLetBinds -> (Int)
mergeId_Inh_GLetBinds (Inh_GLetBinds _ _ _ x _) = x
graph_Inh_GLetBinds :: Inh_GLetBinds -> (GinGraph)
graph_Inh_GLetBinds (Inh_GLetBinds _ _ x _ _) = x
currTaskName_Inh_GLetBinds :: Inh_GLetBinds -> (String)
currTaskName_Inh_GLetBinds (Inh_GLetBinds _ x _ _ _) = x
caseExpr_Inh_GLetBinds :: Inh_GLetBinds -> (Maybe Expression)
caseExpr_Inh_GLetBinds (Inh_GLetBinds x _ _ _ _) = x
recNode_Syn_GLetBinds :: Syn_GLetBinds -> (Bool)
recNode_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_GLetBinds :: Syn_GLetBinds -> ([Doc])
ppDebugs_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_GLetBinds :: Syn_GLetBinds -> (Doc)
ppDebug_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_GLetBinds :: Syn_GLetBinds -> ([Doc])
ppAgs_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_GLetBinds :: Syn_GLetBinds -> (Doc)
ppAg_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Int)
mExitId_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Int)
mEntryId_Syn_GLetBinds (Syn_GLetBinds _ _ _ _ x _ _ _ _ _ _) = x
mCaseVarExpr_Syn_GLetBinds :: Syn_GLetBinds -> (Maybe Expression)
mCaseVarExpr_Syn_GLetBinds (Syn_GLetBinds _ _ _ x _ _ _ _ _ _ _) = x
hasRecs_Syn_GLetBinds :: Syn_GLetBinds -> (Bool)
hasRecs_Syn_GLetBinds (Syn_GLetBinds _ _ x _ _ _ _ _ _ _ _) = x
graph_Syn_GLetBinds :: Syn_GLetBinds -> (GinGraph)
graph_Syn_GLetBinds (Syn_GLetBinds _ x _ _ _ _ _ _ _ _ _) = x
copy_Syn_GLetBinds :: Syn_GLetBinds -> (GLetBinds)
copy_Syn_GLetBinds (Syn_GLetBinds x _ _ _ _ _ _ _ _ _ _) = x
wrap_GLetBinds :: T_GLetBinds  Inh_GLetBinds  -> (Syn_GLetBinds )
wrap_GLetBinds (T_GLetBinds act) (Inh_GLetBinds alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GLetBinds_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLetBinds_s38 sem arg) >>= \ (T_GLetBinds_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLetBinds alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLetBinds :: GLetBinds  -> T_GLetBinds 
sem_GLetBinds list = foldr sem_GLetBinds_Cons sem_GLetBinds_Nil (map sem_GLetBind list)

// semantic domain
attach_T_GLetBinds (T_GLetBinds t_GLetBinds) = t_GLetBinds
inv_GLetBinds_s38 (C_GLetBinds_s38 x) = x
sem_GLetBinds_Cons  :: (T_GLetBind ) (T_GLetBinds ) -> T_GLetBinds 
sem_GLetBinds_Cons arg_hd_ arg_tl_ = T_GLetBinds (lift st38) where
   st38 =
         let
             v37 (T_GLetBinds_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX35 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBind (arg_hd_))
                           st_tlX38 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_tl_))
                           (T_GLetBind_vOut34 ahdIcopy ahdIgraph ahdIhasRecs ahdImCaseVarExpr ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_GLetBind_s35 st_hdX35 (T_GLetBind_vIn34 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_GLetBinds_vOut37 atlIcopy atlIgraph atlIhasRecs atlImCaseVarExpr atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_GLetBinds_s38 st_tlX38 (T_GLetBinds_vIn37 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOmCaseVarExpr = rule750 ahdImCaseVarExpr atlImCaseVarExpr
                           alhsOhasRecs = rule751 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule752 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule753 ahdImExitId atlImExitId
                           alhsOppAg = rule754 ahdIppAg atlIppAg
                           alhsOppAgs = rule755 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule756 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule757 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule758 ahdIrecNode atlIrecNode
                           lcopy = rule759 ahdIcopy atlIcopy
                           alhsOcopy = rule760 lcopy
                           alhsOgraph = rule761 atlIgraph
                           ahdOcaseExpr = rule762 alhsIcaseExpr
                           ahdOcurrTaskName = rule763 alhsIcurrTaskName
                           ahdOgraph = rule764 alhsIgraph
                           ahdOmergeId = rule765 alhsImergeId
                           ahdOmoduleEnv = rule766 alhsImoduleEnv
                           atlOcaseExpr = rule767 alhsIcaseExpr
                           atlOcurrTaskName = rule768 alhsIcurrTaskName
                           atlOgraph = rule769 ahdIgraph
                           atlOmergeId = rule770 alhsImergeId
                           atlOmoduleEnv = rule771 alhsImoduleEnv
                           ag__result_ = T_GLetBinds_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBinds_s38 v37
   /*# LINE 259 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule750 ((ahdImCaseVarExpr)) ((atlImCaseVarExpr)) =
                               /*# LINE 259 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                               ahdImCaseVarExpr <> atlImCaseVarExpr
                               /*# LINE 4091 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule751 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule752 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule753 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule754 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule755 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule756 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule757 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule758 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule759 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule760 lcopy =
     lcopy
   rule761 ((atlIgraph)) =
     atlIgraph
   rule762 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule763 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule764 ((alhsIgraph)) =
     alhsIgraph
   rule765 ((alhsImergeId)) =
     alhsImergeId
   rule766 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule767 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule768 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule769 ((ahdIgraph)) =
     ahdIgraph
   rule770 ((alhsImergeId)) =
     alhsImergeId
   rule771 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_GLetBinds_Nil  ::   T_GLetBinds 
sem_GLetBinds_Nil  = T_GLetBinds (lift st38) where
   st38 =
         let
             v37 (T_GLetBinds_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOmCaseVarExpr = rule772  Void
                           alhsOhasRecs = rule773  Void
                           alhsOmEntryId = rule774  Void
                           alhsOmExitId = rule775  Void
                           alhsOppAg = rule776  Void
                           alhsOppAgs = rule777  Void
                           alhsOppDebug = rule778  Void
                           alhsOppDebugs = rule779  Void
                           alhsOrecNode = rule780  Void
                           lcopy = rule781  Void
                           alhsOcopy = rule782 lcopy
                           alhsOgraph = rule783 alhsIgraph
                           ag__result_ = T_GLetBinds_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBinds_s38 v37
   /*# LINE 260 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule772  (_) =
                               /*# LINE 260 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                               Nothing
                               /*# LINE 4159 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule773  (_) =
     False
   rule774  (_) =
     Nothing
   rule775  (_) =
     Nothing
   rule776  (_) =
     empty
   rule777  (_) =
     []
   rule778  (_) =
     empty
   rule779  (_) =
     []
   rule780  (_) =
     False
   rule781  (_) =
     []
   rule782 lcopy =
     lcopy
   rule783 ((alhsIgraph)) =
     alhsIgraph

// GlobalDefinedSymbol -----------------------------------------
// wrapper
moduleEnv_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (ModuleEnv)
moduleEnv_Inh_GlobalDefinedSymbol (Inh_GlobalDefinedSymbol _ _ _ _ x) = x
mergeId_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (Int)
mergeId_Inh_GlobalDefinedSymbol (Inh_GlobalDefinedSymbol _ _ _ x _) = x
graph_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (GinGraph)
graph_Inh_GlobalDefinedSymbol (Inh_GlobalDefinedSymbol _ _ x _ _) = x
currTaskName_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (String)
currTaskName_Inh_GlobalDefinedSymbol (Inh_GlobalDefinedSymbol _ x _ _ _) = x
caseExpr_Inh_GlobalDefinedSymbol :: Inh_GlobalDefinedSymbol -> (Maybe Expression)
caseExpr_Inh_GlobalDefinedSymbol (Inh_GlobalDefinedSymbol x _ _ _ _) = x
recNode_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Bool)
recNode_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> ([Doc])
ppDebugs_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Doc)
ppDebug_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> ([Doc])
ppAgs_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Doc)
ppAg_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Maybe Int)
mExitId_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Maybe Int)
mEntryId_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (Bool)
hasRecs_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ _ x _ _ _ _ _ _ _) = x
graph_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (GinGraph)
graph_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol _ x _ _ _ _ _ _ _ _) = x
copy_Syn_GlobalDefinedSymbol :: Syn_GlobalDefinedSymbol -> (GlobalDefinedSymbol)
copy_Syn_GlobalDefinedSymbol (Syn_GlobalDefinedSymbol x _ _ _ _ _ _ _ _ _) = x
wrap_GlobalDefinedSymbol :: T_GlobalDefinedSymbol  Inh_GlobalDefinedSymbol  -> (Syn_GlobalDefinedSymbol )
wrap_GlobalDefinedSymbol (T_GlobalDefinedSymbol act) (Inh_GlobalDefinedSymbol alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GlobalDefinedSymbol_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GlobalDefinedSymbol_s41 sem arg) >>= \ (T_GlobalDefinedSymbol_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GlobalDefinedSymbol alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GlobalDefinedSymbol :: GlobalDefinedSymbol  -> T_GlobalDefinedSymbol 
sem_GlobalDefinedSymbol (x1) = sem_GlobalDefinedSymbol_Tuple x1

// semantic domain
attach_T_GlobalDefinedSymbol (T_GlobalDefinedSymbol t_GlobalDefinedSymbol) = t_GlobalDefinedSymbol
inv_GlobalDefinedSymbol_s41 (C_GlobalDefinedSymbol_s41 x) = x
sem_GlobalDefinedSymbol_Tuple  :: (Global DefinedSymbol) -> T_GlobalDefinedSymbol 
sem_GlobalDefinedSymbol_Tuple arg_x1_ = T_GlobalDefinedSymbol (lift st41) where
   st41 =
         let
             v40 (T_GlobalDefinedSymbol_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule784  Void
                           alhsOmEntryId = rule785  Void
                           alhsOmExitId = rule786  Void
                           alhsOppAg = rule787  Void
                           alhsOppAgs = rule788  Void
                           alhsOppDebug = rule789  Void
                           alhsOppDebugs = rule790  Void
                           alhsOrecNode = rule791  Void
                           lcopy = rule792 arg_x1_
                           alhsOcopy = rule793 lcopy
                           alhsOgraph = rule794 alhsIgraph
                           ag__result_ = T_GlobalDefinedSymbol_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GlobalDefinedSymbol_s41 v40
   rule784  (_) =
     False
   rule785  (_) =
     Nothing
   rule786  (_) =
     Nothing
   rule787  (_) =
     empty
   rule788  (_) =
     []
   rule789  (_) =
     empty
   rule790  (_) =
     []
   rule791  (_) =
     False
   rule792 x1_ =
     (x1_)
   rule793 lcopy =
     lcopy
   rule794 ((alhsIgraph)) =
     alhsIgraph

// Ident -------------------------------------------------------
// wrapper
moduleEnv_Inh_Ident :: Inh_Ident -> (ModuleEnv)
moduleEnv_Inh_Ident (Inh_Ident _ _ _ _ x) = x
mergeId_Inh_Ident :: Inh_Ident -> (Int)
mergeId_Inh_Ident (Inh_Ident _ _ _ x _) = x
graph_Inh_Ident :: Inh_Ident -> (GinGraph)
graph_Inh_Ident (Inh_Ident _ _ x _ _) = x
currTaskName_Inh_Ident :: Inh_Ident -> (String)
currTaskName_Inh_Ident (Inh_Ident _ x _ _ _) = x
caseExpr_Inh_Ident :: Inh_Ident -> (Maybe Expression)
caseExpr_Inh_Ident (Inh_Ident x _ _ _ _) = x
reifySymbolType_Syn_Ident :: Syn_Ident -> (Maybe SymbolType)
reifySymbolType_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
reifyFunType_Syn_Ident :: Syn_Ident -> (Maybe FunType)
reifyFunType_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
reifyFunDef_Syn_Ident :: Syn_Ident -> (Maybe GFunDef)
reifyFunDef_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
recNode_Syn_Ident :: Syn_Ident -> (Bool)
recNode_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
ppDebugs_Syn_Ident :: Syn_Ident -> ([Doc])
ppDebugs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
ppDebug_Syn_Ident :: Syn_Ident -> (Doc)
ppDebug_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
ppAgs_Syn_Ident :: Syn_Ident -> ([Doc])
ppAgs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
ppAg_Syn_Ident :: Syn_Ident -> (Doc)
ppAg_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
mExitId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mExitId_Syn_Ident (Syn_Ident _ _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
mEntryId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mEntryId_Syn_Ident (Syn_Ident _ _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
isTask_Syn_Ident :: Syn_Ident -> (Bool)
isTask_Syn_Ident (Syn_Ident _ _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
ident_Syn_Ident :: Syn_Ident -> (String)
ident_Syn_Ident (Syn_Ident _ _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_Ident :: Syn_Ident -> (Bool)
hasRecs_Syn_Ident (Syn_Ident _ _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_Ident :: Syn_Ident -> (GinGraph)
graph_Syn_Ident (Syn_Ident _ x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_Ident :: Syn_Ident -> (Ident)
copy_Syn_Ident (Syn_Ident x _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_Ident :: T_Ident  Inh_Ident  -> (Syn_Ident )
wrap_Ident (T_Ident act) (Inh_Ident alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Ident_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Ident_s44 sem arg) >>= \ (T_Ident_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType) ->
     lift (Syn_Ident alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType)
   )

// cata
sem_Ident :: Ident  -> T_Ident 
sem_Ident { Ident | id_name = id_name_,id_info = id_info_ } = sem_Ident_Ident id_name_ id_info_ 

// semantic domain
attach_T_Ident (T_Ident t_Ident) = t_Ident
inv_Ident_s44 (C_Ident_s44 x) = x
sem_Ident_Ident  :: (String) (SymbolPtr)  -> T_Ident 
sem_Ident_Ident arg_id_name_ arg_id_info_  = T_Ident (lift st44) where
   st44 =
         let
             v43 (T_Ident_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_identSymbolTypeX56 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbolType ((sem_SymbolType identSymbolType_val_)))
                           (T_SymbolType_vOut55 aidentSymbolTypeIcopy aidentSymbolTypeIgraph aidentSymbolTypeIhasRecs aidentSymbolTypeIisTask aidentSymbolTypeImEntryId aidentSymbolTypeImExitId aidentSymbolTypeIppAg aidentSymbolTypeIppAgs aidentSymbolTypeIppDebug aidentSymbolTypeIppDebugs aidentSymbolTypeIrecNode) = inv_SymbolType_s56 st_identSymbolTypeX56 (T_SymbolType_vIn55 aidentSymbolTypeOcaseExpr aidentSymbolTypeOcurrTaskName aidentSymbolTypeOgraph aidentSymbolTypeOmergeId aidentSymbolTypeOmoduleEnv)
                           alhsOident = rule795 arg_id_name_
                           alhsOisTask = rule796 aidentSymbolTypeIisTask
                           identSymbolType_val_ = rule797 arg_id_name_ lreifySymbolType
                           alhsOreifyFunType = rule798 alhsImoduleEnv lcopy
                           alhsOreifySymbolType = rule799 lreifySymbolType
                           lreifySymbolType = rule800 alhsImoduleEnv lcopy
                           alhsOreifyFunDef = rule801 alhsImoduleEnv lcopy
                           alhsOppDebug = rule802 arg_id_name_
                           alhsOppAg = rule803 arg_id_name_
                           alhsOhasRecs = rule804 aidentSymbolTypeIhasRecs
                           alhsOmEntryId = rule805 aidentSymbolTypeImEntryId
                           alhsOmExitId = rule806 aidentSymbolTypeImExitId
                           alhsOppAgs = rule807 aidentSymbolTypeIppAgs
                           alhsOppDebugs = rule808 aidentSymbolTypeIppDebugs
                           alhsOrecNode = rule809 aidentSymbolTypeIrecNode
                           lcopy = rule810 arg_id_info_ arg_id_name_
                           alhsOcopy = rule811 lcopy
                           alhsOgraph = rule812 aidentSymbolTypeIgraph
                           aidentSymbolTypeOcaseExpr = rule813 alhsIcaseExpr
                           aidentSymbolTypeOcurrTaskName = rule814 alhsIcurrTaskName
                           aidentSymbolTypeOgraph = rule815 alhsIgraph
                           aidentSymbolTypeOmergeId = rule816 alhsImergeId
                           aidentSymbolTypeOmoduleEnv = rule817 alhsImoduleEnv
                           ag__result_ = T_Ident_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType
                       in ag__result_
         in C_Ident_s44 v43
   /*# LINE 64 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule795 id_name_ =
                     /*# LINE 64 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                     id_name_
                     /*# LINE 4370 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 65 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule796 ((aidentSymbolTypeIisTask)) =
                     /*# LINE 65 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                     aidentSymbolTypeIisTask
                     /*# LINE 4375 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 68 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule797 id_name_ lreifySymbolType =
                               /*# LINE 68 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                               fromMaybe (abort $ "inst.identSymbolType: " +++ id_name_)
                               lreifySymbolType
                               /*# LINE 4381 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 71 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule798 ((alhsImoduleEnv)) lcopy =
                              /*# LINE 71 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              reifyFunType alhsImoduleEnv lcopy
                              /*# LINE 4386 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 72 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule799 lreifySymbolType =
                              /*# LINE 72 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              lreifySymbolType
                              /*# LINE 4391 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 73 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule800 ((alhsImoduleEnv)) lcopy =
                              /*# LINE 73 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              reifySymbolType alhsImoduleEnv lcopy
                              /*# LINE 4396 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 74 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule801 ((alhsImoduleEnv)) lcopy =
                              /*# LINE 74 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              reifyFunDef alhsImoduleEnv lcopy
                              /*# LINE 4401 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 104 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule802 id_name_ =
                          /*# LINE 104 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4406 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 105 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule803 id_name_ =
                          /*# LINE 105 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4411 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule804 ((aidentSymbolTypeIhasRecs)) =
     aidentSymbolTypeIhasRecs
   rule805 ((aidentSymbolTypeImEntryId)) =
     aidentSymbolTypeImEntryId
   rule806 ((aidentSymbolTypeImExitId)) =
     aidentSymbolTypeImExitId
   rule807 ((aidentSymbolTypeIppAgs)) =
     aidentSymbolTypeIppAgs
   rule808 ((aidentSymbolTypeIppDebugs)) =
     aidentSymbolTypeIppDebugs
   rule809 ((aidentSymbolTypeIrecNode)) =
     aidentSymbolTypeIrecNode
   rule810 id_info_ id_name_ =
     {Ident|id_name = id_name_ , id_info = id_info_}
   rule811 lcopy =
     lcopy
   rule812 ((aidentSymbolTypeIgraph)) =
     aidentSymbolTypeIgraph
   rule813 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule814 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule815 ((alhsIgraph)) =
     alhsIgraph
   rule816 ((alhsImergeId)) =
     alhsImergeId
   rule817 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// Selection ---------------------------------------------------
// wrapper
moduleEnv_Inh_Selection :: Inh_Selection -> (ModuleEnv)
moduleEnv_Inh_Selection (Inh_Selection _ _ _ _ x) = x
mergeId_Inh_Selection :: Inh_Selection -> (Int)
mergeId_Inh_Selection (Inh_Selection _ _ _ x _) = x
graph_Inh_Selection :: Inh_Selection -> (GinGraph)
graph_Inh_Selection (Inh_Selection _ _ x _ _) = x
currTaskName_Inh_Selection :: Inh_Selection -> (String)
currTaskName_Inh_Selection (Inh_Selection _ x _ _ _) = x
caseExpr_Inh_Selection :: Inh_Selection -> (Maybe Expression)
caseExpr_Inh_Selection (Inh_Selection x _ _ _ _) = x
recNode_Syn_Selection :: Syn_Selection -> (Bool)
recNode_Syn_Selection (Syn_Selection _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Selection :: Syn_Selection -> ([Doc])
ppDebugs_Syn_Selection (Syn_Selection _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Selection :: Syn_Selection -> (Doc)
ppDebug_Syn_Selection (Syn_Selection _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Selection :: Syn_Selection -> ([Doc])
ppAgs_Syn_Selection (Syn_Selection _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Selection :: Syn_Selection -> (Doc)
ppAg_Syn_Selection (Syn_Selection _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Selection :: Syn_Selection -> (Maybe Int)
mExitId_Syn_Selection (Syn_Selection _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Selection :: Syn_Selection -> (Maybe Int)
mEntryId_Syn_Selection (Syn_Selection _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_Selection :: Syn_Selection -> (Bool)
hasRecs_Syn_Selection (Syn_Selection _ _ x _ _ _ _ _ _ _) = x
graph_Syn_Selection :: Syn_Selection -> (GinGraph)
graph_Syn_Selection (Syn_Selection _ x _ _ _ _ _ _ _ _) = x
copy_Syn_Selection :: Syn_Selection -> (Selection)
copy_Syn_Selection (Syn_Selection x _ _ _ _ _ _ _ _ _) = x
wrap_Selection :: T_Selection  Inh_Selection  -> (Syn_Selection )
wrap_Selection (T_Selection act) (Inh_Selection alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Selection_s47 sem arg) >>= \ (T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Selection alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Selection :: Selection  -> T_Selection 
sem_Selection ( RecordSelection gds_ n_ ) = sem_Selection_RecordSelection ( sem_GlobalDefinedSymbol gds_ ) n_
sem_Selection ( ArraySelection gds_ eiptr_ expr_ ) = sem_Selection_ArraySelection ( sem_GlobalDefinedSymbol gds_ ) eiptr_ ( sem_Expression expr_ )
sem_Selection ( DictionarySelection bv_ sels_ eiptr_ expr_ ) = sem_Selection_DictionarySelection ( sem_BoundVar bv_ ) ( sem_Selections sels_ ) eiptr_ ( sem_Expression expr_ )

// semantic domain
attach_T_Selection (T_Selection t_Selection) = t_Selection
inv_Selection_s47 (C_Selection_s47 x) = x
sem_Selection_RecordSelection  :: (T_GlobalDefinedSymbol ) (Int) -> T_Selection 
sem_Selection_RecordSelection arg_gds_ arg_n_ = T_Selection (lift st47) where
   st47 =
         let
             v46 (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           (T_GlobalDefinedSymbol_vOut40 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsX41 (T_GlobalDefinedSymbol_vIn40 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           alhsOppDebug = rule818 agdsIppDebug
                           alhsOppAg = rule819 agdsIppAg
                           alhsOhasRecs = rule820 agdsIhasRecs
                           alhsOmEntryId = rule821 agdsImEntryId
                           alhsOmExitId = rule822 agdsImExitId
                           alhsOppAgs = rule823 agdsIppAgs
                           alhsOppDebugs = rule824 agdsIppDebugs
                           alhsOrecNode = rule825 agdsIrecNode
                           lcopy = rule826 agdsIcopy arg_n_
                           alhsOcopy = rule827 lcopy
                           alhsOgraph = rule828 agdsIgraph
                           agdsOcaseExpr = rule829 alhsIcaseExpr
                           agdsOcurrTaskName = rule830 alhsIcurrTaskName
                           agdsOgraph = rule831 alhsIgraph
                           agdsOmergeId = rule832 alhsImergeId
                           agdsOmoduleEnv = rule833 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s47 v46
   /*# LINE 138 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule818 ((agdsIppDebug)) =
                                        /*# LINE 138 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        agdsIppDebug
                                        /*# LINE 4522 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 139 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule819 ((agdsIppAg)) =
                                        /*# LINE 139 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        agdsIppAg
                                        /*# LINE 4527 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule820 ((agdsIhasRecs)) =
     agdsIhasRecs
   rule821 ((agdsImEntryId)) =
     agdsImEntryId
   rule822 ((agdsImExitId)) =
     agdsImExitId
   rule823 ((agdsIppAgs)) =
     agdsIppAgs
   rule824 ((agdsIppDebugs)) =
     agdsIppDebugs
   rule825 ((agdsIrecNode)) =
     agdsIrecNode
   rule826 ((agdsIcopy)) n_ =
     RecordSelection agdsIcopy n_
   rule827 lcopy =
     lcopy
   rule828 ((agdsIgraph)) =
     agdsIgraph
   rule829 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule830 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule831 ((alhsIgraph)) =
     alhsIgraph
   rule832 ((alhsImergeId)) =
     alhsImergeId
   rule833 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selection_ArraySelection  :: (T_GlobalDefinedSymbol ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_ArraySelection arg_gds_ arg_eiptr_ arg_expr_ = T_Selection (lift st47) where
   st47 =
         let
             v46 (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut40 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsX41 (T_GlobalDefinedSymbol_vIn40 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule834  Void
                           alhsOppAg = rule835  Void
                           alhsOhasRecs = rule836 aexprIhasRecs agdsIhasRecs
                           alhsOmEntryId = rule837 aexprImEntryId agdsImEntryId
                           alhsOmExitId = rule838 aexprImExitId agdsImExitId
                           alhsOppAgs = rule839 aexprIppAgs agdsIppAgs
                           alhsOppDebugs = rule840 aexprIppDebugs agdsIppDebugs
                           alhsOrecNode = rule841 aexprIrecNode agdsIrecNode
                           lcopy = rule842 aexprIcopy agdsIcopy arg_eiptr_
                           alhsOcopy = rule843 lcopy
                           alhsOgraph = rule844 aexprIgraph
                           agdsOcaseExpr = rule845 alhsIcaseExpr
                           agdsOcurrTaskName = rule846 alhsIcurrTaskName
                           agdsOgraph = rule847 alhsIgraph
                           agdsOmergeId = rule848 alhsImergeId
                           agdsOmoduleEnv = rule849 alhsImoduleEnv
                           aexprOcaseExpr = rule850 alhsIcaseExpr
                           aexprOcurrTaskName = rule851 alhsIcurrTaskName
                           aexprOgraph = rule852 agdsIgraph
                           aexprOmergeId = rule853 alhsImergeId
                           aexprOmoduleEnv = rule854 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s47 v46
   /*# LINE 140 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule834  (_) =
                                        /*# LINE 140 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 4594 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 141 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule835  (_) =
                                        /*# LINE 141 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 4599 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule836 ((aexprIhasRecs)) ((agdsIhasRecs)) =
     agdsIhasRecs || aexprIhasRecs
   rule837 ((aexprImEntryId)) ((agdsImEntryId)) =
     agdsImEntryId <> aexprImEntryId
   rule838 ((aexprImExitId)) ((agdsImExitId)) =
     agdsImExitId <> aexprImExitId
   rule839 ((aexprIppAgs)) ((agdsIppAgs)) =
     agdsIppAgs ++ aexprIppAgs
   rule840 ((aexprIppDebugs)) ((agdsIppDebugs)) =
     agdsIppDebugs ++ aexprIppDebugs
   rule841 ((aexprIrecNode)) ((agdsIrecNode)) =
     agdsIrecNode || aexprIrecNode
   rule842 ((aexprIcopy)) ((agdsIcopy)) eiptr_ =
     ArraySelection agdsIcopy eiptr_ aexprIcopy
   rule843 lcopy =
     lcopy
   rule844 ((aexprIgraph)) =
     aexprIgraph
   rule845 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule846 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule847 ((alhsIgraph)) =
     alhsIgraph
   rule848 ((alhsImergeId)) =
     alhsImergeId
   rule849 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule850 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule851 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule852 ((agdsIgraph)) =
     agdsIgraph
   rule853 ((alhsImergeId)) =
     alhsImergeId
   rule854 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selection_DictionarySelection  :: (T_BoundVar ) (T_Selections ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_DictionarySelection arg_bv_ arg_sels_ arg_eiptr_ arg_expr_ = T_Selection (lift st47) where
   st47 =
         let
             v46 (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_bvX8 = 'Control.Monad.Identity'.runIdentity (attach_T_BoundVar (arg_bv_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_BoundVar_vOut7 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BoundVar_s8 st_bvX8 (T_BoundVar_vIn7 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule855  Void
                           alhsOppAg = rule856  Void
                           alhsOhasRecs = rule857 abvIhasRecs aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule858 abvImEntryId aexprImEntryId aselsImEntryId
                           alhsOmExitId = rule859 abvImExitId aexprImExitId aselsImExitId
                           alhsOppAgs = rule860 abvIppAgs aexprIppAgs aselsIppAgs
                           alhsOppDebugs = rule861 abvIppDebugs aexprIppDebugs aselsIppDebugs
                           alhsOrecNode = rule862 abvIrecNode aexprIrecNode aselsIrecNode
                           lcopy = rule863 abvIcopy aexprIcopy aselsIcopy arg_eiptr_
                           alhsOcopy = rule864 lcopy
                           alhsOgraph = rule865 aexprIgraph
                           abvOcaseExpr = rule866 alhsIcaseExpr
                           abvOcurrTaskName = rule867 alhsIcurrTaskName
                           abvOgraph = rule868 alhsIgraph
                           abvOmergeId = rule869 alhsImergeId
                           abvOmoduleEnv = rule870 alhsImoduleEnv
                           aselsOcaseExpr = rule871 alhsIcaseExpr
                           aselsOcurrTaskName = rule872 alhsIcurrTaskName
                           aselsOgraph = rule873 abvIgraph
                           aselsOmergeId = rule874 alhsImergeId
                           aselsOmoduleEnv = rule875 alhsImoduleEnv
                           aexprOcaseExpr = rule876 alhsIcaseExpr
                           aexprOcurrTaskName = rule877 alhsIcurrTaskName
                           aexprOgraph = rule878 aselsIgraph
                           aexprOmergeId = rule879 alhsImergeId
                           aexprOmoduleEnv = rule880 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s47 v46
   /*# LINE 142 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule855  (_) =
                                        /*# LINE 142 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 4683 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 143 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule856  (_) =
                                        /*# LINE 143 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 4688 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule857 ((abvIhasRecs)) ((aexprIhasRecs)) ((aselsIhasRecs)) =
     abvIhasRecs || aselsIhasRecs || aexprIhasRecs
   rule858 ((abvImEntryId)) ((aexprImEntryId)) ((aselsImEntryId)) =
     abvImEntryId <> aselsImEntryId <> aexprImEntryId
   rule859 ((abvImExitId)) ((aexprImExitId)) ((aselsImExitId)) =
     abvImExitId <> aselsImExitId <> aexprImExitId
   rule860 ((abvIppAgs)) ((aexprIppAgs)) ((aselsIppAgs)) =
     abvIppAgs ++ aselsIppAgs ++ aexprIppAgs
   rule861 ((abvIppDebugs)) ((aexprIppDebugs)) ((aselsIppDebugs)) =
     abvIppDebugs ++ aselsIppDebugs ++ aexprIppDebugs
   rule862 ((abvIrecNode)) ((aexprIrecNode)) ((aselsIrecNode)) =
     abvIrecNode || aselsIrecNode || aexprIrecNode
   rule863 ((abvIcopy)) ((aexprIcopy)) ((aselsIcopy)) eiptr_ =
     DictionarySelection abvIcopy aselsIcopy eiptr_ aexprIcopy
   rule864 lcopy =
     lcopy
   rule865 ((aexprIgraph)) =
     aexprIgraph
   rule866 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule867 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule868 ((alhsIgraph)) =
     alhsIgraph
   rule869 ((alhsImergeId)) =
     alhsImergeId
   rule870 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule871 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule872 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule873 ((abvIgraph)) =
     abvIgraph
   rule874 ((alhsImergeId)) =
     alhsImergeId
   rule875 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule876 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule877 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule878 ((aselsIgraph)) =
     aselsIgraph
   rule879 ((alhsImergeId)) =
     alhsImergeId
   rule880 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// Selections --------------------------------------------------
// wrapper
moduleEnv_Inh_Selections :: Inh_Selections -> (ModuleEnv)
moduleEnv_Inh_Selections (Inh_Selections _ _ _ _ x) = x
mergeId_Inh_Selections :: Inh_Selections -> (Int)
mergeId_Inh_Selections (Inh_Selections _ _ _ x _) = x
graph_Inh_Selections :: Inh_Selections -> (GinGraph)
graph_Inh_Selections (Inh_Selections _ _ x _ _) = x
currTaskName_Inh_Selections :: Inh_Selections -> (String)
currTaskName_Inh_Selections (Inh_Selections _ x _ _ _) = x
caseExpr_Inh_Selections :: Inh_Selections -> (Maybe Expression)
caseExpr_Inh_Selections (Inh_Selections x _ _ _ _) = x
recNode_Syn_Selections :: Syn_Selections -> (Bool)
recNode_Syn_Selections (Syn_Selections _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Selections :: Syn_Selections -> ([Doc])
ppDebugs_Syn_Selections (Syn_Selections _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Selections :: Syn_Selections -> (Doc)
ppDebug_Syn_Selections (Syn_Selections _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Selections :: Syn_Selections -> ([Doc])
ppAgs_Syn_Selections (Syn_Selections _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Selections :: Syn_Selections -> (Doc)
ppAg_Syn_Selections (Syn_Selections _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Selections :: Syn_Selections -> (Maybe Int)
mExitId_Syn_Selections (Syn_Selections _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Selections :: Syn_Selections -> (Maybe Int)
mEntryId_Syn_Selections (Syn_Selections _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_Selections :: Syn_Selections -> (Bool)
hasRecs_Syn_Selections (Syn_Selections _ _ x _ _ _ _ _ _ _) = x
graph_Syn_Selections :: Syn_Selections -> (GinGraph)
graph_Syn_Selections (Syn_Selections _ x _ _ _ _ _ _ _ _) = x
copy_Syn_Selections :: Syn_Selections -> (Selections)
copy_Syn_Selections (Syn_Selections x _ _ _ _ _ _ _ _ _) = x
wrap_Selections :: T_Selections  Inh_Selections  -> (Syn_Selections )
wrap_Selections (T_Selections act) (Inh_Selections alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Selections_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Selections_s50 sem arg) >>= \ (T_Selections_vOut49 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Selections alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Selections :: Selections  -> T_Selections 
sem_Selections list = foldr sem_Selections_Cons sem_Selections_Nil (map sem_Selection list)

// semantic domain
attach_T_Selections (T_Selections t_Selections) = t_Selections
inv_Selections_s50 (C_Selections_s50 x) = x
sem_Selections_Cons  :: (T_Selection ) (T_Selections ) -> T_Selections 
sem_Selections_Cons arg_hd_ arg_tl_ = T_Selections (lift st50) where
   st50 =
         let
             v49 (T_Selections_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Selection (arg_hd_))
                           st_tlX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_tl_))
                           (T_Selection_vOut46 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Selection_s47 st_hdX47 (T_Selection_vIn46 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Selections_vOut49 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_Selections_s50 st_tlX50 (T_Selections_vIn49 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs = rule881 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule882 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule883 ahdImExitId atlImExitId
                           alhsOppAg = rule884 ahdIppAg atlIppAg
                           alhsOppAgs = rule885 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule886 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule887 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule888 ahdIrecNode atlIrecNode
                           lcopy = rule889 ahdIcopy atlIcopy
                           alhsOcopy = rule890 lcopy
                           alhsOgraph = rule891 atlIgraph
                           ahdOcaseExpr = rule892 alhsIcaseExpr
                           ahdOcurrTaskName = rule893 alhsIcurrTaskName
                           ahdOgraph = rule894 alhsIgraph
                           ahdOmergeId = rule895 alhsImergeId
                           ahdOmoduleEnv = rule896 alhsImoduleEnv
                           atlOcaseExpr = rule897 alhsIcaseExpr
                           atlOcurrTaskName = rule898 alhsIcurrTaskName
                           atlOgraph = rule899 ahdIgraph
                           atlOmergeId = rule900 alhsImergeId
                           atlOmoduleEnv = rule901 alhsImoduleEnv
                           ag__result_ = T_Selections_vOut49 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selections_s50 v49
   rule881 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule882 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule883 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule884 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule885 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule886 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule887 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule888 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule889 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule890 lcopy =
     lcopy
   rule891 ((atlIgraph)) =
     atlIgraph
   rule892 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule893 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule894 ((alhsIgraph)) =
     alhsIgraph
   rule895 ((alhsImergeId)) =
     alhsImergeId
   rule896 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule897 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule898 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule899 ((ahdIgraph)) =
     ahdIgraph
   rule900 ((alhsImergeId)) =
     alhsImergeId
   rule901 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selections_Nil  ::   T_Selections 
sem_Selections_Nil  = T_Selections (lift st50) where
   st50 =
         let
             v49 (T_Selections_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule902  Void
                           alhsOmEntryId = rule903  Void
                           alhsOmExitId = rule904  Void
                           alhsOppAg = rule905  Void
                           alhsOppAgs = rule906  Void
                           alhsOppDebug = rule907  Void
                           alhsOppDebugs = rule908  Void
                           alhsOrecNode = rule909  Void
                           lcopy = rule910  Void
                           alhsOcopy = rule911 lcopy
                           alhsOgraph = rule912 alhsIgraph
                           ag__result_ = T_Selections_vOut49 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selections_s50 v49
   rule902  (_) =
     False
   rule903  (_) =
     Nothing
   rule904  (_) =
     Nothing
   rule905  (_) =
     empty
   rule906  (_) =
     []
   rule907  (_) =
     empty
   rule908  (_) =
     []
   rule909  (_) =
     False
   rule910  (_) =
     []
   rule911 lcopy =
     lcopy
   rule912 ((alhsIgraph)) =
     alhsIgraph

// SymbIdent ---------------------------------------------------
// wrapper
moduleEnv_Inh_SymbIdent :: Inh_SymbIdent -> (ModuleEnv)
moduleEnv_Inh_SymbIdent (Inh_SymbIdent _ _ _ _ x) = x
mergeId_Inh_SymbIdent :: Inh_SymbIdent -> (Int)
mergeId_Inh_SymbIdent (Inh_SymbIdent _ _ _ x _) = x
graph_Inh_SymbIdent :: Inh_SymbIdent -> (GinGraph)
graph_Inh_SymbIdent (Inh_SymbIdent _ _ x _ _) = x
currTaskName_Inh_SymbIdent :: Inh_SymbIdent -> (String)
currTaskName_Inh_SymbIdent (Inh_SymbIdent _ x _ _ _) = x
caseExpr_Inh_SymbIdent :: Inh_SymbIdent -> (Maybe Expression)
caseExpr_Inh_SymbIdent (Inh_SymbIdent x _ _ _ _) = x
reifySymbolType_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe SymbolType)
reifySymbolType_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
reifyFunType_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe FunType)
reifyFunType_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
reifyFunDef_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe GFunDef)
reifyFunDef_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
recNode_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
recNode_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
ppDebugs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppDebugs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
ppDebug_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppDebug_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
ppAgs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppAgs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
ppAg_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppAg_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
mExitId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mExitId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
mEntryId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mEntryId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
isTask_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isTask_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
isInfix_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isInfix_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
isCurrTask_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isCurrTask_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
ident_Syn_SymbIdent :: Syn_SymbIdent -> (String)
ident_Syn_SymbIdent (Syn_SymbIdent _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
hasRecs_Syn_SymbIdent (Syn_SymbIdent _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_SymbIdent :: Syn_SymbIdent -> (GinGraph)
graph_Syn_SymbIdent (Syn_SymbIdent _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_SymbIdent :: Syn_SymbIdent -> (SymbIdent)
copy_Syn_SymbIdent (Syn_SymbIdent x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_SymbIdent :: T_SymbIdent  Inh_SymbIdent  -> (Syn_SymbIdent )
wrap_SymbIdent (T_SymbIdent act) (Inh_SymbIdent alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_SymbIdent_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbIdent_s53 sem arg) >>= \ (T_SymbIdent_vOut52 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType) ->
     lift (Syn_SymbIdent alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType)
   )

// cata
sem_SymbIdent :: SymbIdent  -> T_SymbIdent 
sem_SymbIdent { SymbIdent | symb_ident = symb_ident_,symb_kind = symb_kind_ } = sem_SymbIdent_SymbIdent ( sem_Ident symb_ident_ ) symb_kind_

// semantic domain
attach_T_SymbIdent (T_SymbIdent t_SymbIdent) = t_SymbIdent
inv_SymbIdent_s53 (C_SymbIdent_s53 x) = x
sem_SymbIdent_SymbIdent  :: (T_Ident ) (SymbKind) -> T_SymbIdent 
sem_SymbIdent_SymbIdent arg_symb_ident_ arg_symb_kind_ = T_SymbIdent (lift st53) where
   st53 =
         let
             v52 (T_SymbIdent_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_symb_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_symb_ident_))
                           (T_Ident_vOut43 asymb_identIcopy asymb_identIgraph asymb_identIhasRecs asymb_identIident asymb_identIisTask asymb_identImEntryId asymb_identImExitId asymb_identIppAg asymb_identIppAgs asymb_identIppDebug asymb_identIppDebugs asymb_identIrecNode asymb_identIreifyFunDef asymb_identIreifyFunType asymb_identIreifySymbolType) = inv_Ident_s44 st_symb_identX44 (T_Ident_vIn43 asymb_identOcaseExpr asymb_identOcurrTaskName asymb_identOgraph asymb_identOmergeId asymb_identOmoduleEnv)
                           alhsOreifyFunDef = rule913 alhsImoduleEnv asymb_identIcopy
                           alhsOreifySymbolType = rule914 asymb_identIreifySymbolType
                           lident = rule915 asymb_identIident
                           alhsOident = rule916 lident
                           alhsOisCurrTask = rule917 alhsIcurrTaskName lident
                           alhsOisTask = rule918 asymb_identIisTask
                           alhsOisInfix = rule919 alhsImoduleEnv asymb_identIcopy asymb_identIppAg
                           alhsOppDebug = rule920 asymb_identIppDebug
                           alhsOppAg = rule921 asymb_identIppAg
                           alhsOhasRecs = rule922 asymb_identIhasRecs
                           alhsOmEntryId = rule923 asymb_identImEntryId
                           alhsOmExitId = rule924 asymb_identImExitId
                           alhsOppAgs = rule925 asymb_identIppAgs
                           alhsOppDebugs = rule926 asymb_identIppDebugs
                           alhsOrecNode = rule927 asymb_identIrecNode
                           lcopy = rule928 asymb_identIcopy arg_symb_kind_
                           alhsOcopy = rule929 lcopy
                           alhsOgraph = rule930 asymb_identIgraph
                           alhsOreifyFunType = rule931 asymb_identIreifyFunType
                           asymb_identOcaseExpr = rule932 alhsIcaseExpr
                           asymb_identOcurrTaskName = rule933 alhsIcurrTaskName
                           asymb_identOgraph = rule934 alhsIgraph
                           asymb_identOmergeId = rule935 alhsImergeId
                           asymb_identOmoduleEnv = rule936 alhsImoduleEnv
                           ag__result_ = T_SymbIdent_vOut52 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOreifyFunDef alhsOreifyFunType alhsOreifySymbolType
                       in ag__result_
         in C_SymbIdent_s53 v52
   /*# LINE 94 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule913 ((alhsImoduleEnv)) ((asymb_identIcopy)) =
                          /*# LINE 94 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          reifyFunDef alhsImoduleEnv asymb_identIcopy
                          /*# LINE 5006 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 95 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule914 ((asymb_identIreifySymbolType)) =
                              /*# LINE 95 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                              asymb_identIreifySymbolType
                              /*# LINE 5011 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 97 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule915 ((asymb_identIident)) =
                          /*# LINE 97 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          asymb_identIident
                          /*# LINE 5016 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 98 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule916 lident =
                          /*# LINE 98 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          lident
                          /*# LINE 5021 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 99 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule917 ((alhsIcurrTaskName)) lident =
                          /*# LINE 99 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          lident     == alhsIcurrTaskName
                          /*# LINE 5026 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 100 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule918 ((asymb_identIisTask)) =
                          /*# LINE 100 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                          asymb_identIisTask
                          /*# LINE 5031 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 34 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule919 ((alhsImoduleEnv)) ((asymb_identIcopy)) ((asymb_identIppAg)) =
                                 /*# LINE 34 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                                 let mfd  = reifyFunDef alhsImoduleEnv asymb_identIcopy
                                     mft  = reifyFunType alhsImoduleEnv asymb_identIcopy
                                     isInfix` (Prio _ _) = True
                                     isInfix` _          = False
                                 in  case mfd of
                                       Just fd  -> isInfix` fd.gfd_priority
                                       Nothing  ->
                                         case mft of
                                           Just ft  -> isInfix` ft.ft_priority
                                           _        -> abort ("Failed to determine fixity for " +++ ppCompact asymb_identIppAg)
                                 /*# LINE 5045 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 116 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule920 ((asymb_identIppDebug)) =
                              /*# LINE 116 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppDebug
                              /*# LINE 5050 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   /*# LINE 117 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
   rule921 ((asymb_identIppAg)) =
                              /*# LINE 117 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppAg
                              /*# LINE 5055 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule922 ((asymb_identIhasRecs)) =
     asymb_identIhasRecs
   rule923 ((asymb_identImEntryId)) =
     asymb_identImEntryId
   rule924 ((asymb_identImExitId)) =
     asymb_identImExitId
   rule925 ((asymb_identIppAgs)) =
     asymb_identIppAgs
   rule926 ((asymb_identIppDebugs)) =
     asymb_identIppDebugs
   rule927 ((asymb_identIrecNode)) =
     asymb_identIrecNode
   rule928 ((asymb_identIcopy)) symb_kind_ =
     {SymbIdent|symb_ident = asymb_identIcopy , symb_kind = symb_kind_}
   rule929 lcopy =
     lcopy
   rule930 ((asymb_identIgraph)) =
     asymb_identIgraph
   rule931 ((asymb_identIreifyFunType)) =
     asymb_identIreifyFunType
   rule932 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule933 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule934 ((alhsIgraph)) =
     alhsIgraph
   rule935 ((alhsImergeId)) =
     alhsImergeId
   rule936 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// SymbolType --------------------------------------------------
// wrapper
moduleEnv_Inh_SymbolType :: Inh_SymbolType -> (ModuleEnv)
moduleEnv_Inh_SymbolType (Inh_SymbolType _ _ _ _ x) = x
mergeId_Inh_SymbolType :: Inh_SymbolType -> (Int)
mergeId_Inh_SymbolType (Inh_SymbolType _ _ _ x _) = x
graph_Inh_SymbolType :: Inh_SymbolType -> (GinGraph)
graph_Inh_SymbolType (Inh_SymbolType _ _ x _ _) = x
currTaskName_Inh_SymbolType :: Inh_SymbolType -> (String)
currTaskName_Inh_SymbolType (Inh_SymbolType _ x _ _ _) = x
caseExpr_Inh_SymbolType :: Inh_SymbolType -> (Maybe Expression)
caseExpr_Inh_SymbolType (Inh_SymbolType x _ _ _ _) = x
recNode_Syn_SymbolType :: Syn_SymbolType -> (Bool)
recNode_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppDebugs_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_SymbolType :: Syn_SymbolType -> (Doc)
ppDebug_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppAgs_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_SymbolType :: Syn_SymbolType -> (Doc)
ppAg_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
mExitId_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
mEntryId_Syn_SymbolType (Syn_SymbolType _ _ _ _ x _ _ _ _ _ _) = x
isTask_Syn_SymbolType :: Syn_SymbolType -> (Bool)
isTask_Syn_SymbolType (Syn_SymbolType _ _ _ x _ _ _ _ _ _ _) = x
hasRecs_Syn_SymbolType :: Syn_SymbolType -> (Bool)
hasRecs_Syn_SymbolType (Syn_SymbolType _ _ x _ _ _ _ _ _ _ _) = x
graph_Syn_SymbolType :: Syn_SymbolType -> (GinGraph)
graph_Syn_SymbolType (Syn_SymbolType _ x _ _ _ _ _ _ _ _ _) = x
copy_Syn_SymbolType :: Syn_SymbolType -> (SymbolType)
copy_Syn_SymbolType (Syn_SymbolType x _ _ _ _ _ _ _ _ _ _) = x
wrap_SymbolType :: T_SymbolType  Inh_SymbolType  -> (Syn_SymbolType )
wrap_SymbolType (T_SymbolType act) (Inh_SymbolType alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_SymbolType_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbolType_s56 sem arg) >>= \ (T_SymbolType_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_SymbolType alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_SymbolType :: SymbolType  -> T_SymbolType 
sem_SymbolType { SymbolType | st_vars = st_vars_,st_args = st_args_,st_args_strictness = st_args_strictness_,st_arity = st_arity_,st_result = st_result_,st_context = st_context_,st_attr_vars = st_attr_vars_,st_attr_env = st_attr_env_ } = sem_SymbolType_SymbolType st_vars_ st_args_ st_args_strictness_ st_arity_ st_result_ st_context_ st_attr_vars_ st_attr_env_

// semantic domain
attach_T_SymbolType (T_SymbolType t_SymbolType) = t_SymbolType
inv_SymbolType_s56 (C_SymbolType_s56 x) = x
sem_SymbolType_SymbolType  :: ([TypeVar]) ([AType]) (StrictnessList) (Int) (AType) ([TypeContext]) ([AttributeVar]) ([AttrInequality]) -> T_SymbolType 
sem_SymbolType_SymbolType arg_st_vars_ arg_st_args_ arg_st_args_strictness_ arg_st_arity_ arg_st_result_ arg_st_context_ arg_st_attr_vars_ arg_st_attr_env_ = T_SymbolType (lift st56) where
   st56 =
         let
             v55 (T_SymbolType_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOisTask = rule937 arg_st_result_
                           alhsOhasRecs = rule938  Void
                           alhsOmEntryId = rule939  Void
                           alhsOmExitId = rule940  Void
                           alhsOppAg = rule941  Void
                           alhsOppAgs = rule942  Void
                           alhsOppDebug = rule943  Void
                           alhsOppDebugs = rule944  Void
                           alhsOrecNode = rule945  Void
                           lcopy = rule946 arg_st_args_ arg_st_args_strictness_ arg_st_arity_ arg_st_attr_env_ arg_st_attr_vars_ arg_st_context_ arg_st_result_ arg_st_vars_
                           alhsOcopy = rule947 lcopy
                           alhsOgraph = rule948 alhsIgraph
                           ag__result_ = T_SymbolType_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOisTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_SymbolType_s56 v55
   /*# LINE 56 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
   rule937 st_result_ =
                      /*# LINE 56 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/MkGraph.ag" #*/
                      case st_result_.at_type of
                        TA   tsi _     -> symTyIsTask` tsi
                        TAS  tsi _  _  -> symTyIsTask` tsi
                        _              -> False
                      where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"
                      /*# LINE 5166 "/Users/norm2782/Documents/PhD/Projects/clean-compiler/branches/itask-tonic/frontend/Tonic/Tonic.icl"#*/
   rule938  (_) =
     False
   rule939  (_) =
     Nothing
   rule940  (_) =
     Nothing
   rule941  (_) =
     empty
   rule942  (_) =
     []
   rule943  (_) =
     empty
   rule944  (_) =
     []
   rule945  (_) =
     False
   rule946 st_args_ st_args_strictness_ st_arity_ st_attr_env_ st_attr_vars_ st_context_ st_result_ st_vars_ =
     {SymbolType|st_vars = st_vars_ , st_args = st_args_ , st_args_strictness = st_args_strictness_ , st_arity = st_arity_ , st_result = st_result_ , st_context = st_context_ , st_attr_vars = st_attr_vars_ , st_attr_env = st_attr_env_}
   rule947 lcopy =
     lcopy
   rule948 ((alhsIgraph)) =
     alhsIgraph
