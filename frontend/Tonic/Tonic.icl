implementation module Tonic.Tonic

// 2 "./frontend/Tonic/MkGraph.ag"

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
  :: FunctionBody {..}, :: TransformedBody {..}, :: CheckedBody, :: ParsedBody
// 26 "frontend/Tonic/Tonic.icl"

// 2 "./frontend/Tonic/Pretty.ag"

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
// 47 "frontend/Tonic/Tonic.icl"

// 2 "./frontend/Tonic/ExprSyn.ag"

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
// 66 "frontend/Tonic/Tonic.icl"
from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// 199 "./frontend/Tonic/MkGraph.ag"


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
// 177 "frontend/Tonic/Tonic.icl"

// 163 "./frontend/Tonic/Pretty.ag"

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
// 278 "frontend/Tonic/Tonic.icl"
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
recNode_Syn_App :: Syn_App -> (Bool)
recNode_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_App :: Syn_App -> ([Doc])
ppDebugs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_App :: Syn_App -> (Doc)
ppDebug_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_App :: Syn_App -> ([Doc])
ppAgs_Syn_App (Syn_App _ _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_App :: Syn_App -> (Doc)
ppAg_Syn_App (Syn_App _ _ _ _ _ _ _ x _ _ _ _) = x
mSymbolType_Syn_App :: Syn_App -> (Maybe SymbolType)
mSymbolType_Syn_App (Syn_App _ _ _ _ _ _ x _ _ _ _ _) = x
mFunDef_Syn_App :: Syn_App -> (Maybe GFunDef)
mFunDef_Syn_App (Syn_App _ _ _ _ _ x _ _ _ _ _ _) = x
mExitId_Syn_App :: Syn_App -> (Maybe Int)
mExitId_Syn_App (Syn_App _ _ _ _ x _ _ _ _ _ _ _) = x
mEntryId_Syn_App :: Syn_App -> (Maybe Int)
mEntryId_Syn_App (Syn_App _ _ _ x _ _ _ _ _ _ _ _) = x
hasRecs_Syn_App :: Syn_App -> (Bool)
hasRecs_Syn_App (Syn_App _ _ x _ _ _ _ _ _ _ _ _) = x
graph_Syn_App :: Syn_App -> (GinGraph)
graph_Syn_App (Syn_App _ x _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_App :: Syn_App -> (App)
copy_Syn_App (Syn_App x _ _ _ _ _ _ _ _ _ _ _) = x
wrap_App :: T_App  Inh_App  -> (Syn_App )
wrap_App (T_App act) (Inh_App alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_App_s2 sem arg) >>= \ (T_App_vOut1 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_App alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_App :: App  -> T_App 
sem_App { App | app_symb = app_symb_,app_args = app_args_,app_info_ptr = app_info_ptr_ } = sem_App_App ( sem_SymbIdent app_symb_ ) ( sem_Expressions app_args_ ) app_info_ptr_    

// semantic domain
attach_T_App (T_App t_App) = t_App
inv_App_s2 (C_App_s2 x) = x
sem_App_App  :: (T_SymbIdent ) (T_Expressions ) (ExprInfoPtr)     -> T_App 
sem_App_App arg_app_symb_ arg_app_args_ arg_app_info_ptr_     = T_App (lift st2) where
   st2 =
        let
            v1 :: T_App_v1 
            v1 = \ (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_app_symbX53 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_app_symb_))
                          st_app_argsX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_app_args_))
                          st_bindLhsExprIX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression bindLhsExprI_val_)))
                          st_bindRhsAppIX2 = 'Control.Monad.Identity'.runIdentity (attach_T_App ((sem_App bindRhsAppI_val_)))
                          st_bindRhsFunDefX29 = 'Control.Monad.Identity'.runIdentity (attach_T_GFunDef ((sem_GFunDef bindRhsFunDef_val_)))
                          st_bindRhsSymbolTypeIX56 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbolType ((sem_SymbolType bindRhsSymbolTypeI_val_)))
                          (T_SymbIdent_vOut52 aapp_symbIcopy aapp_symbIgraph aapp_symbIhasRecs aapp_symbIident aapp_symbIisCurrTask aapp_symbIisInfix aapp_symbImEntryId aapp_symbImExitId aapp_symbImFunDef aapp_symbImSymbolType aapp_symbIppAg aapp_symbIppAgs aapp_symbIppDebug aapp_symbIppDebugs aapp_symbIrecNode) = inv_SymbIdent_s53 st_app_symbX53 (T_SymbIdent_vIn52 aapp_symbOcaseExpr aapp_symbOcurrTaskName aapp_symbOgraph aapp_symbOmergeId aapp_symbOmoduleEnv)
                          (T_Expressions_vOut16 aapp_argsIcopy aapp_argsIgraph aapp_argsIhasRecs aapp_argsImEntryId aapp_argsImExitId aapp_argsIppAg aapp_argsIppAgs aapp_argsIppDebug aapp_argsIppDebugs aapp_argsIrecNode) = inv_Expressions_s17 st_app_argsX17 (T_Expressions_vIn16 aapp_argsOcaseExpr aapp_argsOcurrTaskName aapp_argsOgraph aapp_argsOmergeId aapp_argsOmoduleEnv)
                          (T_Expression_vOut13 abindLhsExprIIcopy abindLhsExprIIgraph abindLhsExprIIhasRecs abindLhsExprIImEntryId abindLhsExprIImExitId abindLhsExprIIppAg abindLhsExprIIppAgs abindLhsExprIIppDebug abindLhsExprIIppDebugs abindLhsExprIIrecNode) = inv_Expression_s14 st_bindLhsExprIX14 (T_Expression_vIn13 abindLhsExprIOcaseExpr abindLhsExprIOcurrTaskName abindLhsExprIOgraph abindLhsExprIOmergeId abindLhsExprIOmoduleEnv)
                          (T_App_vOut1 abindRhsAppIIcopy abindRhsAppIIgraph abindRhsAppIIhasRecs abindRhsAppIImEntryId abindRhsAppIImExitId abindRhsAppIImFunDef abindRhsAppIImSymbolType abindRhsAppIIppAg abindRhsAppIIppAgs abindRhsAppIIppDebug abindRhsAppIIppDebugs abindRhsAppIIrecNode) = inv_App_s2 st_bindRhsAppIX2 (T_App_vIn1 abindRhsAppIOcaseExpr abindRhsAppIOcurrTaskName abindRhsAppIOgraph abindRhsAppIOmergeId abindRhsAppIOmoduleEnv)
                          (T_GFunDef_vOut28 abindRhsFunDefIcopy abindRhsFunDefIfunArgs abindRhsFunDefIfunRhs abindRhsFunDefIgraph abindRhsFunDefIhasRecs abindRhsFunDefImEntryId abindRhsFunDefImExitId abindRhsFunDefIrecNode) = inv_GFunDef_s29 st_bindRhsFunDefX29 (T_GFunDef_vIn28 abindRhsFunDefOcaseExpr abindRhsFunDefOcurrTaskName abindRhsFunDefOgraph abindRhsFunDefOmergeId abindRhsFunDefOmoduleEnv)
                          (T_SymbolType_vOut55 abindRhsSymbolTypeIIcopy abindRhsSymbolTypeIIgraph abindRhsSymbolTypeIIhasRecs abindRhsSymbolTypeIImEntryId abindRhsSymbolTypeIImExitId abindRhsSymbolTypeIIppAg abindRhsSymbolTypeIIppAgs abindRhsSymbolTypeIIppDebug abindRhsSymbolTypeIIppDebugs abindRhsSymbolTypeIIrecNode) = inv_SymbolType_s56 st_bindRhsSymbolTypeIX56 (T_SymbolType_vIn55 abindRhsSymbolTypeIOcaseExpr abindRhsSymbolTypeIOcurrTaskName abindRhsSymbolTypeIOgraph abindRhsSymbolTypeIOmergeId abindRhsSymbolTypeIOmoduleEnv)
                          alhsOmFunDef :: Maybe GFunDef
                          alhsOmFunDef = rule0 aapp_symbImFunDef
                          alhsOmSymbolType :: Maybe SymbolType
                          alhsOmSymbolType = rule1 aapp_symbImSymbolType
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule2 aapp_symbIcopy alhsIgraph alhsImoduleEnv ltaskGraph
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule3 ltaskEntryId
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule4 ltaskExitId
                          (ltaskGraph,ltaskEntryId,ltaskExitId) = rule5 aapp_symbIident lassignEntryId lassignExitId lassignGraph lbinAppEntryId lbinAppExitId lbinAppGraph lbindGraph lparBinAppEntryId lparBinAppExitId lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId
                          lnodictargs = rule6 alhsImoduleEnv lcopy
                          (lbindLhsExpr,lbindRhsApp) = rule7 lnodictargs
                          bindLhsExprI_val_ = rule8 lbindLhsExpr
                          bindRhsAppI_val_ = rule9 lbindRhsApp
                          lbindRhsSymbolType = rule10 abindRhsAppIImSymbolType
                          bindRhsFunDef_val_ = rule11 abindRhsAppIImFunDef
                          bindRhsSymbolTypeI_val_ = rule12 lbindRhsSymbolType
                          lbindGraph = rule13 abindLhsExprIImEntryId abindLhsExprIImExitId abindRhsFunDefIfunArgs abindRhsFunDefIfunRhs abindRhsFunDefImEntryId abindRhsFunDefImExitId alhsIgraph alhsImoduleEnv lbindLhsExpr lbindRhsSymbolType
                          (lreturnId,lreturnGraph) = rule14 alhsIgraph lnodictargs
                          lbinAppGraph = rule15  Void
                          lbinAppEntryId = rule16  Void
                          lbinAppExitId = rule17  Void
                          lassignGraph = rule18  Void
                          lassignEntryId = rule19  Void
                          lassignExitId = rule20  Void
                          lstepGraph = rule21  Void
                          lstepEntryId = rule22  Void
                          lstepExitId = rule23  Void
                          lparBinAppGraph = rule24  Void
                          lparBinAppEntryId = rule25  Void
                          lparBinAppExitId = rule26  Void
                          lparListAppGraph = rule27  Void
                          lparListAppEntryId = rule28  Void
                          lparListAppExitId = rule29  Void
                          (ltaskAppId,ltaskAppGraph) = rule30 aapp_argsIppAgs aapp_symbIident aapp_symbIisCurrTask alhsIgraph
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule31 aapp_argsIppAgs aapp_symbIppAg
                          alhsOppAg :: Doc
                          alhsOppAg = rule32 aapp_argsIppAgs aapp_symbIisInfix aapp_symbIppAg alhsImoduleEnv lcopy
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule33 aapp_argsIhasRecs aapp_symbIhasRecs abindLhsExprIIhasRecs abindRhsAppIIhasRecs abindRhsFunDefIhasRecs abindRhsSymbolTypeIIhasRecs
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule34 aapp_argsIppAgs aapp_symbIppAgs abindLhsExprIIppAgs abindRhsAppIIppAgs abindRhsSymbolTypeIIppAgs
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule35 aapp_argsIppDebugs aapp_symbIppDebugs abindLhsExprIIppDebugs abindRhsAppIIppDebugs abindRhsSymbolTypeIIppDebugs
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule36 aapp_argsIrecNode aapp_symbIrecNode abindLhsExprIIrecNode abindRhsAppIIrecNode abindRhsFunDefIrecNode abindRhsSymbolTypeIIrecNode
                          lcopy = rule37 aapp_argsIcopy aapp_symbIcopy arg_app_info_ptr_
                          alhsOcopy :: App
                          alhsOcopy = rule38 lcopy
                          aapp_symbOcaseExpr = rule39 alhsIcaseExpr
                          aapp_symbOcurrTaskName = rule40 alhsIcurrTaskName
                          aapp_symbOgraph = rule41 alhsIgraph
                          aapp_symbOmergeId = rule42 alhsImergeId
                          aapp_symbOmoduleEnv = rule43 alhsImoduleEnv
                          aapp_argsOcaseExpr = rule44 alhsIcaseExpr
                          aapp_argsOcurrTaskName = rule45 alhsIcurrTaskName
                          aapp_argsOgraph = rule46 aapp_symbIgraph
                          aapp_argsOmergeId = rule47 alhsImergeId
                          aapp_argsOmoduleEnv = rule48 alhsImoduleEnv
                          abindLhsExprIOcaseExpr = rule49 alhsIcaseExpr
                          abindLhsExprIOcurrTaskName = rule50 alhsIcurrTaskName
                          abindLhsExprIOgraph = rule51 aapp_argsIgraph
                          abindLhsExprIOmergeId = rule52 alhsImergeId
                          abindLhsExprIOmoduleEnv = rule53 alhsImoduleEnv
                          abindRhsAppIOcaseExpr = rule54 alhsIcaseExpr
                          abindRhsAppIOcurrTaskName = rule55 alhsIcurrTaskName
                          abindRhsAppIOgraph = rule56 abindLhsExprIIgraph
                          abindRhsAppIOmergeId = rule57 alhsImergeId
                          abindRhsAppIOmoduleEnv = rule58 alhsImoduleEnv
                          abindRhsFunDefOcaseExpr = rule59 alhsIcaseExpr
                          abindRhsFunDefOcurrTaskName = rule60 alhsIcurrTaskName
                          abindRhsFunDefOgraph = rule61 abindRhsAppIIgraph
                          abindRhsFunDefOmergeId = rule62 alhsImergeId
                          abindRhsFunDefOmoduleEnv = rule63 alhsImoduleEnv
                          abindRhsSymbolTypeIOcaseExpr = rule64 alhsIcaseExpr
                          abindRhsSymbolTypeIOcurrTaskName = rule65 alhsIcurrTaskName
                          abindRhsSymbolTypeIOgraph = rule66 abindRhsFunDefIgraph
                          abindRhsSymbolTypeIOmergeId = rule67 alhsImergeId
                          abindRhsSymbolTypeIOmoduleEnv = rule68 alhsImoduleEnv
                          ag__result_ = T_App_vOut1 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_App_s2 v1
   /*# LINE 51 "./frontend/Tonic/MkGraph.ag" #*/
   rule0 = \ ((aapp_symbImFunDef)) ->
                        /*# LINE 51 "./frontend/Tonic/MkGraph.ag" #*/
                        aapp_symbImFunDef
                        /*# LINE 438 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 52 "./frontend/Tonic/MkGraph.ag" #*/
   rule1 = \ ((aapp_symbImSymbolType)) ->
                            /*# LINE 52 "./frontend/Tonic/MkGraph.ag" #*/
                            aapp_symbImSymbolType
                            /*# LINE 443 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 77 "./frontend/Tonic/MkGraph.ag" #*/
   rule2 = \ ((aapp_symbIcopy)) ((alhsIgraph)) ((alhsImoduleEnv)) ltaskGraph ->
                    /*# LINE 77 "./frontend/Tonic/MkGraph.ag" #*/
                    if (symbIdentIsTask alhsImoduleEnv aapp_symbIcopy)
                      ltaskGraph
                      alhsIgraph
                    /*# LINE 450 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 80 "./frontend/Tonic/MkGraph.ag" #*/
   rule3 = \ ltaskEntryId ->
                       /*# LINE 80 "./frontend/Tonic/MkGraph.ag" #*/
                       ltaskEntryId
                       /*# LINE 455 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
   rule4 = \ ltaskExitId ->
                       /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
                       ltaskExitId
                       /*# LINE 460 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
   rule5 = \ ((aapp_symbIident)) lassignEntryId lassignExitId lassignGraph lbinAppEntryId lbinAppExitId lbinAppGraph lbindGraph lparBinAppEntryId lparBinAppExitId lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId ->
                                                   /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
                                                   case aapp_symbIident of
                                                     ">>="       -> (lbindGraph    , Nothing, Nothing)
                                                     "return"    -> (lreturnGraph    , Just lreturnId    , Just lreturnId    )
                                                     ">>|"       -> (lbinAppGraph     Nothing, lbinAppEntryId     Nothing, lbinAppExitId     Nothing)
                                                     "@:"        -> (lassignGraph    , lassignEntryId    , lassignExitId    )
                                                     ">>*"       -> (lstepGraph    , lstepEntryId    , lstepExitId    )
                                                     "-||-"      -> (lparBinAppGraph     DisFirstBin, lparBinAppEntryId     DisFirstBin, lparBinAppExitId     DisFirstBin)
                                                     "||-"       -> (lparBinAppGraph     DisRight, lparBinAppEntryId     DisFirstBin, lparBinAppExitId     DisFirstBin)
                                                     "-||"       -> (lparBinAppGraph     DisLeft, lparBinAppEntryId     DisFirstBin, lparBinAppExitId     DisFirstBin)
                                                     "-&&-"      -> (lparBinAppGraph     ConPair, lparBinAppEntryId     DisFirstBin, lparBinAppExitId     DisFirstBin)
                                                     "anyTask"   -> (lparListAppGraph     DisFirstList, lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                                                     "allTasks"  -> (lparListAppGraph     ConAll, lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                                                     _           -> (ltaskAppGraph    , ltaskAppId    , ltaskAppId    )
                                                   /*# LINE 477 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 97 "./frontend/Tonic/MkGraph.ag" #*/
   rule6 = \ ((alhsImoduleEnv)) lcopy ->
                         /*# LINE 97 "./frontend/Tonic/MkGraph.ag" #*/
                         dropAppContexts lcopy alhsImoduleEnv
                         /*# LINE 482 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 99 "./frontend/Tonic/MkGraph.ag" #*/
   rule7 = \ lnodictargs ->
                                         /*# LINE 99 "./frontend/Tonic/MkGraph.ag" #*/
                                         case lnodictargs     of
                                           [e:App a:_] -> (e, a)
                                           _                 -> abort ("Invalid bind: ")
                                         /*# LINE 489 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 105 "./frontend/Tonic/MkGraph.ag" #*/
   rule8 = \ lbindLhsExpr ->
                            /*# LINE 105 "./frontend/Tonic/MkGraph.ag" #*/
                            lbindLhsExpr
                            /*# LINE 494 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 108 "./frontend/Tonic/MkGraph.ag" #*/
   rule9 = \ lbindRhsApp ->
                           /*# LINE 108 "./frontend/Tonic/MkGraph.ag" #*/
                           lbindRhsApp
                           /*# LINE 499 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
   rule10 = \ ((abindRhsAppIImSymbolType)) ->
                                /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
                                fromMaybe (abort "mkGraphAlg #2: failed to find symbol type")
                                abindRhsAppIImSymbolType
                                /*# LINE 505 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 114 "./frontend/Tonic/MkGraph.ag" #*/
   rule11 = \ ((abindRhsAppIImFunDef)) ->
                             /*# LINE 114 "./frontend/Tonic/MkGraph.ag" #*/
                             fromMaybe (abort "mkGraphAlg #1: failed to find function definition")
                             abindRhsAppIImFunDef
                             /*# LINE 511 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 118 "./frontend/Tonic/MkGraph.ag" #*/
   rule12 = \ lbindRhsSymbolType ->
                                  /*# LINE 118 "./frontend/Tonic/MkGraph.ag" #*/
                                  lbindRhsSymbolType
                                  /*# LINE 516 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
   rule13 = \ ((abindLhsExprIImEntryId)) ((abindLhsExprIImExitId)) ((abindRhsFunDefIfunArgs)) ((abindRhsFunDefIfunRhs)) ((abindRhsFunDefImEntryId)) ((abindRhsFunDefImExitId)) ((alhsIgraph)) ((alhsImoduleEnv)) lbindLhsExpr lbindRhsSymbolType ->
                        /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
                        case ( abindLhsExprIImEntryId, abindLhsExprIImExitId
                             , abindRhsFunDefImEntryId, abindRhsFunDefImExitId) of
                          (Just _, Just lx, Just rn, Just _)
                             # patid = withHead freeVarName (abort "Invalid bind")
                                     $ [x \\ x <- dropContexts lbindRhsSymbolType     abindRhsFunDefIfunArgs | x.fv_def_level == -1]
                             = addEdge (mkEdge patid) (lx, rn) alhsIgraph
                          (_, lid, rid, _)        = edgeErr alhsImoduleEnv "bind edge" lid lbindLhsExpr     rid abindRhsFunDefIfunRhs
                        /*# LINE 527 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 128 "./frontend/Tonic/MkGraph.ag" #*/
   rule14 = \ ((alhsIgraph)) lnodictargs ->
                                      /*# LINE 128 "./frontend/Tonic/MkGraph.ag" #*/
                                      let node   = GReturn $ withHead f (abort "Invalid return") lnodictargs
                                          f _ = GCleanExpression "(return)"
                                      in  addNode node alhsIgraph
                                      /*# LINE 534 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 136 "./frontend/Tonic/MkGraph.ag" #*/
   rule15 = \  (_) ->
                          /*# LINE 136 "./frontend/Tonic/MkGraph.ag" #*/
                          \mPat -> undef
                          /*# LINE 539 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 137 "./frontend/Tonic/MkGraph.ag" #*/
   rule16 = \  (_) ->
                            /*# LINE 137 "./frontend/Tonic/MkGraph.ag" #*/
                            \mPat -> undef
                            /*# LINE 544 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 138 "./frontend/Tonic/MkGraph.ag" #*/
   rule17 = \  (_) ->
                           /*# LINE 138 "./frontend/Tonic/MkGraph.ag" #*/
                           \mPat -> undef
                           /*# LINE 549 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 140 "./frontend/Tonic/MkGraph.ag" #*/
   rule18 = \  (_) ->
                          /*# LINE 140 "./frontend/Tonic/MkGraph.ag" #*/
                          undef
                          /*# LINE 554 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 141 "./frontend/Tonic/MkGraph.ag" #*/
   rule19 = \  (_) ->
                            /*# LINE 141 "./frontend/Tonic/MkGraph.ag" #*/
                            undef
                            /*# LINE 559 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 142 "./frontend/Tonic/MkGraph.ag" #*/
   rule20 = \  (_) ->
                           /*# LINE 142 "./frontend/Tonic/MkGraph.ag" #*/
                           undef
                           /*# LINE 564 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 144 "./frontend/Tonic/MkGraph.ag" #*/
   rule21 = \  (_) ->
                        /*# LINE 144 "./frontend/Tonic/MkGraph.ag" #*/
                        abort "Step not implemented yet"
                        /*# LINE 569 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 145 "./frontend/Tonic/MkGraph.ag" #*/
   rule22 = \  (_) ->
                          /*# LINE 145 "./frontend/Tonic/MkGraph.ag" #*/
                          undef
                          /*# LINE 574 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 146 "./frontend/Tonic/MkGraph.ag" #*/
   rule23 = \  (_) ->
                         /*# LINE 146 "./frontend/Tonic/MkGraph.ag" #*/
                         undef
                         /*# LINE 579 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 148 "./frontend/Tonic/MkGraph.ag" #*/
   rule24 = \  (_) ->
                               /*# LINE 148 "./frontend/Tonic/MkGraph.ag" #*/
                               \join -> undef
                               /*# LINE 584 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 149 "./frontend/Tonic/MkGraph.ag" #*/
   rule25 = \  (_) ->
                               /*# LINE 149 "./frontend/Tonic/MkGraph.ag" #*/
                               \join -> undef
                               /*# LINE 589 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 150 "./frontend/Tonic/MkGraph.ag" #*/
   rule26 = \  (_) ->
                               /*# LINE 150 "./frontend/Tonic/MkGraph.ag" #*/
                               \join -> undef
                               /*# LINE 594 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 152 "./frontend/Tonic/MkGraph.ag" #*/
   rule27 = \  (_) ->
                                /*# LINE 152 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 599 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 153 "./frontend/Tonic/MkGraph.ag" #*/
   rule28 = \  (_) ->
                                /*# LINE 153 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 604 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 154 "./frontend/Tonic/MkGraph.ag" #*/
   rule29 = \  (_) ->
                                /*# LINE 154 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 609 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 156 "./frontend/Tonic/MkGraph.ag" #*/
   rule30 = \ ((aapp_argsIppAgs)) ((aapp_symbIident)) ((aapp_symbIisCurrTask)) ((alhsIgraph)) ->
                                        /*# LINE 156 "./frontend/Tonic/MkGraph.ag" #*/
                                        if aapp_symbIisCurrTask
                                          (Nothing, alhsIgraph)
                                          (let appArgs = map (GCleanExpression o ppCompact) aapp_argsIppAgs
                                               (n, g)  = addNode (GTaskApp aapp_symbIident appArgs) alhsIgraph
                                           in (Just n, g))
                                        /*# LINE 618 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 63 "./frontend/Tonic/Pretty.ag" #*/
   rule31 = \ ((aapp_argsIppAgs)) ((aapp_symbIppAg)) ->
                      /*# LINE 63 "./frontend/Tonic/Pretty.ag" #*/
                      let argsPP = hcat $ intersperse (text ", ") aapp_argsIppAgs
                      in  text "<App>" <+> aapp_symbIppAg <+> brackets argsPP
                      /*# LINE 624 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 66 "./frontend/Tonic/Pretty.ag" #*/
   rule32 = \ ((aapp_argsIppAgs)) ((aapp_symbIisInfix)) ((aapp_symbIppAg)) ((alhsImoduleEnv)) lcopy ->
                      /*# LINE 66 "./frontend/Tonic/Pretty.ag" #*/
                      let appc      = lcopy
                      in  case appc.app_args of
                            []     -> aapp_symbIppAg
                            [x:xs] -> if aapp_symbIisInfix
                                        (ppExpression alhsImoduleEnv x <+> aapp_symbIppAg <+> hcat (intersperse (text " ") (map (ppExpression alhsImoduleEnv) xs)))
                                        (aapp_symbIppAg <+> hcat (intersperse (text " ") aapp_argsIppAgs))
                      /*# LINE 634 "frontend/Tonic/Tonic.icl"#*/
   rule33 = \ ((aapp_argsIhasRecs)) ((aapp_symbIhasRecs)) ((abindLhsExprIIhasRecs)) ((abindRhsAppIIhasRecs)) ((abindRhsFunDefIhasRecs)) ((abindRhsSymbolTypeIIhasRecs)) ->
     aapp_symbIhasRecs || aapp_argsIhasRecs || abindLhsExprIIhasRecs || abindRhsAppIIhasRecs || abindRhsFunDefIhasRecs || abindRhsSymbolTypeIIhasRecs
   rule34 = \ ((aapp_argsIppAgs)) ((aapp_symbIppAgs)) ((abindLhsExprIIppAgs)) ((abindRhsAppIIppAgs)) ((abindRhsSymbolTypeIIppAgs)) ->
     aapp_symbIppAgs ++ aapp_argsIppAgs ++ abindLhsExprIIppAgs ++ abindRhsAppIIppAgs ++ abindRhsSymbolTypeIIppAgs
   rule35 = \ ((aapp_argsIppDebugs)) ((aapp_symbIppDebugs)) ((abindLhsExprIIppDebugs)) ((abindRhsAppIIppDebugs)) ((abindRhsSymbolTypeIIppDebugs)) ->
     aapp_symbIppDebugs ++ aapp_argsIppDebugs ++ abindLhsExprIIppDebugs ++ abindRhsAppIIppDebugs ++ abindRhsSymbolTypeIIppDebugs
   rule36 = \ ((aapp_argsIrecNode)) ((aapp_symbIrecNode)) ((abindLhsExprIIrecNode)) ((abindRhsAppIIrecNode)) ((abindRhsFunDefIrecNode)) ((abindRhsSymbolTypeIIrecNode)) ->
     aapp_symbIrecNode || aapp_argsIrecNode || abindLhsExprIIrecNode || abindRhsAppIIrecNode || abindRhsFunDefIrecNode || abindRhsSymbolTypeIIrecNode
   rule37 = \ ((aapp_argsIcopy)) ((aapp_symbIcopy)) app_info_ptr_ ->
     {App|app_symb = aapp_symbIcopy , app_args = aapp_argsIcopy , app_info_ptr = app_info_ptr_}
   rule38 = \ lcopy ->
     lcopy
   rule39 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule40 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule41 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule42 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule43 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule44 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule45 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule46 = \ ((aapp_symbIgraph)) ->
     aapp_symbIgraph
   rule47 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule48 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule49 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule50 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule51 = \ ((aapp_argsIgraph)) ->
     aapp_argsIgraph
   rule52 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule53 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule54 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule55 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule56 = \ ((abindLhsExprIIgraph)) ->
     abindLhsExprIIgraph
   rule57 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule58 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule59 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule60 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule61 = \ ((abindRhsAppIIgraph)) ->
     abindRhsAppIIgraph
   rule62 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule63 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule64 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule65 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule66 = \ ((abindRhsFunDefIgraph)) ->
     abindRhsFunDefIgraph
   rule67 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule68 = \ ((alhsImoduleEnv)) ->
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
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule69 arg_str_
                          alhsOppAg :: Doc
                          alhsOppAg = rule70 arg_str_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule71  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule72  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule73  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule74  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule75  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule76  Void
                          lcopy = rule77 arg_str_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule78 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule79 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 120 "./frontend/Tonic/Pretty.ag" #*/
   rule69 = \ str_ ->
                        /*# LINE 120 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 796 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 121 "./frontend/Tonic/Pretty.ag" #*/
   rule70 = \ str_ ->
                        /*# LINE 121 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 801 "frontend/Tonic/Tonic.icl"#*/
   rule71 = \  (_) ->
     False
   rule72 = \  (_) ->
     Nothing
   rule73 = \  (_) ->
     Nothing
   rule74 = \  (_) ->
     []
   rule75 = \  (_) ->
     []
   rule76 = \  (_) ->
     False
   rule77 = \ str_ ->
     BVI str_
   rule78 = \ lcopy ->
     lcopy
   rule79 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_BasicValue_BVInt  :: (Int) -> T_BasicValue 
sem_BasicValue_BVInt arg_i_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule80 arg_i_
                          alhsOppAg :: Doc
                          alhsOppAg = rule81 arg_i_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule82  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule83  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule84  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule85  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule86  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule87  Void
                          lcopy = rule88 arg_i_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule89 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule90 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 122 "./frontend/Tonic/Pretty.ag" #*/
   rule80 = \ i_ ->
                          /*# LINE 122 "./frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 855 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 123 "./frontend/Tonic/Pretty.ag" #*/
   rule81 = \ i_ ->
                          /*# LINE 123 "./frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 860 "frontend/Tonic/Tonic.icl"#*/
   rule82 = \  (_) ->
     False
   rule83 = \  (_) ->
     Nothing
   rule84 = \  (_) ->
     Nothing
   rule85 = \  (_) ->
     []
   rule86 = \  (_) ->
     []
   rule87 = \  (_) ->
     False
   rule88 = \ i_ ->
     BVInt i_
   rule89 = \ lcopy ->
     lcopy
   rule90 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_BasicValue_BVC  :: (String) -> T_BasicValue 
sem_BasicValue_BVC arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule91 arg_str_
                          alhsOppAg :: Doc
                          alhsOppAg = rule92 arg_str_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule93  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule94  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule95  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule96  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule97  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule98  Void
                          lcopy = rule99 arg_str_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule100 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule101 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 124 "./frontend/Tonic/Pretty.ag" #*/
   rule91 = \ str_ ->
                        /*# LINE 124 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 914 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 125 "./frontend/Tonic/Pretty.ag" #*/
   rule92 = \ str_ ->
                        /*# LINE 125 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 919 "frontend/Tonic/Tonic.icl"#*/
   rule93 = \  (_) ->
     False
   rule94 = \  (_) ->
     Nothing
   rule95 = \  (_) ->
     Nothing
   rule96 = \  (_) ->
     []
   rule97 = \  (_) ->
     []
   rule98 = \  (_) ->
     False
   rule99 = \ str_ ->
     BVC str_
   rule100 = \ lcopy ->
     lcopy
   rule101 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_BasicValue_BVB  :: (Bool) -> T_BasicValue 
sem_BasicValue_BVB arg_b_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule102 arg_b_
                          alhsOppAg :: Doc
                          alhsOppAg = rule103 arg_b_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule104  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule105  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule106  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule107  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule108  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule109  Void
                          lcopy = rule110 arg_b_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule111 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule112 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 126 "./frontend/Tonic/Pretty.ag" #*/
   rule102 = \ b_ ->
                        /*# LINE 126 "./frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 973 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 127 "./frontend/Tonic/Pretty.ag" #*/
   rule103 = \ b_ ->
                        /*# LINE 127 "./frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 978 "frontend/Tonic/Tonic.icl"#*/
   rule104 = \  (_) ->
     False
   rule105 = \  (_) ->
     Nothing
   rule106 = \  (_) ->
     Nothing
   rule107 = \  (_) ->
     []
   rule108 = \  (_) ->
     []
   rule109 = \  (_) ->
     False
   rule110 = \ b_ ->
     BVB b_
   rule111 = \ lcopy ->
     lcopy
   rule112 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_BasicValue_BVR  :: (String) -> T_BasicValue 
sem_BasicValue_BVR arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule113 arg_str_
                          alhsOppAg :: Doc
                          alhsOppAg = rule114 arg_str_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule115  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule116  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule117  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule118  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule119  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule120  Void
                          lcopy = rule121 arg_str_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule122 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule123 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 128 "./frontend/Tonic/Pretty.ag" #*/
   rule113 = \ str_ ->
                        /*# LINE 128 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1032 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 129 "./frontend/Tonic/Pretty.ag" #*/
   rule114 = \ str_ ->
                        /*# LINE 129 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1037 "frontend/Tonic/Tonic.icl"#*/
   rule115 = \  (_) ->
     False
   rule116 = \  (_) ->
     Nothing
   rule117 = \  (_) ->
     Nothing
   rule118 = \  (_) ->
     []
   rule119 = \  (_) ->
     []
   rule120 = \  (_) ->
     False
   rule121 = \ str_ ->
     BVR str_
   rule122 = \ lcopy ->
     lcopy
   rule123 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_BasicValue_BVS  :: (String) -> T_BasicValue 
sem_BasicValue_BVS arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 :: T_BasicValue_v4 
            v4 = \ (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule124 arg_str_
                          alhsOppAg :: Doc
                          alhsOppAg = rule125 arg_str_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule126  Void
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule127  Void
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule128  Void
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule129  Void
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule130  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule131  Void
                          lcopy = rule132 arg_str_
                          alhsOcopy :: BasicValue
                          alhsOcopy = rule133 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule134 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BasicValue_s5 v4
   /*# LINE 130 "./frontend/Tonic/Pretty.ag" #*/
   rule124 = \ str_ ->
                        /*# LINE 130 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1091 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 131 "./frontend/Tonic/Pretty.ag" #*/
   rule125 = \ str_ ->
                        /*# LINE 131 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 1096 "frontend/Tonic/Tonic.icl"#*/
   rule126 = \  (_) ->
     False
   rule127 = \  (_) ->
     Nothing
   rule128 = \  (_) ->
     Nothing
   rule129 = \  (_) ->
     []
   rule130 = \  (_) ->
     []
   rule131 = \  (_) ->
     False
   rule132 = \ str_ ->
     BVS str_
   rule133 = \ lcopy ->
     lcopy
   rule134 = \ ((alhsIgraph)) ->
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
            v7 :: T_BoundVar_v7 
            v7 = \ (T_BoundVar_vIn7 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_var_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_var_ident_))
                          (T_Ident_vOut43 avar_identIcopy avar_identIgraph avar_identIhasRecs avar_identIident avar_identImEntryId avar_identImExitId avar_identIppAg avar_identIppAgs avar_identIppDebug avar_identIppDebugs avar_identIrecNode) = inv_Ident_s44 st_var_identX44 (T_Ident_vIn43 avar_identOcaseExpr avar_identOcurrTaskName avar_identOgraph avar_identOmergeId avar_identOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule135 avar_identIppDebug
                          alhsOppAg :: Doc
                          alhsOppAg = rule136 avar_identIppAg
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule137 avar_identIhasRecs
                          alhsOmEntryId :: Maybe Int
                          alhsOmEntryId = rule138 avar_identImEntryId
                          alhsOmExitId :: Maybe Int
                          alhsOmExitId = rule139 avar_identImExitId
                          alhsOppAgs :: [Doc]
                          alhsOppAgs = rule140 avar_identIppAgs
                          alhsOppDebugs :: [Doc]
                          alhsOppDebugs = rule141 avar_identIppDebugs
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule142 avar_identIrecNode
                          lcopy = rule143 avar_identIcopy arg_var_expr_ptr_ arg_var_info_ptr_
                          alhsOcopy :: BoundVar
                          alhsOcopy = rule144 lcopy
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule145 avar_identIgraph
                          avar_identOcaseExpr = rule146 alhsIcaseExpr
                          avar_identOcurrTaskName = rule147 alhsIcurrTaskName
                          avar_identOgraph = rule148 alhsIgraph
                          avar_identOmergeId = rule149 alhsImergeId
                          avar_identOmoduleEnv = rule150 alhsImoduleEnv
                          ag__result_ = T_BoundVar_vOut7 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_ )
        in C_BoundVar_s8 v7
   /*# LINE 108 "./frontend/Tonic/Pretty.ag" #*/
   rule135 = \ ((avar_identIppDebug)) ->
                             /*# LINE 108 "./frontend/Tonic/Pretty.ag" #*/
                             avar_identIppDebug
                             /*# LINE 1206 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 109 "./frontend/Tonic/Pretty.ag" #*/
   rule136 = \ ((avar_identIppAg)) ->
                             /*# LINE 109 "./frontend/Tonic/Pretty.ag" #*/
                             avar_identIppAg
                             /*# LINE 1211 "frontend/Tonic/Tonic.icl"#*/
   rule137 = \ ((avar_identIhasRecs)) ->
     avar_identIhasRecs
   rule138 = \ ((avar_identImEntryId)) ->
     avar_identImEntryId
   rule139 = \ ((avar_identImExitId)) ->
     avar_identImExitId
   rule140 = \ ((avar_identIppAgs)) ->
     avar_identIppAgs
   rule141 = \ ((avar_identIppDebugs)) ->
     avar_identIppDebugs
   rule142 = \ ((avar_identIrecNode)) ->
     avar_identIrecNode
   rule143 = \ ((avar_identIcopy)) var_expr_ptr_ var_info_ptr_ ->
     {BoundVar|var_ident = avar_identIcopy , var_info_ptr = var_info_ptr_ , var_expr_ptr = var_expr_ptr_}
   rule144 = \ lcopy ->
     lcopy
   rule145 = \ ((avar_identIgraph)) ->
     avar_identIgraph
   rule146 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule147 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule148 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule149 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule150 = \ ((alhsImoduleEnv)) ->
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
             v10 :: T_DefinedSymbol_v10 
             v10 = \ (T_DefinedSymbol_vIn10 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_ds_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ds_ident_))
                           (T_Ident_vOut43 ads_identIcopy ads_identIgraph ads_identIhasRecs ads_identIident ads_identImEntryId ads_identImExitId ads_identIppAg ads_identIppAgs ads_identIppDebug ads_identIppDebugs ads_identIrecNode) = inv_Ident_s44 st_ds_identX44 (T_Ident_vIn43 ads_identOcaseExpr ads_identOcurrTaskName ads_identOgraph ads_identOmergeId ads_identOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule151 ads_identIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule152 ads_identIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule153 ads_identIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule154 ads_identImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule155 ads_identImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule156 ads_identIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule157 ads_identIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule158 ads_identIrecNode
                           lcopy = rule159 ads_identIcopy arg_ds_arity_ arg_ds_index_
                           alhsOcopy :: DefinedSymbol
                           alhsOcopy = rule160 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule161 ads_identIgraph
                           ads_identOcaseExpr = rule162 alhsIcaseExpr
                           ads_identOcurrTaskName = rule163 alhsIcurrTaskName
                           ads_identOgraph = rule164 alhsIgraph
                           ads_identOmergeId = rule165 alhsImergeId
                           ads_identOmoduleEnv = rule166 alhsImoduleEnv
                           ag__result_ = T_DefinedSymbol_vOut10 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_DefinedSymbol_s11 v10
   /*# LINE 134 "./frontend/Tonic/Pretty.ag" #*/
   rule151 = \ ((ads_identIppDebug)) ->
                                  /*# LINE 134 "./frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppDebug
                                  /*# LINE 1331 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 135 "./frontend/Tonic/Pretty.ag" #*/
   rule152 = \ ((ads_identIppAg)) ->
                                  /*# LINE 135 "./frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppAg
                                  /*# LINE 1336 "frontend/Tonic/Tonic.icl"#*/
   rule153 = \ ((ads_identIhasRecs)) ->
     ads_identIhasRecs
   rule154 = \ ((ads_identImEntryId)) ->
     ads_identImEntryId
   rule155 = \ ((ads_identImExitId)) ->
     ads_identImExitId
   rule156 = \ ((ads_identIppAgs)) ->
     ads_identIppAgs
   rule157 = \ ((ads_identIppDebugs)) ->
     ads_identIppDebugs
   rule158 = \ ((ads_identIrecNode)) ->
     ads_identIrecNode
   rule159 = \ ((ads_identIcopy)) ds_arity_ ds_index_ ->
     {DefinedSymbol|ds_ident = ads_identIcopy , ds_arity = ds_arity_ , ds_index = ds_index_}
   rule160 = \ lcopy ->
     lcopy
   rule161 = \ ((ads_identIgraph)) ->
     ads_identIgraph
   rule162 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule163 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule164 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule165 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule166 = \ ((alhsImoduleEnv)) ->
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
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_bvX8 = 'Control.Monad.Identity'.runIdentity (attach_T_BoundVar (arg_bv_))
                           (T_BoundVar_vOut7 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BoundVar_s8 st_bvX8 (T_BoundVar_vIn7 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule167 abvIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule168 abvIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule169 abvIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule170 abvImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule171 abvImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule172 abvIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule173 abvIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule174 abvIrecNode
                           lcopy = rule175 abvIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule176 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule177 abvIgraph
                           abvOcaseExpr = rule178 alhsIcaseExpr
                           abvOcurrTaskName = rule179 alhsIcurrTaskName
                           abvOgraph = rule180 alhsIgraph
                           abvOmergeId = rule181 alhsImergeId
                           abvOmoduleEnv = rule182 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 75 "./frontend/Tonic/Pretty.ag" #*/
   rule167 = \ ((abvIppDebug)) ->
                      /*# LINE 75 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Var>" <+> abvIppDebug
                      /*# LINE 1480 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 76 "./frontend/Tonic/Pretty.ag" #*/
   rule168 = \ ((abvIppAg)) ->
                      /*# LINE 76 "./frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 1485 "frontend/Tonic/Tonic.icl"#*/
   rule169 = \ ((abvIhasRecs)) ->
     abvIhasRecs
   rule170 = \ ((abvImEntryId)) ->
     abvImEntryId
   rule171 = \ ((abvImExitId)) ->
     abvImExitId
   rule172 = \ ((abvIppAgs)) ->
     abvIppAgs
   rule173 = \ ((abvIppDebugs)) ->
     abvIppDebugs
   rule174 = \ ((abvIrecNode)) ->
     abvIrecNode
   rule175 = \ ((abvIcopy)) ->
     Var abvIcopy
   rule176 = \ lcopy ->
     lcopy
   rule177 = \ ((abvIgraph)) ->
     abvIgraph
   rule178 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule179 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule180 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule181 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule182 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_App  :: (T_App ) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_appX2 = 'Control.Monad.Identity'.runIdentity (attach_T_App (arg_app_))
                           (T_App_vOut1 aappIcopy aappIgraph aappIhasRecs aappImEntryId aappImExitId aappImFunDef aappImSymbolType aappIppAg aappIppAgs aappIppDebug aappIppDebugs aappIrecNode) = inv_App_s2 st_appX2 (T_App_vIn1 aappOcaseExpr aappOcurrTaskName aappOgraph aappOmergeId aappOmoduleEnv)
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule183 aappIgraph
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule184 aappIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule185 aappIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule186 aappIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule187 aappImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule188 aappImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule189 aappIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule190 aappIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule191 aappIrecNode
                           lcopy = rule192 aappIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule193 lcopy
                           aappOcaseExpr = rule194 alhsIcaseExpr
                           aappOcurrTaskName = rule195 alhsIcurrTaskName
                           aappOgraph = rule196 alhsIgraph
                           aappOmergeId = rule197 alhsImergeId
                           aappOmoduleEnv = rule198 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 164 "./frontend/Tonic/MkGraph.ag" #*/
   rule183 = \ ((aappIgraph)) ->
                    /*# LINE 164 "./frontend/Tonic/MkGraph.ag" #*/
                    aappIgraph
                    /*# LINE 1556 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 78 "./frontend/Tonic/Pretty.ag" #*/
   rule184 = \ ((aappIppDebug)) ->
                        /*# LINE 78 "./frontend/Tonic/Pretty.ag" #*/
                        aappIppDebug
                        /*# LINE 1561 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 79 "./frontend/Tonic/Pretty.ag" #*/
   rule185 = \ ((aappIppAg)) ->
                        /*# LINE 79 "./frontend/Tonic/Pretty.ag" #*/
                        aappIppAg
                        /*# LINE 1566 "frontend/Tonic/Tonic.icl"#*/
   rule186 = \ ((aappIhasRecs)) ->
     aappIhasRecs
   rule187 = \ ((aappImEntryId)) ->
     aappImEntryId
   rule188 = \ ((aappImExitId)) ->
     aappImExitId
   rule189 = \ ((aappIppAgs)) ->
     aappIppAgs
   rule190 = \ ((aappIppDebugs)) ->
     aappIppDebugs
   rule191 = \ ((aappIrecNode)) ->
     aappIrecNode
   rule192 = \ ((aappIcopy)) ->
     App aappIcopy
   rule193 = \ lcopy ->
     lcopy
   rule194 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule195 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule196 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule197 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule198 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_At arg_expr_ arg_exprs_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_exprsX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_exprs_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_Expressions_vOut16 aexprsIcopy aexprsIgraph aexprsIhasRecs aexprsImEntryId aexprsImExitId aexprsIppAg aexprsIppAgs aexprsIppDebug aexprsIppDebugs aexprsIrecNode) = inv_Expressions_s17 st_exprsX17 (T_Expressions_vIn16 aexprsOcaseExpr aexprsOcurrTaskName aexprsOgraph aexprsOmergeId aexprsOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule199 aexprIhasRecs aexprsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule200 aexprImEntryId aexprsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule201 aexprImExitId aexprsImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule202 aexprIppAg aexprsIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule203 aexprIppAgs aexprsIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule204 aexprIppDebug aexprsIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule205 aexprIppDebugs aexprsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule206 aexprIrecNode aexprsIrecNode
                           lcopy = rule207 aexprIcopy aexprsIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule208 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule209 aexprsIgraph
                           aexprOcaseExpr = rule210 alhsIcaseExpr
                           aexprOcurrTaskName = rule211 alhsIcurrTaskName
                           aexprOgraph = rule212 alhsIgraph
                           aexprOmergeId = rule213 alhsImergeId
                           aexprOmoduleEnv = rule214 alhsImoduleEnv
                           aexprsOcaseExpr = rule215 alhsIcaseExpr
                           aexprsOcurrTaskName = rule216 alhsIcurrTaskName
                           aexprsOgraph = rule217 aexprIgraph
                           aexprsOmergeId = rule218 alhsImergeId
                           aexprsOmoduleEnv = rule219 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule199 = \ ((aexprIhasRecs)) ((aexprsIhasRecs)) ->
     aexprIhasRecs || aexprsIhasRecs
   rule200 = \ ((aexprImEntryId)) ((aexprsImEntryId)) ->
     aexprImEntryId <> aexprsImEntryId
   rule201 = \ ((aexprImExitId)) ((aexprsImExitId)) ->
     aexprImExitId <> aexprsImExitId
   rule202 = \ ((aexprIppAg)) ((aexprsIppAg)) ->
     aexprIppAg <$$> aexprsIppAg
   rule203 = \ ((aexprIppAgs)) ((aexprsIppAgs)) ->
     aexprIppAgs ++ aexprsIppAgs
   rule204 = \ ((aexprIppDebug)) ((aexprsIppDebug)) ->
     aexprIppDebug <$$> aexprsIppDebug
   rule205 = \ ((aexprIppDebugs)) ((aexprsIppDebugs)) ->
     aexprIppDebugs ++ aexprsIppDebugs
   rule206 = \ ((aexprIrecNode)) ((aexprsIrecNode)) ->
     aexprIrecNode || aexprsIrecNode
   rule207 = \ ((aexprIcopy)) ((aexprsIcopy)) ->
     At aexprIcopy aexprsIcopy
   rule208 = \ lcopy ->
     lcopy
   rule209 = \ ((aexprsIgraph)) ->
     aexprsIgraph
   rule210 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule211 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule212 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule213 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule214 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule215 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule216 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule217 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule218 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule219 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Let arg_let__  = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_gletX32 = 'Control.Monad.Identity'.runIdentity (attach_T_GLet ((sem_GLet glet_val_)))
                           (T_GLet_vOut31 agletIcopy agletIgraph agletIhasRecs agletImEntryId agletImExitId agletIppAg agletIppAgs agletIppDebug agletIppDebugs agletIrecNode) = inv_GLet_s32 st_gletX32 (T_GLet_vIn31 agletOcaseExpr agletOcurrTaskName agletOgraph agletOmergeId agletOmoduleEnv)
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule220 agletIgraph
                           glet_val_ = rule221 alhsImoduleEnv arg_let__
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule222 agletIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule223 agletImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule224 agletImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule225 agletIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule226 agletIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule227 agletIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule228 agletIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule229 agletIrecNode
                           lcopy = rule230 arg_let__
                           alhsOcopy :: Expression
                           alhsOcopy = rule231 lcopy
                           agletOcaseExpr = rule232 alhsIcaseExpr
                           agletOcurrTaskName = rule233 alhsIcurrTaskName
                           agletOgraph = rule234 alhsIgraph
                           agletOmergeId = rule235 alhsImergeId
                           agletOmoduleEnv = rule236 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 167 "./frontend/Tonic/MkGraph.ag" #*/
   rule220 = \ ((agletIgraph)) ->
                    /*# LINE 167 "./frontend/Tonic/MkGraph.ag" #*/
                    agletIgraph
                    /*# LINE 1723 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 170 "./frontend/Tonic/MkGraph.ag" #*/
   rule221 = \ ((alhsImoduleEnv)) let__ ->
                    /*# LINE 170 "./frontend/Tonic/MkGraph.ag" #*/
                    mkGLet alhsImoduleEnv let__
                    /*# LINE 1728 "frontend/Tonic/Tonic.icl"#*/
   rule222 = \ ((agletIhasRecs)) ->
     agletIhasRecs
   rule223 = \ ((agletImEntryId)) ->
     agletImEntryId
   rule224 = \ ((agletImExitId)) ->
     agletImExitId
   rule225 = \ ((agletIppAg)) ->
     agletIppAg
   rule226 = \ ((agletIppAgs)) ->
     agletIppAgs
   rule227 = \ ((agletIppDebug)) ->
     agletIppDebug
   rule228 = \ ((agletIppDebugs)) ->
     agletIppDebugs
   rule229 = \ ((agletIrecNode)) ->
     agletIrecNode
   rule230 = \ let__ ->
     Let let__
   rule231 = \ lcopy ->
     lcopy
   rule232 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule233 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule234 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule235 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule236 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Case arg_case__ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule237  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule238  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule239  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule240  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule241  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule242  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule243  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule244  Void
                           lcopy = rule245 arg_case__
                           alhsOcopy :: Expression
                           alhsOcopy = rule246 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule247 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule237 = \  (_) ->
     False
   rule238 = \  (_) ->
     Nothing
   rule239 = \  (_) ->
     Nothing
   rule240 = \  (_) ->
     empty
   rule241 = \  (_) ->
     []
   rule242 = \  (_) ->
     empty
   rule243 = \  (_) ->
     []
   rule244 = \  (_) ->
     False
   rule245 = \ case__ ->
     Case case__
   rule246 = \ lcopy ->
     lcopy
   rule247 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) (T_Selections ) -> T_Expression 
sem_Expression_Selection arg_skind_ arg_expr_ arg_sels_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule248 aexprIppDebug lrecsel
                           alhsOppAg :: Doc
                           alhsOppAg = rule249 aexprIppAg lrecsel
                           lrecsel = rule250 aselsIppAgs
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule251 aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule252 aexprImEntryId aselsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule253 aexprImExitId aselsImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule254 aexprIppAgs aselsIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule255 aexprIppDebugs aselsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule256 aexprIrecNode aselsIrecNode
                           lcopy = rule257 aexprIcopy aselsIcopy arg_skind_
                           alhsOcopy :: Expression
                           alhsOcopy = rule258 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule259 aselsIgraph
                           aexprOcaseExpr = rule260 alhsIcaseExpr
                           aexprOcurrTaskName = rule261 alhsIcurrTaskName
                           aexprOgraph = rule262 alhsIgraph
                           aexprOmergeId = rule263 alhsImergeId
                           aexprOmoduleEnv = rule264 alhsImoduleEnv
                           aselsOcaseExpr = rule265 alhsIcaseExpr
                           aselsOcurrTaskName = rule266 alhsIcurrTaskName
                           aselsOgraph = rule267 aexprIgraph
                           aselsOmergeId = rule268 alhsImergeId
                           aselsOmoduleEnv = rule269 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 82 "./frontend/Tonic/Pretty.ag" #*/
   rule248 = \ ((aexprIppDebug)) lrecsel ->
                      /*# LINE 82 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Selection>" <+> aexprIppDebug <-> lrecsel
                      /*# LINE 1862 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 84 "./frontend/Tonic/Pretty.ag" #*/
   rule249 = \ ((aexprIppAg)) lrecsel ->
                      /*# LINE 84 "./frontend/Tonic/Pretty.ag" #*/
                      aexprIppAg <-> lrecsel
                      /*# LINE 1867 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 85 "./frontend/Tonic/Pretty.ag" #*/
   rule250 = \ ((aselsIppAgs)) ->
                      /*# LINE 85 "./frontend/Tonic/Pretty.ag" #*/
                      char '.' <-> hcat (intersperse (char '.') $ aselsIppAgs)
                      /*# LINE 1872 "frontend/Tonic/Tonic.icl"#*/
   rule251 = \ ((aexprIhasRecs)) ((aselsIhasRecs)) ->
     aexprIhasRecs || aselsIhasRecs
   rule252 = \ ((aexprImEntryId)) ((aselsImEntryId)) ->
     aexprImEntryId <> aselsImEntryId
   rule253 = \ ((aexprImExitId)) ((aselsImExitId)) ->
     aexprImExitId <> aselsImExitId
   rule254 = \ ((aexprIppAgs)) ((aselsIppAgs)) ->
     aexprIppAgs ++ aselsIppAgs
   rule255 = \ ((aexprIppDebugs)) ((aselsIppDebugs)) ->
     aexprIppDebugs ++ aselsIppDebugs
   rule256 = \ ((aexprIrecNode)) ((aselsIrecNode)) ->
     aexprIrecNode || aselsIrecNode
   rule257 = \ ((aexprIcopy)) ((aselsIcopy)) skind_ ->
     Selection skind_ aexprIcopy aselsIcopy
   rule258 = \ lcopy ->
     lcopy
   rule259 = \ ((aselsIgraph)) ->
     aselsIgraph
   rule260 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule261 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule262 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule263 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule264 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule265 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule266 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule267 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule268 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule269 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Update  :: (T_Expression ) (T_Selections ) (T_Expression ) -> T_Expression 
sem_Expression_Update arg_exprl_ arg_sels_ arg_exprr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprlX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprl_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprrX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprr_))
                           (T_Expression_vOut13 aexprlIcopy aexprlIgraph aexprlIhasRecs aexprlImEntryId aexprlImExitId aexprlIppAg aexprlIppAgs aexprlIppDebug aexprlIppDebugs aexprlIrecNode) = inv_Expression_s14 st_exprlX14 (T_Expression_vIn13 aexprlOcaseExpr aexprlOcurrTaskName aexprlOgraph aexprlOmergeId aexprlOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprrIcopy aexprrIgraph aexprrIhasRecs aexprrImEntryId aexprrImExitId aexprrIppAg aexprrIppAgs aexprrIppDebug aexprrIppDebugs aexprrIrecNode) = inv_Expression_s14 st_exprrX14 (T_Expression_vIn13 aexprrOcaseExpr aexprrOcurrTaskName aexprrOgraph aexprrOmergeId aexprrOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule270  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule271  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule272 aexprlIhasRecs aexprrIhasRecs aselsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule273 aexprlImEntryId aexprrImEntryId aselsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule274 aexprlImExitId aexprrImExitId aselsImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule275 aexprlIppAgs aexprrIppAgs aselsIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule276 aexprlIppDebugs aexprrIppDebugs aselsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule277 aexprlIrecNode aexprrIrecNode aselsIrecNode
                           lcopy = rule278 aexprlIcopy aexprrIcopy aselsIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule279 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule280 aexprrIgraph
                           aexprlOcaseExpr = rule281 alhsIcaseExpr
                           aexprlOcurrTaskName = rule282 alhsIcurrTaskName
                           aexprlOgraph = rule283 alhsIgraph
                           aexprlOmergeId = rule284 alhsImergeId
                           aexprlOmoduleEnv = rule285 alhsImoduleEnv
                           aselsOcaseExpr = rule286 alhsIcaseExpr
                           aselsOcurrTaskName = rule287 alhsIcurrTaskName
                           aselsOgraph = rule288 aexprlIgraph
                           aselsOmergeId = rule289 alhsImergeId
                           aselsOmoduleEnv = rule290 alhsImoduleEnv
                           aexprrOcaseExpr = rule291 alhsIcaseExpr
                           aexprrOcurrTaskName = rule292 alhsIcurrTaskName
                           aexprrOgraph = rule293 aselsIgraph
                           aexprrOmergeId = rule294 alhsImergeId
                           aexprrOmoduleEnv = rule295 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 88 "./frontend/Tonic/Pretty.ag" #*/
   rule270 = \  (_) ->
                      /*# LINE 88 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1967 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 89 "./frontend/Tonic/Pretty.ag" #*/
   rule271 = \  (_) ->
                      /*# LINE 89 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1972 "frontend/Tonic/Tonic.icl"#*/
   rule272 = \ ((aexprlIhasRecs)) ((aexprrIhasRecs)) ((aselsIhasRecs)) ->
     aexprlIhasRecs || aselsIhasRecs || aexprrIhasRecs
   rule273 = \ ((aexprlImEntryId)) ((aexprrImEntryId)) ((aselsImEntryId)) ->
     aexprlImEntryId <> aselsImEntryId <> aexprrImEntryId
   rule274 = \ ((aexprlImExitId)) ((aexprrImExitId)) ((aselsImExitId)) ->
     aexprlImExitId <> aselsImExitId <> aexprrImExitId
   rule275 = \ ((aexprlIppAgs)) ((aexprrIppAgs)) ((aselsIppAgs)) ->
     aexprlIppAgs ++ aselsIppAgs ++ aexprrIppAgs
   rule276 = \ ((aexprlIppDebugs)) ((aexprrIppDebugs)) ((aselsIppDebugs)) ->
     aexprlIppDebugs ++ aselsIppDebugs ++ aexprrIppDebugs
   rule277 = \ ((aexprlIrecNode)) ((aexprrIrecNode)) ((aselsIrecNode)) ->
     aexprlIrecNode || aselsIrecNode || aexprrIrecNode
   rule278 = \ ((aexprlIcopy)) ((aexprrIcopy)) ((aselsIcopy)) ->
     Update aexprlIcopy aselsIcopy aexprrIcopy
   rule279 = \ lcopy ->
     lcopy
   rule280 = \ ((aexprrIgraph)) ->
     aexprrIgraph
   rule281 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule282 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule283 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule284 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule285 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule286 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule287 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule288 = \ ((aexprlIgraph)) ->
     aexprlIgraph
   rule289 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule290 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule291 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule292 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule293 = \ ((aselsIgraph)) ->
     aselsIgraph
   rule294 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule295 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_RecordUpdate  :: (T_GlobalDefinedSymbol ) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate arg_gdsym_ arg_expr_ arg_binds_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_gdsymX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdsym_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut40 agdsymIcopy agdsymIgraph agdsymIhasRecs agdsymImEntryId agdsymImExitId agdsymIppAg agdsymIppAgs agdsymIppDebug agdsymIppDebugs agdsymIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsymX41 (T_GlobalDefinedSymbol_vIn40 agdsymOcaseExpr agdsymOcurrTaskName agdsymOgraph agdsymOmergeId agdsymOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule296  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule297  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule298 aexprIhasRecs agdsymIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule299 aexprImEntryId agdsymImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule300 aexprImExitId agdsymImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule301 aexprIppAgs agdsymIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule302 aexprIppDebugs agdsymIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule303 aexprIrecNode agdsymIrecNode
                           lcopy = rule304 aexprIcopy agdsymIcopy arg_binds_
                           alhsOcopy :: Expression
                           alhsOcopy = rule305 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule306 aexprIgraph
                           agdsymOcaseExpr = rule307 alhsIcaseExpr
                           agdsymOcurrTaskName = rule308 alhsIcurrTaskName
                           agdsymOgraph = rule309 alhsIgraph
                           agdsymOmergeId = rule310 alhsImergeId
                           agdsymOmoduleEnv = rule311 alhsImoduleEnv
                           aexprOcaseExpr = rule312 alhsIcaseExpr
                           aexprOcurrTaskName = rule313 alhsIcurrTaskName
                           aexprOgraph = rule314 agdsymIgraph
                           aexprOmergeId = rule315 alhsImergeId
                           aexprOmoduleEnv = rule316 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 92 "./frontend/Tonic/Pretty.ag" #*/
   rule296 = \  (_) ->
                      /*# LINE 92 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 2070 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 93 "./frontend/Tonic/Pretty.ag" #*/
   rule297 = \  (_) ->
                      /*# LINE 93 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 2075 "frontend/Tonic/Tonic.icl"#*/
   rule298 = \ ((aexprIhasRecs)) ((agdsymIhasRecs)) ->
     agdsymIhasRecs || aexprIhasRecs
   rule299 = \ ((aexprImEntryId)) ((agdsymImEntryId)) ->
     agdsymImEntryId <> aexprImEntryId
   rule300 = \ ((aexprImExitId)) ((agdsymImExitId)) ->
     agdsymImExitId <> aexprImExitId
   rule301 = \ ((aexprIppAgs)) ((agdsymIppAgs)) ->
     agdsymIppAgs ++ aexprIppAgs
   rule302 = \ ((aexprIppDebugs)) ((agdsymIppDebugs)) ->
     agdsymIppDebugs ++ aexprIppDebugs
   rule303 = \ ((aexprIrecNode)) ((agdsymIrecNode)) ->
     agdsymIrecNode || aexprIrecNode
   rule304 = \ ((aexprIcopy)) ((agdsymIcopy)) binds_ ->
     RecordUpdate agdsymIcopy aexprIcopy binds_
   rule305 = \ lcopy ->
     lcopy
   rule306 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule307 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule308 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule309 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule310 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule311 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule312 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule313 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule314 = \ ((agdsymIgraph)) ->
     agdsymIgraph
   rule315 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule316 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_TupleSelect  :: (T_DefinedSymbol ) (Int) (T_Expression ) -> T_Expression 
sem_Expression_TupleSelect arg_dsym_ arg_n_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_dsymX11 = 'Control.Monad.Identity'.runIdentity (attach_T_DefinedSymbol (arg_dsym_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_DefinedSymbol_vOut10 adsymIcopy adsymIgraph adsymIhasRecs adsymImEntryId adsymImExitId adsymIppAg adsymIppAgs adsymIppDebug adsymIppDebugs adsymIrecNode) = inv_DefinedSymbol_s11 st_dsymX11 (T_DefinedSymbol_vIn10 adsymOcaseExpr adsymOcurrTaskName adsymOgraph adsymOmergeId adsymOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule317  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule318  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule319 adsymIhasRecs aexprIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule320 adsymImEntryId aexprImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule321 adsymImExitId aexprImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule322 adsymIppAgs aexprIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule323 adsymIppDebugs aexprIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule324 adsymIrecNode aexprIrecNode
                           lcopy = rule325 adsymIcopy aexprIcopy arg_n_
                           alhsOcopy :: Expression
                           alhsOcopy = rule326 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule327 aexprIgraph
                           adsymOcaseExpr = rule328 alhsIcaseExpr
                           adsymOcurrTaskName = rule329 alhsIcurrTaskName
                           adsymOgraph = rule330 alhsIgraph
                           adsymOmergeId = rule331 alhsImergeId
                           adsymOmoduleEnv = rule332 alhsImoduleEnv
                           aexprOcaseExpr = rule333 alhsIcaseExpr
                           aexprOcurrTaskName = rule334 alhsIcurrTaskName
                           aexprOgraph = rule335 adsymIgraph
                           aexprOmergeId = rule336 alhsImergeId
                           aexprOmoduleEnv = rule337 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 96 "./frontend/Tonic/Pretty.ag" #*/
   rule317 = \  (_) ->
                      /*# LINE 96 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 2163 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 97 "./frontend/Tonic/Pretty.ag" #*/
   rule318 = \  (_) ->
                      /*# LINE 97 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 2168 "frontend/Tonic/Tonic.icl"#*/
   rule319 = \ ((adsymIhasRecs)) ((aexprIhasRecs)) ->
     adsymIhasRecs || aexprIhasRecs
   rule320 = \ ((adsymImEntryId)) ((aexprImEntryId)) ->
     adsymImEntryId <> aexprImEntryId
   rule321 = \ ((adsymImExitId)) ((aexprImExitId)) ->
     adsymImExitId <> aexprImExitId
   rule322 = \ ((adsymIppAgs)) ((aexprIppAgs)) ->
     adsymIppAgs ++ aexprIppAgs
   rule323 = \ ((adsymIppDebugs)) ((aexprIppDebugs)) ->
     adsymIppDebugs ++ aexprIppDebugs
   rule324 = \ ((adsymIrecNode)) ((aexprIrecNode)) ->
     adsymIrecNode || aexprIrecNode
   rule325 = \ ((adsymIcopy)) ((aexprIcopy)) n_ ->
     TupleSelect adsymIcopy n_ aexprIcopy
   rule326 = \ lcopy ->
     lcopy
   rule327 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule328 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule329 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule330 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule331 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule332 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule333 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule334 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule335 = \ ((adsymIgraph)) ->
     adsymIgraph
   rule336 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule337 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_BasicExpr  :: (T_BasicValue ) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_bvX5 = 'Control.Monad.Identity'.runIdentity (attach_T_BasicValue (arg_bv_))
                           (T_BasicValue_vOut4 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BasicValue_s5 st_bvX5 (T_BasicValue_vIn4 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule338 abvIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule339 abvIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule340 abvIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule341 abvImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule342 abvImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule343 abvIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule344 abvIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule345 abvIrecNode
                           lcopy = rule346 abvIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule347 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule348 abvIgraph
                           abvOcaseExpr = rule349 alhsIcaseExpr
                           abvOcurrTaskName = rule350 alhsIcurrTaskName
                           abvOgraph = rule351 alhsIgraph
                           abvOmergeId = rule352 alhsImergeId
                           abvOmoduleEnv = rule353 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   /*# LINE 100 "./frontend/Tonic/Pretty.ag" #*/
   rule338 = \ ((abvIppDebug)) ->
                      /*# LINE 100 "./frontend/Tonic/Pretty.ag" #*/
                      text "<BasicValue>" <+> abvIppDebug
                      /*# LINE 2249 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 101 "./frontend/Tonic/Pretty.ag" #*/
   rule339 = \ ((abvIppAg)) ->
                      /*# LINE 101 "./frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 2254 "frontend/Tonic/Tonic.icl"#*/
   rule340 = \ ((abvIhasRecs)) ->
     abvIhasRecs
   rule341 = \ ((abvImEntryId)) ->
     abvImEntryId
   rule342 = \ ((abvImExitId)) ->
     abvImExitId
   rule343 = \ ((abvIppAgs)) ->
     abvIppAgs
   rule344 = \ ((abvIppDebugs)) ->
     abvIppDebugs
   rule345 = \ ((abvIrecNode)) ->
     abvIrecNode
   rule346 = \ ((abvIcopy)) ->
     BasicExpr abvIcopy
   rule347 = \ lcopy ->
     lcopy
   rule348 = \ ((abvIgraph)) ->
     abvIgraph
   rule349 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule350 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule351 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule352 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule353 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_Conditional arg_cond_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule354  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule355  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule356  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule357  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule358  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule359  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule360  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule361  Void
                           lcopy = rule362 arg_cond_
                           alhsOcopy :: Expression
                           alhsOcopy = rule363 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule364 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule354 = \  (_) ->
     False
   rule355 = \  (_) ->
     Nothing
   rule356 = \  (_) ->
     Nothing
   rule357 = \  (_) ->
     empty
   rule358 = \  (_) ->
     []
   rule359 = \  (_) ->
     empty
   rule360 = \  (_) ->
     []
   rule361 = \  (_) ->
     False
   rule362 = \ cond_ ->
     Conditional cond_
   rule363 = \ lcopy ->
     lcopy
   rule364 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr arg_cbbv_ arg_cbfv_ arg_ss_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule365  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule366  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule367  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule368  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule369  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule370  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule371  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule372  Void
                           lcopy = rule373 arg_cbbv_ arg_cbfv_ arg_ss_
                           alhsOcopy :: Expression
                           alhsOcopy = rule374 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule375 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule365 = \  (_) ->
     False
   rule366 = \  (_) ->
     Nothing
   rule367 = \  (_) ->
     Nothing
   rule368 = \  (_) ->
     empty
   rule369 = \  (_) ->
     []
   rule370 = \  (_) ->
     empty
   rule371 = \  (_) ->
     []
   rule372 = \  (_) ->
     False
   rule373 = \ cbbv_ cbfv_ ss_ ->
     AnyCodeExpr cbbv_ cbfv_ ss_
   rule374 = \ lcopy ->
     lcopy
   rule375 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr arg_ss_ arg_bl_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule376  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule377  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule378  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule379  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule380  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule381  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule382  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule383  Void
                           lcopy = rule384 arg_bl_ arg_ss_
                           alhsOcopy :: Expression
                           alhsOcopy = rule385 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule386 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule376 = \  (_) ->
     False
   rule377 = \  (_) ->
     Nothing
   rule378 = \  (_) ->
     Nothing
   rule379 = \  (_) ->
     empty
   rule380 = \  (_) ->
     []
   rule381 = \  (_) ->
     empty
   rule382 = \  (_) ->
     []
   rule383 = \  (_) ->
     False
   rule384 = \ bl_ ss_ ->
     ABCCodeExpr ss_ bl_
   rule385 = \ lcopy ->
     lcopy
   rule386 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr arg_gdfs_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule387 aexprIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule388 aexprImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule389 aexprImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule390 aexprIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule391 aexprIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule392 aexprIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule393 aexprIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule394 aexprIrecNode
                           lcopy = rule395 aexprIcopy arg_gdfs_
                           alhsOcopy :: Expression
                           alhsOcopy = rule396 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule397 aexprIgraph
                           aexprOcaseExpr = rule398 alhsIcaseExpr
                           aexprOcurrTaskName = rule399 alhsIcurrTaskName
                           aexprOgraph = rule400 alhsIgraph
                           aexprOmergeId = rule401 alhsImergeId
                           aexprOmoduleEnv = rule402 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule387 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule388 = \ ((aexprImEntryId)) ->
     aexprImEntryId
   rule389 = \ ((aexprImExitId)) ->
     aexprImExitId
   rule390 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule391 = \ ((aexprIppAgs)) ->
     aexprIppAgs
   rule392 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule393 = \ ((aexprIppDebugs)) ->
     aexprIppDebugs
   rule394 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule395 = \ ((aexprIcopy)) gdfs_ ->
     MatchExpr gdfs_ aexprIcopy
   rule396 = \ lcopy ->
     lcopy
   rule397 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule398 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule399 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule400 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule401 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule402 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_IsConstructor  :: (T_Expression ) (T_GlobalDefinedSymbol ) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ arg_gdfs_ arg_arity_ arg_gidx_ arg_ident_ arg_pos_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_gdfsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdfs_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_GlobalDefinedSymbol_vOut40 agdfsIcopy agdfsIgraph agdfsIhasRecs agdfsImEntryId agdfsImExitId agdfsIppAg agdfsIppAgs agdfsIppDebug agdfsIppDebugs agdfsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdfsX41 (T_GlobalDefinedSymbol_vIn40 agdfsOcaseExpr agdfsOcurrTaskName agdfsOgraph agdfsOmergeId agdfsOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule403 aexprIhasRecs agdfsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule404 aexprImEntryId agdfsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule405 aexprImExitId agdfsImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule406 aexprIppAg agdfsIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule407 aexprIppAgs agdfsIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule408 aexprIppDebug agdfsIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule409 aexprIppDebugs agdfsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule410 aexprIrecNode agdfsIrecNode
                           lcopy = rule411 aexprIcopy agdfsIcopy arg_arity_ arg_gidx_ arg_ident_ arg_pos_
                           alhsOcopy :: Expression
                           alhsOcopy = rule412 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule413 agdfsIgraph
                           aexprOcaseExpr = rule414 alhsIcaseExpr
                           aexprOcurrTaskName = rule415 alhsIcurrTaskName
                           aexprOgraph = rule416 alhsIgraph
                           aexprOmergeId = rule417 alhsImergeId
                           aexprOmoduleEnv = rule418 alhsImoduleEnv
                           agdfsOcaseExpr = rule419 alhsIcaseExpr
                           agdfsOcurrTaskName = rule420 alhsIcurrTaskName
                           agdfsOgraph = rule421 aexprIgraph
                           agdfsOmergeId = rule422 alhsImergeId
                           agdfsOmoduleEnv = rule423 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule403 = \ ((aexprIhasRecs)) ((agdfsIhasRecs)) ->
     aexprIhasRecs || agdfsIhasRecs
   rule404 = \ ((aexprImEntryId)) ((agdfsImEntryId)) ->
     aexprImEntryId <> agdfsImEntryId
   rule405 = \ ((aexprImExitId)) ((agdfsImExitId)) ->
     aexprImExitId <> agdfsImExitId
   rule406 = \ ((aexprIppAg)) ((agdfsIppAg)) ->
     aexprIppAg <$$> agdfsIppAg
   rule407 = \ ((aexprIppAgs)) ((agdfsIppAgs)) ->
     aexprIppAgs ++ agdfsIppAgs
   rule408 = \ ((aexprIppDebug)) ((agdfsIppDebug)) ->
     aexprIppDebug <$$> agdfsIppDebug
   rule409 = \ ((aexprIppDebugs)) ((agdfsIppDebugs)) ->
     aexprIppDebugs ++ agdfsIppDebugs
   rule410 = \ ((aexprIrecNode)) ((agdfsIrecNode)) ->
     aexprIrecNode || agdfsIrecNode
   rule411 = \ ((aexprIcopy)) ((agdfsIcopy)) arity_ gidx_ ident_ pos_ ->
     IsConstructor aexprIcopy agdfsIcopy arity_ gidx_ ident_ pos_
   rule412 = \ lcopy ->
     lcopy
   rule413 = \ ((agdfsIgraph)) ->
     agdfsIgraph
   rule414 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule415 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule416 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule417 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule418 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule419 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule420 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule421 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule422 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule423 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_FreeVar  :: (T_FreeVar ) -> T_Expression 
sem_Expression_FreeVar arg_fv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_fvX20 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVar (arg_fv_))
                           (T_FreeVar_vOut19 afvIcopy afvIgraph afvIhasRecs afvImEntryId afvImExitId afvIppAg afvIppAgs afvIppDebug afvIppDebugs afvIrecNode) = inv_FreeVar_s20 st_fvX20 (T_FreeVar_vIn19 afvOcaseExpr afvOcurrTaskName afvOgraph afvOmergeId afvOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule424 afvIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule425 afvImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule426 afvImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule427 afvIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule428 afvIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule429 afvIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule430 afvIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule431 afvIrecNode
                           lcopy = rule432 afvIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule433 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule434 afvIgraph
                           afvOcaseExpr = rule435 alhsIcaseExpr
                           afvOcurrTaskName = rule436 alhsIcurrTaskName
                           afvOgraph = rule437 alhsIgraph
                           afvOmergeId = rule438 alhsImergeId
                           afvOmoduleEnv = rule439 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule424 = \ ((afvIhasRecs)) ->
     afvIhasRecs
   rule425 = \ ((afvImEntryId)) ->
     afvImEntryId
   rule426 = \ ((afvImExitId)) ->
     afvImExitId
   rule427 = \ ((afvIppAg)) ->
     afvIppAg
   rule428 = \ ((afvIppAgs)) ->
     afvIppAgs
   rule429 = \ ((afvIppDebug)) ->
     afvIppDebug
   rule430 = \ ((afvIppDebugs)) ->
     afvIppDebugs
   rule431 = \ ((afvIrecNode)) ->
     afvIrecNode
   rule432 = \ ((afvIcopy)) ->
     FreeVar afvIcopy
   rule433 = \ lcopy ->
     lcopy
   rule434 = \ ((afvIgraph)) ->
     afvIgraph
   rule435 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule436 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule437 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule438 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule439 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction arg_fvat_ arg_expr_ arg_aty_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule440 aexprIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule441 aexprImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule442 aexprImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule443 aexprIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule444 aexprIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule445 aexprIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule446 aexprIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule447 aexprIrecNode
                           lcopy = rule448 aexprIcopy arg_aty_ arg_fvat_
                           alhsOcopy :: Expression
                           alhsOcopy = rule449 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule450 aexprIgraph
                           aexprOcaseExpr = rule451 alhsIcaseExpr
                           aexprOcurrTaskName = rule452 alhsIcurrTaskName
                           aexprOgraph = rule453 alhsIgraph
                           aexprOmergeId = rule454 alhsImergeId
                           aexprOmoduleEnv = rule455 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule440 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule441 = \ ((aexprImEntryId)) ->
     aexprImEntryId
   rule442 = \ ((aexprImExitId)) ->
     aexprImExitId
   rule443 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule444 = \ ((aexprIppAgs)) ->
     aexprIppAgs
   rule445 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule446 = \ ((aexprIppDebugs)) ->
     aexprIppDebugs
   rule447 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule448 = \ ((aexprIcopy)) aty_ fvat_ ->
     DictionariesFunction fvat_ aexprIcopy aty_
   rule449 = \ lcopy ->
     lcopy
   rule450 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule451 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule452 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule453 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule454 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule455 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Constant  :: (T_SymbIdent ) (Int) (Priority) -> T_Expression 
sem_Expression_Constant arg_symid_ arg_n_ arg_prio_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_symidX53 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_symid_))
                           (T_SymbIdent_vOut52 asymidIcopy asymidIgraph asymidIhasRecs asymidIident asymidIisCurrTask asymidIisInfix asymidImEntryId asymidImExitId asymidImFunDef asymidImSymbolType asymidIppAg asymidIppAgs asymidIppDebug asymidIppDebugs asymidIrecNode) = inv_SymbIdent_s53 st_symidX53 (T_SymbIdent_vIn52 asymidOcaseExpr asymidOcurrTaskName asymidOgraph asymidOmergeId asymidOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule456 asymidIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule457 asymidImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule458 asymidImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule459 asymidIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule460 asymidIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule461 asymidIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule462 asymidIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule463 asymidIrecNode
                           lcopy = rule464 asymidIcopy arg_n_ arg_prio_
                           alhsOcopy :: Expression
                           alhsOcopy = rule465 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule466 asymidIgraph
                           asymidOcaseExpr = rule467 alhsIcaseExpr
                           asymidOcurrTaskName = rule468 alhsIcurrTaskName
                           asymidOgraph = rule469 alhsIgraph
                           asymidOmergeId = rule470 alhsImergeId
                           asymidOmoduleEnv = rule471 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule456 = \ ((asymidIhasRecs)) ->
     asymidIhasRecs
   rule457 = \ ((asymidImEntryId)) ->
     asymidImEntryId
   rule458 = \ ((asymidImExitId)) ->
     asymidImExitId
   rule459 = \ ((asymidIppAg)) ->
     asymidIppAg
   rule460 = \ ((asymidIppAgs)) ->
     asymidIppAgs
   rule461 = \ ((asymidIppDebug)) ->
     asymidIppDebug
   rule462 = \ ((asymidIppDebugs)) ->
     asymidIppDebugs
   rule463 = \ ((asymidIrecNode)) ->
     asymidIrecNode
   rule464 = \ ((asymidIcopy)) n_ prio_ ->
     Constant asymidIcopy n_ prio_
   rule465 = \ lcopy ->
     lcopy
   rule466 = \ ((asymidIgraph)) ->
     asymidIgraph
   rule467 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule468 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule469 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule470 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule471 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable arg_varinfptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule472  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule473  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule474  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule475  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule476  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule477  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule478  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule479  Void
                           lcopy = rule480 arg_varinfptr_
                           alhsOcopy :: Expression
                           alhsOcopy = rule481 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule482 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule472 = \  (_) ->
     False
   rule473 = \  (_) ->
     Nothing
   rule474 = \  (_) ->
     Nothing
   rule475 = \  (_) ->
     empty
   rule476 = \  (_) ->
     []
   rule477 = \  (_) ->
     empty
   rule478 = \  (_) ->
     []
   rule479 = \  (_) ->
     False
   rule480 = \ varinfptr_ ->
     ClassVariable varinfptr_
   rule481 = \ lcopy ->
     lcopy
   rule482 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr arg_dynexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule483  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule484  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule485  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule486  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule487  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule488  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule489  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule490  Void
                           lcopy = rule491 arg_dynexpr_
                           alhsOcopy :: Expression
                           alhsOcopy = rule492 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule493 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule483 = \  (_) ->
     False
   rule484 = \  (_) ->
     Nothing
   rule485 = \  (_) ->
     Nothing
   rule486 = \  (_) ->
     empty
   rule487 = \  (_) ->
     []
   rule488 = \  (_) ->
     empty
   rule489 = \  (_) ->
     []
   rule490 = \  (_) ->
     False
   rule491 = \ dynexpr_ ->
     DynamicExpr dynexpr_
   rule492 = \ lcopy ->
     lcopy
   rule493 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression arg_tycodeexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule494  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule495  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule496  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule497  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule498  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule499  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule500  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule501  Void
                           lcopy = rule502 arg_tycodeexpr_
                           alhsOcopy :: Expression
                           alhsOcopy = rule503 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule504 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule494 = \  (_) ->
     False
   rule495 = \  (_) ->
     Nothing
   rule496 = \  (_) ->
     Nothing
   rule497 = \  (_) ->
     empty
   rule498 = \  (_) ->
     []
   rule499 = \  (_) ->
     empty
   rule500 = \  (_) ->
     []
   rule501 = \  (_) ->
     False
   rule502 = \ tycodeexpr_ ->
     TypeCodeExpression tycodeexpr_
   rule503 = \ lcopy ->
     lcopy
   rule504 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature arg_sigfun_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule505 aexprIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule506 aexprImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule507 aexprImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule508 aexprIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule509 aexprIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule510 aexprIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule511 aexprIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule512 aexprIrecNode
                           lcopy = rule513 aexprIcopy arg_sigfun_
                           alhsOcopy :: Expression
                           alhsOcopy = rule514 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule515 aexprIgraph
                           aexprOcaseExpr = rule516 alhsIcaseExpr
                           aexprOcurrTaskName = rule517 alhsIcurrTaskName
                           aexprOgraph = rule518 alhsIgraph
                           aexprOmergeId = rule519 alhsImergeId
                           aexprOmoduleEnv = rule520 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule505 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule506 = \ ((aexprImEntryId)) ->
     aexprImEntryId
   rule507 = \ ((aexprImExitId)) ->
     aexprImExitId
   rule508 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule509 = \ ((aexprIppAgs)) ->
     aexprIppAgs
   rule510 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule511 = \ ((aexprIppDebugs)) ->
     aexprIppDebugs
   rule512 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule513 = \ ((aexprIcopy)) sigfun_ ->
     TypeSignature sigfun_ aexprIcopy
   rule514 = \ lcopy ->
     lcopy
   rule515 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule516 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule517 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule518 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule519 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule520 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_EE  ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule521  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule522  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule523  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule524  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule525  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule526  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule527  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule528  Void
                           lcopy = rule529  Void
                           alhsOcopy :: Expression
                           alhsOcopy = rule530 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule531 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule521 = \  (_) ->
     False
   rule522 = \  (_) ->
     Nothing
   rule523 = \  (_) ->
     Nothing
   rule524 = \  (_) ->
     empty
   rule525 = \  (_) ->
     []
   rule526 = \  (_) ->
     empty
   rule527 = \  (_) ->
     []
   rule528 = \  (_) ->
     False
   rule529 = \  (_) ->
     EE
   rule530 = \ lcopy ->
     lcopy
   rule531 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind arg_exprinfoptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule532  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule533  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule534  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule535  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule536  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule537  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule538  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule539  Void
                           lcopy = rule540 arg_exprinfoptr_
                           alhsOcopy :: Expression
                           alhsOcopy = rule541 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule542 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule532 = \  (_) ->
     False
   rule533 = \  (_) ->
     Nothing
   rule534 = \  (_) ->
     Nothing
   rule535 = \  (_) ->
     empty
   rule536 = \  (_) ->
     []
   rule537 = \  (_) ->
     empty
   rule538 = \  (_) ->
     []
   rule539 = \  (_) ->
     False
   rule540 = \ exprinfoptr_ ->
     NoBind exprinfoptr_
   rule541 = \ lcopy ->
     lcopy
   rule542 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_FailExpr  :: (T_Ident ) -> T_Expression 
sem_Expression_FailExpr arg_ident_ = T_Expression (lift st14) where
   st14 =
         let
             v13 :: T_Expression_v13 
             v13 = \ (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ident_))
                           (T_Ident_vOut43 aidentIcopy aidentIgraph aidentIhasRecs aidentIident aidentImEntryId aidentImExitId aidentIppAg aidentIppAgs aidentIppDebug aidentIppDebugs aidentIrecNode) = inv_Ident_s44 st_identX44 (T_Ident_vIn43 aidentOcaseExpr aidentOcurrTaskName aidentOgraph aidentOmergeId aidentOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule543 aidentIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule544 aidentImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule545 aidentImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule546 aidentIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule547 aidentIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule548 aidentIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule549 aidentIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule550 aidentIrecNode
                           lcopy = rule551 aidentIcopy
                           alhsOcopy :: Expression
                           alhsOcopy = rule552 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule553 aidentIgraph
                           aidentOcaseExpr = rule554 alhsIcaseExpr
                           aidentOcurrTaskName = rule555 alhsIcurrTaskName
                           aidentOgraph = rule556 alhsIgraph
                           aidentOmergeId = rule557 alhsImergeId
                           aidentOmoduleEnv = rule558 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expression_s14 v13
   rule543 = \ ((aidentIhasRecs)) ->
     aidentIhasRecs
   rule544 = \ ((aidentImEntryId)) ->
     aidentImEntryId
   rule545 = \ ((aidentImExitId)) ->
     aidentImExitId
   rule546 = \ ((aidentIppAg)) ->
     aidentIppAg
   rule547 = \ ((aidentIppAgs)) ->
     aidentIppAgs
   rule548 = \ ((aidentIppDebug)) ->
     aidentIppDebug
   rule549 = \ ((aidentIppDebugs)) ->
     aidentIppDebugs
   rule550 = \ ((aidentIrecNode)) ->
     aidentIrecNode
   rule551 = \ ((aidentIcopy)) ->
     FailExpr aidentIcopy
   rule552 = \ lcopy ->
     lcopy
   rule553 = \ ((aidentIgraph)) ->
     aidentIgraph
   rule554 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule555 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule556 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule557 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule558 = \ ((alhsImoduleEnv)) ->
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
             v16 :: T_Expressions_v16 
             v16 = \ (T_Expressions_vIn16 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_hdX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_hd_))
                           st_tlX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_tl_))
                           (T_Expression_vOut13 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Expression_s14 st_hdX14 (T_Expression_vIn13 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Expressions_vOut16 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_Expressions_s17 st_tlX17 (T_Expressions_vIn16 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule559 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule560 ahdImEntryId atlImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule561 ahdImExitId atlImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule562 ahdIppAg atlIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule563 ahdIppAgs atlIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule564 ahdIppDebug atlIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule565 ahdIppDebugs atlIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule566 ahdIrecNode atlIrecNode
                           lcopy = rule567 ahdIcopy atlIcopy
                           alhsOcopy :: Expressions
                           alhsOcopy = rule568 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule569 atlIgraph
                           ahdOcaseExpr = rule570 alhsIcaseExpr
                           ahdOcurrTaskName = rule571 alhsIcurrTaskName
                           ahdOgraph = rule572 alhsIgraph
                           ahdOmergeId = rule573 alhsImergeId
                           ahdOmoduleEnv = rule574 alhsImoduleEnv
                           atlOcaseExpr = rule575 alhsIcaseExpr
                           atlOcurrTaskName = rule576 alhsIcurrTaskName
                           atlOgraph = rule577 ahdIgraph
                           atlOmergeId = rule578 alhsImergeId
                           atlOmoduleEnv = rule579 alhsImoduleEnv
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expressions_s17 v16
   rule559 = \ ((ahdIhasRecs)) ((atlIhasRecs)) ->
     ahdIhasRecs || atlIhasRecs
   rule560 = \ ((ahdImEntryId)) ((atlImEntryId)) ->
     ahdImEntryId <> atlImEntryId
   rule561 = \ ((ahdImExitId)) ((atlImExitId)) ->
     ahdImExitId <> atlImExitId
   rule562 = \ ((ahdIppAg)) ((atlIppAg)) ->
     ahdIppAg <$$> atlIppAg
   rule563 = \ ((ahdIppAgs)) ((atlIppAgs)) ->
     ahdIppAgs ++ atlIppAgs
   rule564 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug <$$> atlIppDebug
   rule565 = \ ((ahdIppDebugs)) ((atlIppDebugs)) ->
     ahdIppDebugs ++ atlIppDebugs
   rule566 = \ ((ahdIrecNode)) ((atlIrecNode)) ->
     ahdIrecNode || atlIrecNode
   rule567 = \ ((ahdIcopy)) ((atlIcopy)) ->
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule568 = \ lcopy ->
     lcopy
   rule569 = \ ((atlIgraph)) ->
     atlIgraph
   rule570 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule571 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule572 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule573 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule574 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule575 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule576 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule577 = \ ((ahdIgraph)) ->
     ahdIgraph
   rule578 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule579 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expressions_Nil  ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st17) where
   st17 =
         let
             v16 :: T_Expressions_v16 
             v16 = \ (T_Expressions_vIn16 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule580  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule581  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule582  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule583  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule584  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule585  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule586  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule587  Void
                           lcopy = rule588  Void
                           alhsOcopy :: Expressions
                           alhsOcopy = rule589 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule590 alhsIgraph
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Expressions_s17 v16
   rule580 = \  (_) ->
     False
   rule581 = \  (_) ->
     Nothing
   rule582 = \  (_) ->
     Nothing
   rule583 = \  (_) ->
     empty
   rule584 = \  (_) ->
     []
   rule585 = \  (_) ->
     empty
   rule586 = \  (_) ->
     []
   rule587 = \  (_) ->
     False
   rule588 = \  (_) ->
     []
   rule589 = \ lcopy ->
     lcopy
   rule590 = \ ((alhsIgraph)) ->
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
             v19 :: T_FreeVar_v19 
             v19 = \ (T_FreeVar_vIn19 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_fv_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_fv_ident_))
                           (T_Ident_vOut43 afv_identIcopy afv_identIgraph afv_identIhasRecs afv_identIident afv_identImEntryId afv_identImExitId afv_identIppAg afv_identIppAgs afv_identIppDebug afv_identIppDebugs afv_identIrecNode) = inv_Ident_s44 st_fv_identX44 (T_Ident_vIn43 afv_identOcaseExpr afv_identOcurrTaskName afv_identOgraph afv_identOmergeId afv_identOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule591 afv_identIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule592 afv_identIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule593 afv_identIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule594 afv_identImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule595 afv_identImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule596 afv_identIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule597 afv_identIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule598 afv_identIrecNode
                           lcopy = rule599 afv_identIcopy arg_fv_count_ arg_fv_def_level_ arg_fv_info_ptr_
                           alhsOcopy :: FreeVar
                           alhsOcopy = rule600 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule601 afv_identIgraph
                           afv_identOcaseExpr = rule602 alhsIcaseExpr
                           afv_identOcurrTaskName = rule603 alhsIcurrTaskName
                           afv_identOgraph = rule604 alhsIgraph
                           afv_identOmergeId = rule605 alhsImergeId
                           afv_identOmoduleEnv = rule606 alhsImoduleEnv
                           ag__result_ = T_FreeVar_vOut19 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_FreeVar_s20 v19
   /*# LINE 112 "./frontend/Tonic/Pretty.ag" #*/
   rule591 = \ ((afv_identIppDebug)) ->
                            /*# LINE 112 "./frontend/Tonic/Pretty.ag" #*/
                            afv_identIppDebug
                            /*# LINE 3494 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 113 "./frontend/Tonic/Pretty.ag" #*/
   rule592 = \ ((afv_identIppAg)) ->
                            /*# LINE 113 "./frontend/Tonic/Pretty.ag" #*/
                            afv_identIppAg
                            /*# LINE 3499 "frontend/Tonic/Tonic.icl"#*/
   rule593 = \ ((afv_identIhasRecs)) ->
     afv_identIhasRecs
   rule594 = \ ((afv_identImEntryId)) ->
     afv_identImEntryId
   rule595 = \ ((afv_identImExitId)) ->
     afv_identImExitId
   rule596 = \ ((afv_identIppAgs)) ->
     afv_identIppAgs
   rule597 = \ ((afv_identIppDebugs)) ->
     afv_identIppDebugs
   rule598 = \ ((afv_identIrecNode)) ->
     afv_identIrecNode
   rule599 = \ ((afv_identIcopy)) fv_count_ fv_def_level_ fv_info_ptr_ ->
     {FreeVar|fv_def_level = fv_def_level_ , fv_ident = afv_identIcopy , fv_info_ptr = fv_info_ptr_ , fv_count = fv_count_}
   rule600 = \ lcopy ->
     lcopy
   rule601 = \ ((afv_identIgraph)) ->
     afv_identIgraph
   rule602 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule603 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule604 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule605 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule606 = \ ((alhsImoduleEnv)) ->
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
             v22 :: T_FreeVars_v22 
             v22 = \ (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_hdX20 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVar (arg_hd_))
                           st_tlX23 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVars (arg_tl_))
                           (T_FreeVar_vOut19 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_FreeVar_s20 st_hdX20 (T_FreeVar_vIn19 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_FreeVars_vOut22 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIrecNode) = inv_FreeVars_s23 st_tlX23 (T_FreeVars_vIn22 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule607 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule608 ahdImEntryId atlImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule609 ahdImExitId atlImExitId
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule610 ahdIrecNode atlIrecNode
                           lcopy = rule611 ahdIcopy atlIcopy
                           alhsOcopy :: FreeVars
                           alhsOcopy = rule612 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule613 atlIgraph
                           ahdOcaseExpr = rule614 alhsIcaseExpr
                           ahdOcurrTaskName = rule615 alhsIcurrTaskName
                           ahdOgraph = rule616 alhsIgraph
                           ahdOmergeId = rule617 alhsImergeId
                           ahdOmoduleEnv = rule618 alhsImoduleEnv
                           atlOcaseExpr = rule619 alhsIcaseExpr
                           atlOcurrTaskName = rule620 alhsIcurrTaskName
                           atlOgraph = rule621 ahdIgraph
                           atlOmergeId = rule622 alhsImergeId
                           atlOmoduleEnv = rule623 alhsImoduleEnv
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_ )
         in C_FreeVars_s23 v22
   rule607 = \ ((ahdIhasRecs)) ((atlIhasRecs)) ->
     ahdIhasRecs || atlIhasRecs
   rule608 = \ ((ahdImEntryId)) ((atlImEntryId)) ->
     ahdImEntryId <> atlImEntryId
   rule609 = \ ((ahdImExitId)) ((atlImExitId)) ->
     ahdImExitId <> atlImExitId
   rule610 = \ ((ahdIrecNode)) ((atlIrecNode)) ->
     ahdIrecNode || atlIrecNode
   rule611 = \ ((ahdIcopy)) ((atlIcopy)) ->
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule612 = \ lcopy ->
     lcopy
   rule613 = \ ((atlIgraph)) ->
     atlIgraph
   rule614 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule615 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule616 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule617 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule618 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule619 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule620 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule621 = \ ((ahdIgraph)) ->
     ahdIgraph
   rule622 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule623 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_FreeVars_Nil  ::   T_FreeVars 
sem_FreeVars_Nil  = T_FreeVars (lift st23) where
   st23 =
         let
             v22 :: T_FreeVars_v22 
             v22 = \ (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule624  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule625  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule626  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule627  Void
                           lcopy = rule628  Void
                           alhsOcopy :: FreeVars
                           alhsOcopy = rule629 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule630 alhsIgraph
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_ )
         in C_FreeVars_s23 v22
   rule624 = \  (_) ->
     False
   rule625 = \  (_) ->
     Nothing
   rule626 = \  (_) ->
     Nothing
   rule627 = \  (_) ->
     False
   rule628 = \  (_) ->
     []
   rule629 = \ lcopy ->
     lcopy
   rule630 = \ ((alhsIgraph)) ->
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
             v25 :: T_GExpression_v25 
             v25 = \ (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule631  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule632  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule633  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule634  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule635  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule636  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule637  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule638  Void
                           lcopy = rule639  Void
                           alhsOcopy :: GExpression
                           alhsOcopy = rule640 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule641 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GExpression_s26 v25
   /*# LINE 146 "./frontend/Tonic/Pretty.ag" #*/
   rule631 = \  (_) ->
                                          /*# LINE 146 "./frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3764 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 147 "./frontend/Tonic/Pretty.ag" #*/
   rule632 = \  (_) ->
                                          /*# LINE 147 "./frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3769 "frontend/Tonic/Tonic.icl"#*/
   rule633 = \  (_) ->
     False
   rule634 = \  (_) ->
     Nothing
   rule635 = \  (_) ->
     Nothing
   rule636 = \  (_) ->
     []
   rule637 = \  (_) ->
     []
   rule638 = \  (_) ->
     False
   rule639 = \  (_) ->
     GUndefinedExpression
   rule640 = \ lcopy ->
     lcopy
   rule641 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_GExpression_GGraphExpression  :: (GGraph) -> T_GExpression 
sem_GExpression_GGraphExpression arg_gg_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 :: T_GExpression_v25 
             v25 = \ (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule642  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule643  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule644  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule645  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule646  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule647  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule648  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule649  Void
                           lcopy = rule650 arg_gg_
                           alhsOcopy :: GExpression
                           alhsOcopy = rule651 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule652 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GExpression_s26 v25
   /*# LINE 148 "./frontend/Tonic/Pretty.ag" #*/
   rule642 = \  (_) ->
                                          /*# LINE 148 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3823 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 149 "./frontend/Tonic/Pretty.ag" #*/
   rule643 = \  (_) ->
                                          /*# LINE 149 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3828 "frontend/Tonic/Tonic.icl"#*/
   rule644 = \  (_) ->
     False
   rule645 = \  (_) ->
     Nothing
   rule646 = \  (_) ->
     Nothing
   rule647 = \  (_) ->
     []
   rule648 = \  (_) ->
     []
   rule649 = \  (_) ->
     False
   rule650 = \ gg_ ->
     GGraphExpression gg_
   rule651 = \ lcopy ->
     lcopy
   rule652 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_GExpression_GListExpression  :: ([GExpression]) -> T_GExpression 
sem_GExpression_GListExpression arg_gexprs_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 :: T_GExpression_v25 
             v25 = \ (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule653  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule654  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule655  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule656  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule657  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule658  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule659  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule660  Void
                           lcopy = rule661 arg_gexprs_
                           alhsOcopy :: GExpression
                           alhsOcopy = rule662 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule663 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GExpression_s26 v25
   /*# LINE 150 "./frontend/Tonic/Pretty.ag" #*/
   rule653 = \  (_) ->
                                          /*# LINE 150 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3882 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 151 "./frontend/Tonic/Pretty.ag" #*/
   rule654 = \  (_) ->
                                          /*# LINE 151 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3887 "frontend/Tonic/Tonic.icl"#*/
   rule655 = \  (_) ->
     False
   rule656 = \  (_) ->
     Nothing
   rule657 = \  (_) ->
     Nothing
   rule658 = \  (_) ->
     []
   rule659 = \  (_) ->
     []
   rule660 = \  (_) ->
     False
   rule661 = \ gexprs_ ->
     GListExpression gexprs_
   rule662 = \ lcopy ->
     lcopy
   rule663 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_GExpression_GCleanExpression  :: (GCleanExpression) -> T_GExpression 
sem_GExpression_GCleanExpression arg_gcexpr_ = T_GExpression (lift st26) where
   st26 =
         let
             v25 :: T_GExpression_v25 
             v25 = \ (T_GExpression_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule664 arg_gcexpr_
                           alhsOppAg :: Doc
                           alhsOppAg = rule665 arg_gcexpr_
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule666  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule667  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule668  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule669  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule670  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule671  Void
                           lcopy = rule672 arg_gcexpr_
                           alhsOcopy :: GExpression
                           alhsOcopy = rule673 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule674 alhsIgraph
                           ag__result_ = T_GExpression_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GExpression_s26 v25
   /*# LINE 152 "./frontend/Tonic/Pretty.ag" #*/
   rule664 = \ gcexpr_ ->
                                          /*# LINE 152 "./frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3941 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 153 "./frontend/Tonic/Pretty.ag" #*/
   rule665 = \ gcexpr_ ->
                                          /*# LINE 153 "./frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3946 "frontend/Tonic/Tonic.icl"#*/
   rule666 = \  (_) ->
     False
   rule667 = \  (_) ->
     Nothing
   rule668 = \  (_) ->
     Nothing
   rule669 = \  (_) ->
     []
   rule670 = \  (_) ->
     []
   rule671 = \  (_) ->
     False
   rule672 = \ gcexpr_ ->
     GCleanExpression gcexpr_
   rule673 = \ lcopy ->
     lcopy
   rule674 = \ ((alhsIgraph)) ->
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
             v28 :: T_GFunDef_v28 
             v28 = \ (T_GFunDef_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_gfd_argsX23 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVars (arg_gfd_args_))
                           st_gfd_rhsX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_gfd_rhs_))
                           (T_FreeVars_vOut22 agfd_argsIcopy agfd_argsIgraph agfd_argsIhasRecs agfd_argsImEntryId agfd_argsImExitId agfd_argsIrecNode) = inv_FreeVars_s23 st_gfd_argsX23 (T_FreeVars_vIn22 agfd_argsOcaseExpr agfd_argsOcurrTaskName agfd_argsOgraph agfd_argsOmergeId agfd_argsOmoduleEnv)
                           (T_Expression_vOut13 agfd_rhsIcopy agfd_rhsIgraph agfd_rhsIhasRecs agfd_rhsImEntryId agfd_rhsImExitId agfd_rhsIppAg agfd_rhsIppAgs agfd_rhsIppDebug agfd_rhsIppDebugs agfd_rhsIrecNode) = inv_Expression_s14 st_gfd_rhsX14 (T_Expression_vIn13 agfd_rhsOcaseExpr agfd_rhsOcurrTaskName agfd_rhsOgraph agfd_rhsOmergeId agfd_rhsOmoduleEnv)
                           alhsOfunArgs :: [FreeVar]
                           alhsOfunArgs = rule675 agfd_argsIcopy
                           alhsOfunRhs :: Expression
                           alhsOfunRhs = rule676 agfd_rhsIcopy
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule677 agfd_rhsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule678 agfd_rhsImExitId
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule679 agfd_argsIhasRecs agfd_rhsIhasRecs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule680 agfd_argsIrecNode agfd_rhsIrecNode
                           lcopy = rule681 agfd_argsIcopy agfd_rhsIcopy arg_gfd_name_ arg_gfd_priority_ arg_gfd_type_
                           alhsOcopy :: GFunDef
                           alhsOcopy = rule682 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule683 agfd_rhsIgraph
                           agfd_argsOcaseExpr = rule684 alhsIcaseExpr
                           agfd_argsOcurrTaskName = rule685 alhsIcurrTaskName
                           agfd_argsOgraph = rule686 alhsIgraph
                           agfd_argsOmergeId = rule687 alhsImergeId
                           agfd_argsOmoduleEnv = rule688 alhsImoduleEnv
                           agfd_rhsOcaseExpr = rule689 alhsIcaseExpr
                           agfd_rhsOcurrTaskName = rule690 alhsIcurrTaskName
                           agfd_rhsOgraph = rule691 agfd_argsIgraph
                           agfd_rhsOmergeId = rule692 alhsImergeId
                           agfd_rhsOmoduleEnv = rule693 alhsImoduleEnv
                           ag__result_ = T_GFunDef_vOut28 alhsOcopy alhsOfunArgs alhsOfunRhs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_ )
         in C_GFunDef_s29 v28
   /*# LINE 69 "./frontend/Tonic/MkGraph.ag" #*/
   rule675 = \ ((agfd_argsIcopy)) ->
                      /*# LINE 69 "./frontend/Tonic/MkGraph.ag" #*/
                      agfd_argsIcopy
                      /*# LINE 4055 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 70 "./frontend/Tonic/MkGraph.ag" #*/
   rule676 = \ ((agfd_rhsIcopy)) ->
                      /*# LINE 70 "./frontend/Tonic/MkGraph.ag" #*/
                      agfd_rhsIcopy
                      /*# LINE 4060 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 72 "./frontend/Tonic/MkGraph.ag" #*/
   rule677 = \ ((agfd_rhsImEntryId)) ->
                       /*# LINE 72 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImEntryId
                       /*# LINE 4065 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 73 "./frontend/Tonic/MkGraph.ag" #*/
   rule678 = \ ((agfd_rhsImExitId)) ->
                       /*# LINE 73 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImExitId
                       /*# LINE 4070 "frontend/Tonic/Tonic.icl"#*/
   rule679 = \ ((agfd_argsIhasRecs)) ((agfd_rhsIhasRecs)) ->
     agfd_argsIhasRecs || agfd_rhsIhasRecs
   rule680 = \ ((agfd_argsIrecNode)) ((agfd_rhsIrecNode)) ->
     agfd_argsIrecNode || agfd_rhsIrecNode
   rule681 = \ ((agfd_argsIcopy)) ((agfd_rhsIcopy)) gfd_name_ gfd_priority_ gfd_type_ ->
     {GFunDef|gfd_name = gfd_name_ , gfd_args = agfd_argsIcopy , gfd_rhs = agfd_rhsIcopy , gfd_type = gfd_type_ , gfd_priority = gfd_priority_}
   rule682 = \ lcopy ->
     lcopy
   rule683 = \ ((agfd_rhsIgraph)) ->
     agfd_rhsIgraph
   rule684 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule685 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule686 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule687 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule688 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule689 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule690 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule691 = \ ((agfd_argsIgraph)) ->
     agfd_argsIgraph
   rule692 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule693 = \ ((alhsImoduleEnv)) ->
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
             v31 :: T_GLet_v31 
             v31 = \ (T_GLet_vIn31 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_glet_bindsX38 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_glet_binds_))
                           st_glet_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glet_expr_))
                           (T_GLetBinds_vOut37 aglet_bindsIcopy aglet_bindsIgraph aglet_bindsIhasRecs aglet_bindsImCaseVarExpr aglet_bindsImEntryId aglet_bindsImExitId aglet_bindsIppAg aglet_bindsIppAgs aglet_bindsIppDebug aglet_bindsIppDebugs aglet_bindsIrecNode) = inv_GLetBinds_s38 st_glet_bindsX38 (T_GLetBinds_vIn37 aglet_bindsOcaseExpr aglet_bindsOcurrTaskName aglet_bindsOgraph aglet_bindsOmergeId aglet_bindsOmoduleEnv)
                           (T_Expression_vOut13 aglet_exprIcopy aglet_exprIgraph aglet_exprIhasRecs aglet_exprImEntryId aglet_exprImExitId aglet_exprIppAg aglet_exprIppAgs aglet_exprIppDebug aglet_exprIppDebugs aglet_exprIrecNode) = inv_Expression_s14 st_glet_exprX14 (T_Expression_vIn13 aglet_exprOcaseExpr aglet_exprOcurrTaskName aglet_exprOgraph aglet_exprOmergeId aglet_exprOmoduleEnv)
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule694 aglet_bindsIcopy aglet_exprIgraph lconnId lmCaseVarExpr
                           lmCaseVarExpr = rule695 aglet_bindsImCaseVarExpr
                           aglet_exprOcaseExpr = rule696 lmCaseVarExpr
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule697  Void
                           lconnId = rule698 aglet_exprImEntryId aglet_exprIrecNode alhsImergeId
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule699 aglet_bindsIppDebugs
                           alhsOppAg :: Doc
                           alhsOppAg = rule700 aglet_bindsIppAgs
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule701 aglet_bindsIhasRecs aglet_exprIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule702 aglet_bindsImEntryId aglet_exprImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule703 aglet_bindsImExitId aglet_exprImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule704 aglet_bindsIppAgs aglet_exprIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule705 aglet_bindsIppDebugs aglet_exprIppDebugs
                           lcopy = rule706 aglet_bindsIcopy aglet_exprIcopy
                           alhsOcopy :: GLet
                           alhsOcopy = rule707 lcopy
                           aglet_bindsOcaseExpr = rule708 alhsIcaseExpr
                           aglet_bindsOcurrTaskName = rule709 alhsIcurrTaskName
                           aglet_bindsOgraph = rule710 alhsIgraph
                           aglet_bindsOmergeId = rule711 alhsImergeId
                           aglet_bindsOmoduleEnv = rule712 alhsImoduleEnv
                           aglet_exprOcurrTaskName = rule713 alhsIcurrTaskName
                           aglet_exprOgraph = rule714 aglet_bindsIgraph
                           aglet_exprOmergeId = rule715 alhsImergeId
                           aglet_exprOmoduleEnv = rule716 alhsImoduleEnv
                           ag__result_ = T_GLet_vOut31 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GLet_s32 v31
   /*# LINE 174 "./frontend/Tonic/MkGraph.ag" #*/
   rule694 = \ ((aglet_bindsIcopy)) ((aglet_exprIgraph)) lconnId lmCaseVarExpr ->
                    /*# LINE 174 "./frontend/Tonic/MkGraph.ag" #*/
                    case lmCaseVarExpr     of
                      Just e  -> aglet_exprIgraph
                      _       -> let (lid, g)  = addNode (GLet aglet_bindsIcopy) aglet_exprIgraph
                                     err       = abort "Failed to add let edge; no synthesized ID from let body"
                                 in maybe err (\n -> addEmptyEdge (lid, n) g) lconnId
                    /*# LINE 4205 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 181 "./frontend/Tonic/MkGraph.ag" #*/
   rule695 = \ ((aglet_bindsImCaseVarExpr)) ->
                           /*# LINE 181 "./frontend/Tonic/MkGraph.ag" #*/
                           aglet_bindsImCaseVarExpr
                           /*# LINE 4210 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 183 "./frontend/Tonic/MkGraph.ag" #*/
   rule696 = \ lmCaseVarExpr ->
                             /*# LINE 183 "./frontend/Tonic/MkGraph.ag" #*/
                             lmCaseVarExpr
                             /*# LINE 4215 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 185 "./frontend/Tonic/MkGraph.ag" #*/
   rule697 = \  (_) ->
                      /*# LINE 185 "./frontend/Tonic/MkGraph.ag" #*/
                      False
                      /*# LINE 4220 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 187 "./frontend/Tonic/MkGraph.ag" #*/
   rule698 = \ ((aglet_exprImEntryId)) ((aglet_exprIrecNode)) ((alhsImergeId)) ->
                     /*# LINE 187 "./frontend/Tonic/MkGraph.ag" #*/
                     if aglet_exprIrecNode (Just alhsImergeId) aglet_exprImEntryId
                     /*# LINE 4225 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 156 "./frontend/Tonic/Pretty.ag" #*/
   rule699 = \ ((aglet_bindsIppDebugs)) ->
                         /*# LINE 156 "./frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppDebugs
                         /*# LINE 4230 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 157 "./frontend/Tonic/Pretty.ag" #*/
   rule700 = \ ((aglet_bindsIppAgs)) ->
                         /*# LINE 157 "./frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppAgs
                         /*# LINE 4235 "frontend/Tonic/Tonic.icl"#*/
   rule701 = \ ((aglet_bindsIhasRecs)) ((aglet_exprIhasRecs)) ->
     aglet_bindsIhasRecs || aglet_exprIhasRecs
   rule702 = \ ((aglet_bindsImEntryId)) ((aglet_exprImEntryId)) ->
     aglet_bindsImEntryId <> aglet_exprImEntryId
   rule703 = \ ((aglet_bindsImExitId)) ((aglet_exprImExitId)) ->
     aglet_bindsImExitId <> aglet_exprImExitId
   rule704 = \ ((aglet_bindsIppAgs)) ((aglet_exprIppAgs)) ->
     aglet_bindsIppAgs ++ aglet_exprIppAgs
   rule705 = \ ((aglet_bindsIppDebugs)) ((aglet_exprIppDebugs)) ->
     aglet_bindsIppDebugs ++ aglet_exprIppDebugs
   rule706 = \ ((aglet_bindsIcopy)) ((aglet_exprIcopy)) ->
     {GLet|glet_binds = aglet_bindsIcopy , glet_expr = aglet_exprIcopy}
   rule707 = \ lcopy ->
     lcopy
   rule708 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule709 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule710 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule711 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule712 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule713 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule714 = \ ((aglet_bindsIgraph)) ->
     aglet_bindsIgraph
   rule715 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule716 = \ ((alhsImoduleEnv)) ->
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
             v34 :: T_GLetBind_v34 
             v34 = \ (T_GLetBind_vIn34 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_glb_srcX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glb_src_))
                           (T_Expression_vOut13 aglb_srcIcopy aglb_srcIgraph aglb_srcIhasRecs aglb_srcImEntryId aglb_srcImExitId aglb_srcIppAg aglb_srcIppAgs aglb_srcIppDebug aglb_srcIppDebugs aglb_srcIrecNode) = inv_Expression_s14 st_glb_srcX14 (T_Expression_vIn13 aglb_srcOcaseExpr aglb_srcOcurrTaskName aglb_srcOgraph aglb_srcOmergeId aglb_srcOmoduleEnv)
                           alhsOmCaseVarExpr :: Maybe Expression
                           alhsOmCaseVarExpr = rule717 aglb_srcIcopy arg_glb_dst_
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule718 aglb_srcIppDebug arg_glb_dst_
                           alhsOppAg :: Doc
                           alhsOppAg = rule719 aglb_srcIppAg arg_glb_dst_
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule720 aglb_srcIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule721 aglb_srcImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule722 aglb_srcImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule723 aglb_srcIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule724 aglb_srcIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule725 aglb_srcIrecNode
                           lcopy = rule726 aglb_srcIcopy arg_glb_dst_
                           alhsOcopy :: GLetBind
                           alhsOcopy = rule727 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule728 aglb_srcIgraph
                           aglb_srcOcaseExpr = rule729 alhsIcaseExpr
                           aglb_srcOcurrTaskName = rule730 alhsIcurrTaskName
                           aglb_srcOgraph = rule731 alhsIgraph
                           aglb_srcOmergeId = rule732 alhsImergeId
                           aglb_srcOmoduleEnv = rule733 alhsImoduleEnv
                           ag__result_ = T_GLetBind_vOut34 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GLetBind_s35 v34
   /*# LINE 197 "./frontend/Tonic/MkGraph.ag" #*/
   rule717 = \ ((aglb_srcIcopy)) glb_dst_ ->
                                  /*# LINE 197 "./frontend/Tonic/MkGraph.ag" #*/
                                  if (glb_dst_ == "_case_var") (Just aglb_srcIcopy) Nothing
                                  /*# LINE 4363 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 160 "./frontend/Tonic/Pretty.ag" #*/
   rule718 = \ ((aglb_srcIppDebug)) glb_dst_ ->
                             /*# LINE 160 "./frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppDebug
                             /*# LINE 4368 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 161 "./frontend/Tonic/Pretty.ag" #*/
   rule719 = \ ((aglb_srcIppAg)) glb_dst_ ->
                             /*# LINE 161 "./frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppAg
                             /*# LINE 4373 "frontend/Tonic/Tonic.icl"#*/
   rule720 = \ ((aglb_srcIhasRecs)) ->
     aglb_srcIhasRecs
   rule721 = \ ((aglb_srcImEntryId)) ->
     aglb_srcImEntryId
   rule722 = \ ((aglb_srcImExitId)) ->
     aglb_srcImExitId
   rule723 = \ ((aglb_srcIppAgs)) ->
     aglb_srcIppAgs
   rule724 = \ ((aglb_srcIppDebugs)) ->
     aglb_srcIppDebugs
   rule725 = \ ((aglb_srcIrecNode)) ->
     aglb_srcIrecNode
   rule726 = \ ((aglb_srcIcopy)) glb_dst_ ->
     {GLetBind|glb_dst = glb_dst_ , glb_src = aglb_srcIcopy}
   rule727 = \ lcopy ->
     lcopy
   rule728 = \ ((aglb_srcIgraph)) ->
     aglb_srcIgraph
   rule729 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule730 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule731 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule732 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule733 = \ ((alhsImoduleEnv)) ->
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
             v37 :: T_GLetBinds_v37 
             v37 = \ (T_GLetBinds_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_hdX35 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBind (arg_hd_))
                           st_tlX38 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_tl_))
                           (T_GLetBind_vOut34 ahdIcopy ahdIgraph ahdIhasRecs ahdImCaseVarExpr ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_GLetBind_s35 st_hdX35 (T_GLetBind_vIn34 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_GLetBinds_vOut37 atlIcopy atlIgraph atlIhasRecs atlImCaseVarExpr atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_GLetBinds_s38 st_tlX38 (T_GLetBinds_vIn37 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOmCaseVarExpr :: Maybe Expression
                           alhsOmCaseVarExpr = rule734 ahdImCaseVarExpr atlImCaseVarExpr
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule735 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule736 ahdImEntryId atlImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule737 ahdImExitId atlImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule738 ahdIppAg atlIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule739 ahdIppAgs atlIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule740 ahdIppDebug atlIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule741 ahdIppDebugs atlIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule742 ahdIrecNode atlIrecNode
                           lcopy = rule743 ahdIcopy atlIcopy
                           alhsOcopy :: GLetBinds
                           alhsOcopy = rule744 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule745 atlIgraph
                           ahdOcaseExpr = rule746 alhsIcaseExpr
                           ahdOcurrTaskName = rule747 alhsIcurrTaskName
                           ahdOgraph = rule748 alhsIgraph
                           ahdOmergeId = rule749 alhsImergeId
                           ahdOmoduleEnv = rule750 alhsImoduleEnv
                           atlOcaseExpr = rule751 alhsIcaseExpr
                           atlOcurrTaskName = rule752 alhsIcurrTaskName
                           atlOgraph = rule753 ahdIgraph
                           atlOmergeId = rule754 alhsImergeId
                           atlOmoduleEnv = rule755 alhsImoduleEnv
                           ag__result_ = T_GLetBinds_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GLetBinds_s38 v37
   /*# LINE 193 "./frontend/Tonic/MkGraph.ag" #*/
   rule734 = \ ((ahdImCaseVarExpr)) ((atlImCaseVarExpr)) ->
                               /*# LINE 193 "./frontend/Tonic/MkGraph.ag" #*/
                               ahdImCaseVarExpr <> atlImCaseVarExpr
                               /*# LINE 4504 "frontend/Tonic/Tonic.icl"#*/
   rule735 = \ ((ahdIhasRecs)) ((atlIhasRecs)) ->
     ahdIhasRecs || atlIhasRecs
   rule736 = \ ((ahdImEntryId)) ((atlImEntryId)) ->
     ahdImEntryId <> atlImEntryId
   rule737 = \ ((ahdImExitId)) ((atlImExitId)) ->
     ahdImExitId <> atlImExitId
   rule738 = \ ((ahdIppAg)) ((atlIppAg)) ->
     ahdIppAg <$$> atlIppAg
   rule739 = \ ((ahdIppAgs)) ((atlIppAgs)) ->
     ahdIppAgs ++ atlIppAgs
   rule740 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug <$$> atlIppDebug
   rule741 = \ ((ahdIppDebugs)) ((atlIppDebugs)) ->
     ahdIppDebugs ++ atlIppDebugs
   rule742 = \ ((ahdIrecNode)) ((atlIrecNode)) ->
     ahdIrecNode || atlIrecNode
   rule743 = \ ((ahdIcopy)) ((atlIcopy)) ->
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule744 = \ lcopy ->
     lcopy
   rule745 = \ ((atlIgraph)) ->
     atlIgraph
   rule746 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule747 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule748 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule749 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule750 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule751 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule752 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule753 = \ ((ahdIgraph)) ->
     ahdIgraph
   rule754 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule755 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_GLetBinds_Nil  ::   T_GLetBinds 
sem_GLetBinds_Nil  = T_GLetBinds (lift st38) where
   st38 =
         let
             v37 :: T_GLetBinds_v37 
             v37 = \ (T_GLetBinds_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOmCaseVarExpr :: Maybe Expression
                           alhsOmCaseVarExpr = rule756  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule757  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule758  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule759  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule760  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule761  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule762  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule763  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule764  Void
                           lcopy = rule765  Void
                           alhsOcopy :: GLetBinds
                           alhsOcopy = rule766 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule767 alhsIgraph
                           ag__result_ = T_GLetBinds_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GLetBinds_s38 v37
   /*# LINE 194 "./frontend/Tonic/MkGraph.ag" #*/
   rule756 = \  (_) ->
                               /*# LINE 194 "./frontend/Tonic/MkGraph.ag" #*/
                               Nothing
                               /*# LINE 4584 "frontend/Tonic/Tonic.icl"#*/
   rule757 = \  (_) ->
     False
   rule758 = \  (_) ->
     Nothing
   rule759 = \  (_) ->
     Nothing
   rule760 = \  (_) ->
     empty
   rule761 = \  (_) ->
     []
   rule762 = \  (_) ->
     empty
   rule763 = \  (_) ->
     []
   rule764 = \  (_) ->
     False
   rule765 = \  (_) ->
     []
   rule766 = \ lcopy ->
     lcopy
   rule767 = \ ((alhsIgraph)) ->
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
             v40 :: T_GlobalDefinedSymbol_v40 
             v40 = \ (T_GlobalDefinedSymbol_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule768  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule769  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule770  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule771  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule772  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule773  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule774  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule775  Void
                           lcopy = rule776 arg_x1_
                           alhsOcopy :: GlobalDefinedSymbol
                           alhsOcopy = rule777 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule778 alhsIgraph
                           ag__result_ = T_GlobalDefinedSymbol_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_GlobalDefinedSymbol_s41 v40
   rule768 = \  (_) ->
     False
   rule769 = \  (_) ->
     Nothing
   rule770 = \  (_) ->
     Nothing
   rule771 = \  (_) ->
     empty
   rule772 = \  (_) ->
     []
   rule773 = \  (_) ->
     empty
   rule774 = \  (_) ->
     []
   rule775 = \  (_) ->
     False
   rule776 = \ x1_ ->
     (x1_)
   rule777 = \ lcopy ->
     lcopy
   rule778 = \ ((alhsIgraph)) ->
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
recNode_Syn_Ident :: Syn_Ident -> (Bool)
recNode_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Ident :: Syn_Ident -> ([Doc])
ppDebugs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Ident :: Syn_Ident -> (Doc)
ppDebug_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Ident :: Syn_Ident -> ([Doc])
ppAgs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Ident :: Syn_Ident -> (Doc)
ppAg_Syn_Ident (Syn_Ident _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mExitId_Syn_Ident (Syn_Ident _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mEntryId_Syn_Ident (Syn_Ident _ _ _ _ x _ _ _ _ _ _) = x
ident_Syn_Ident :: Syn_Ident -> (String)
ident_Syn_Ident (Syn_Ident _ _ _ x _ _ _ _ _ _ _) = x
hasRecs_Syn_Ident :: Syn_Ident -> (Bool)
hasRecs_Syn_Ident (Syn_Ident _ _ x _ _ _ _ _ _ _ _) = x
graph_Syn_Ident :: Syn_Ident -> (GinGraph)
graph_Syn_Ident (Syn_Ident _ x _ _ _ _ _ _ _ _ _) = x
copy_Syn_Ident :: Syn_Ident -> (Ident)
copy_Syn_Ident (Syn_Ident x _ _ _ _ _ _ _ _ _ _) = x
wrap_Ident :: T_Ident  Inh_Ident  -> (Syn_Ident )
wrap_Ident (T_Ident act) (Inh_Ident alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Ident_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Ident_s44 sem arg) >>= \ (T_Ident_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Ident alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Ident :: Ident  -> T_Ident 
sem_Ident { Ident | id_name = id_name_,id_info = id_info_ } = sem_Ident_Ident id_name_ id_info_

// semantic domain
attach_T_Ident (T_Ident t_Ident) = t_Ident
inv_Ident_s44 (C_Ident_s44 x) = x
sem_Ident_Ident  :: (String) (SymbolPtr) -> T_Ident 
sem_Ident_Ident arg_id_name_ arg_id_info_ = T_Ident (lift st44) where
   st44 =
         let
             v43 :: T_Ident_v43 
             v43 = \ (T_Ident_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOident :: String
                           alhsOident = rule779 arg_id_name_
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule780 arg_id_name_
                           alhsOppAg :: Doc
                           alhsOppAg = rule781 arg_id_name_
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule782  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule783  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule784  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule785  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule786  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule787  Void
                           lcopy = rule788 arg_id_info_ arg_id_name_
                           alhsOcopy :: Ident
                           alhsOcopy = rule789 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule790 alhsIgraph
                           ag__result_ = T_Ident_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Ident_s44 v43
   /*# LINE 48 "./frontend/Tonic/MkGraph.ag" #*/
   rule779 = \ id_name_ ->
                        /*# LINE 48 "./frontend/Tonic/MkGraph.ag" #*/
                        id_name_
                        /*# LINE 4797 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 104 "./frontend/Tonic/Pretty.ag" #*/
   rule780 = \ id_name_ ->
                          /*# LINE 104 "./frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4802 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 105 "./frontend/Tonic/Pretty.ag" #*/
   rule781 = \ id_name_ ->
                          /*# LINE 105 "./frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4807 "frontend/Tonic/Tonic.icl"#*/
   rule782 = \  (_) ->
     False
   rule783 = \  (_) ->
     Nothing
   rule784 = \  (_) ->
     Nothing
   rule785 = \  (_) ->
     []
   rule786 = \  (_) ->
     []
   rule787 = \  (_) ->
     False
   rule788 = \ id_info_ id_name_ ->
     {Ident|id_name = id_name_ , id_info = id_info_}
   rule789 = \ lcopy ->
     lcopy
   rule790 = \ ((alhsIgraph)) ->
     alhsIgraph

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
             v46 :: T_Selection_v46 
             v46 = \ (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_gdsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           (T_GlobalDefinedSymbol_vOut40 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsX41 (T_GlobalDefinedSymbol_vIn40 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule791 agdsIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule792 agdsIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule793 agdsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule794 agdsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule795 agdsImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule796 agdsIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule797 agdsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule798 agdsIrecNode
                           lcopy = rule799 agdsIcopy arg_n_
                           alhsOcopy :: Selection
                           alhsOcopy = rule800 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule801 agdsIgraph
                           agdsOcaseExpr = rule802 alhsIcaseExpr
                           agdsOcurrTaskName = rule803 alhsIcurrTaskName
                           agdsOgraph = rule804 alhsIgraph
                           agdsOmergeId = rule805 alhsImergeId
                           agdsOmoduleEnv = rule806 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Selection_s47 v46
   /*# LINE 138 "./frontend/Tonic/Pretty.ag" #*/
   rule791 = \ ((agdsIppDebug)) ->
                                        /*# LINE 138 "./frontend/Tonic/Pretty.ag" #*/
                                        agdsIppDebug
                                        /*# LINE 4919 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 139 "./frontend/Tonic/Pretty.ag" #*/
   rule792 = \ ((agdsIppAg)) ->
                                        /*# LINE 139 "./frontend/Tonic/Pretty.ag" #*/
                                        agdsIppAg
                                        /*# LINE 4924 "frontend/Tonic/Tonic.icl"#*/
   rule793 = \ ((agdsIhasRecs)) ->
     agdsIhasRecs
   rule794 = \ ((agdsImEntryId)) ->
     agdsImEntryId
   rule795 = \ ((agdsImExitId)) ->
     agdsImExitId
   rule796 = \ ((agdsIppAgs)) ->
     agdsIppAgs
   rule797 = \ ((agdsIppDebugs)) ->
     agdsIppDebugs
   rule798 = \ ((agdsIrecNode)) ->
     agdsIrecNode
   rule799 = \ ((agdsIcopy)) n_ ->
     RecordSelection agdsIcopy n_
   rule800 = \ lcopy ->
     lcopy
   rule801 = \ ((agdsIgraph)) ->
     agdsIgraph
   rule802 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule803 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule804 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule805 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule806 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Selection_ArraySelection  :: (T_GlobalDefinedSymbol ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_ArraySelection arg_gds_ arg_eiptr_ arg_expr_ = T_Selection (lift st47) where
   st47 =
         let
             v46 :: T_Selection_v46 
             v46 = \ (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_gdsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut40 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s41 st_gdsX41 (T_GlobalDefinedSymbol_vIn40 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule807  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule808  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule809 aexprIhasRecs agdsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule810 aexprImEntryId agdsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule811 aexprImExitId agdsImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule812 aexprIppAgs agdsIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule813 aexprIppDebugs agdsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule814 aexprIrecNode agdsIrecNode
                           lcopy = rule815 aexprIcopy agdsIcopy arg_eiptr_
                           alhsOcopy :: Selection
                           alhsOcopy = rule816 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule817 aexprIgraph
                           agdsOcaseExpr = rule818 alhsIcaseExpr
                           agdsOcurrTaskName = rule819 alhsIcurrTaskName
                           agdsOgraph = rule820 alhsIgraph
                           agdsOmergeId = rule821 alhsImergeId
                           agdsOmoduleEnv = rule822 alhsImoduleEnv
                           aexprOcaseExpr = rule823 alhsIcaseExpr
                           aexprOcurrTaskName = rule824 alhsIcurrTaskName
                           aexprOgraph = rule825 agdsIgraph
                           aexprOmergeId = rule826 alhsImergeId
                           aexprOmoduleEnv = rule827 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Selection_s47 v46
   /*# LINE 140 "./frontend/Tonic/Pretty.ag" #*/
   rule807 = \  (_) ->
                                        /*# LINE 140 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 5002 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 141 "./frontend/Tonic/Pretty.ag" #*/
   rule808 = \  (_) ->
                                        /*# LINE 141 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 5007 "frontend/Tonic/Tonic.icl"#*/
   rule809 = \ ((aexprIhasRecs)) ((agdsIhasRecs)) ->
     agdsIhasRecs || aexprIhasRecs
   rule810 = \ ((aexprImEntryId)) ((agdsImEntryId)) ->
     agdsImEntryId <> aexprImEntryId
   rule811 = \ ((aexprImExitId)) ((agdsImExitId)) ->
     agdsImExitId <> aexprImExitId
   rule812 = \ ((aexprIppAgs)) ((agdsIppAgs)) ->
     agdsIppAgs ++ aexprIppAgs
   rule813 = \ ((aexprIppDebugs)) ((agdsIppDebugs)) ->
     agdsIppDebugs ++ aexprIppDebugs
   rule814 = \ ((aexprIrecNode)) ((agdsIrecNode)) ->
     agdsIrecNode || aexprIrecNode
   rule815 = \ ((aexprIcopy)) ((agdsIcopy)) eiptr_ ->
     ArraySelection agdsIcopy eiptr_ aexprIcopy
   rule816 = \ lcopy ->
     lcopy
   rule817 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule818 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule819 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule820 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule821 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule822 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule823 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule824 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule825 = \ ((agdsIgraph)) ->
     agdsIgraph
   rule826 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule827 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Selection_DictionarySelection  :: (T_BoundVar ) (T_Selections ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_DictionarySelection arg_bv_ arg_sels_ arg_eiptr_ arg_expr_ = T_Selection (lift st47) where
   st47 =
         let
             v46 :: T_Selection_v46 
             v46 = \ (T_Selection_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_bvX8 = 'Control.Monad.Identity'.runIdentity (attach_T_BoundVar (arg_bv_))
                           st_selsX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_BoundVar_vOut7 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BoundVar_s8 st_bvX8 (T_BoundVar_vIn7 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           (T_Selections_vOut49 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s50 st_selsX50 (T_Selections_vIn49 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule828  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule829  Void
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule830 abvIhasRecs aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule831 abvImEntryId aexprImEntryId aselsImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule832 abvImExitId aexprImExitId aselsImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule833 abvIppAgs aexprIppAgs aselsIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule834 abvIppDebugs aexprIppDebugs aselsIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule835 abvIrecNode aexprIrecNode aselsIrecNode
                           lcopy = rule836 abvIcopy aexprIcopy aselsIcopy arg_eiptr_
                           alhsOcopy :: Selection
                           alhsOcopy = rule837 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule838 aexprIgraph
                           abvOcaseExpr = rule839 alhsIcaseExpr
                           abvOcurrTaskName = rule840 alhsIcurrTaskName
                           abvOgraph = rule841 alhsIgraph
                           abvOmergeId = rule842 alhsImergeId
                           abvOmoduleEnv = rule843 alhsImoduleEnv
                           aselsOcaseExpr = rule844 alhsIcaseExpr
                           aselsOcurrTaskName = rule845 alhsIcurrTaskName
                           aselsOgraph = rule846 abvIgraph
                           aselsOmergeId = rule847 alhsImergeId
                           aselsOmoduleEnv = rule848 alhsImoduleEnv
                           aexprOcaseExpr = rule849 alhsIcaseExpr
                           aexprOcurrTaskName = rule850 alhsIcurrTaskName
                           aexprOgraph = rule851 aselsIgraph
                           aexprOmergeId = rule852 alhsImergeId
                           aexprOmoduleEnv = rule853 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Selection_s47 v46
   /*# LINE 142 "./frontend/Tonic/Pretty.ag" #*/
   rule828 = \  (_) ->
                                        /*# LINE 142 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 5102 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 143 "./frontend/Tonic/Pretty.ag" #*/
   rule829 = \  (_) ->
                                        /*# LINE 143 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 5107 "frontend/Tonic/Tonic.icl"#*/
   rule830 = \ ((abvIhasRecs)) ((aexprIhasRecs)) ((aselsIhasRecs)) ->
     abvIhasRecs || aselsIhasRecs || aexprIhasRecs
   rule831 = \ ((abvImEntryId)) ((aexprImEntryId)) ((aselsImEntryId)) ->
     abvImEntryId <> aselsImEntryId <> aexprImEntryId
   rule832 = \ ((abvImExitId)) ((aexprImExitId)) ((aselsImExitId)) ->
     abvImExitId <> aselsImExitId <> aexprImExitId
   rule833 = \ ((abvIppAgs)) ((aexprIppAgs)) ((aselsIppAgs)) ->
     abvIppAgs ++ aselsIppAgs ++ aexprIppAgs
   rule834 = \ ((abvIppDebugs)) ((aexprIppDebugs)) ((aselsIppDebugs)) ->
     abvIppDebugs ++ aselsIppDebugs ++ aexprIppDebugs
   rule835 = \ ((abvIrecNode)) ((aexprIrecNode)) ((aselsIrecNode)) ->
     abvIrecNode || aselsIrecNode || aexprIrecNode
   rule836 = \ ((abvIcopy)) ((aexprIcopy)) ((aselsIcopy)) eiptr_ ->
     DictionarySelection abvIcopy aselsIcopy eiptr_ aexprIcopy
   rule837 = \ lcopy ->
     lcopy
   rule838 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule839 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule840 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule841 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule842 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule843 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule844 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule845 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule846 = \ ((abvIgraph)) ->
     abvIgraph
   rule847 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule848 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule849 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule850 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule851 = \ ((aselsIgraph)) ->
     aselsIgraph
   rule852 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule853 = \ ((alhsImoduleEnv)) ->
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
             v49 :: T_Selections_v49 
             v49 = \ (T_Selections_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_hdX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Selection (arg_hd_))
                           st_tlX50 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_tl_))
                           (T_Selection_vOut46 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Selection_s47 st_hdX47 (T_Selection_vIn46 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Selections_vOut49 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_Selections_s50 st_tlX50 (T_Selections_vIn49 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule854 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule855 ahdImEntryId atlImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule856 ahdImExitId atlImExitId
                           alhsOppAg :: Doc
                           alhsOppAg = rule857 ahdIppAg atlIppAg
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule858 ahdIppAgs atlIppAgs
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule859 ahdIppDebug atlIppDebug
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule860 ahdIppDebugs atlIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule861 ahdIrecNode atlIrecNode
                           lcopy = rule862 ahdIcopy atlIcopy
                           alhsOcopy :: Selections
                           alhsOcopy = rule863 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule864 atlIgraph
                           ahdOcaseExpr = rule865 alhsIcaseExpr
                           ahdOcurrTaskName = rule866 alhsIcurrTaskName
                           ahdOgraph = rule867 alhsIgraph
                           ahdOmergeId = rule868 alhsImergeId
                           ahdOmoduleEnv = rule869 alhsImoduleEnv
                           atlOcaseExpr = rule870 alhsIcaseExpr
                           atlOcurrTaskName = rule871 alhsIcurrTaskName
                           atlOgraph = rule872 ahdIgraph
                           atlOmergeId = rule873 alhsImergeId
                           atlOmoduleEnv = rule874 alhsImoduleEnv
                           ag__result_ = T_Selections_vOut49 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Selections_s50 v49
   rule854 = \ ((ahdIhasRecs)) ((atlIhasRecs)) ->
     ahdIhasRecs || atlIhasRecs
   rule855 = \ ((ahdImEntryId)) ((atlImEntryId)) ->
     ahdImEntryId <> atlImEntryId
   rule856 = \ ((ahdImExitId)) ((atlImExitId)) ->
     ahdImExitId <> atlImExitId
   rule857 = \ ((ahdIppAg)) ((atlIppAg)) ->
     ahdIppAg <$$> atlIppAg
   rule858 = \ ((ahdIppAgs)) ((atlIppAgs)) ->
     ahdIppAgs ++ atlIppAgs
   rule859 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug <$$> atlIppDebug
   rule860 = \ ((ahdIppDebugs)) ((atlIppDebugs)) ->
     ahdIppDebugs ++ atlIppDebugs
   rule861 = \ ((ahdIrecNode)) ((atlIrecNode)) ->
     ahdIrecNode || atlIrecNode
   rule862 = \ ((ahdIcopy)) ((atlIcopy)) ->
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule863 = \ lcopy ->
     lcopy
   rule864 = \ ((atlIgraph)) ->
     atlIgraph
   rule865 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule866 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule867 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule868 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule869 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule870 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule871 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule872 = \ ((ahdIgraph)) ->
     ahdIgraph
   rule873 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule874 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Selections_Nil  ::   T_Selections 
sem_Selections_Nil  = T_Selections (lift st50) where
   st50 =
         let
             v49 :: T_Selections_v49 
             v49 = \ (T_Selections_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule875  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule876  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule877  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule878  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule879  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule880  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule881  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule882  Void
                           lcopy = rule883  Void
                           alhsOcopy :: Selections
                           alhsOcopy = rule884 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule885 alhsIgraph
                           ag__result_ = T_Selections_vOut49 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_Selections_s50 v49
   rule875 = \  (_) ->
     False
   rule876 = \  (_) ->
     Nothing
   rule877 = \  (_) ->
     Nothing
   rule878 = \  (_) ->
     empty
   rule879 = \  (_) ->
     []
   rule880 = \  (_) ->
     empty
   rule881 = \  (_) ->
     []
   rule882 = \  (_) ->
     False
   rule883 = \  (_) ->
     []
   rule884 = \ lcopy ->
     lcopy
   rule885 = \ ((alhsIgraph)) ->
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
recNode_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
recNode_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppDebugs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppDebug_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppAgs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppAg_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
mSymbolType_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe SymbolType)
mSymbolType_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
mFunDef_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe GFunDef)
mFunDef_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
mExitId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mExitId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
mEntryId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mEntryId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
isInfix_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isInfix_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
isCurrTask_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isCurrTask_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
ident_Syn_SymbIdent :: Syn_SymbIdent -> (String)
ident_Syn_SymbIdent (Syn_SymbIdent _ _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
hasRecs_Syn_SymbIdent (Syn_SymbIdent _ _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_SymbIdent :: Syn_SymbIdent -> (GinGraph)
graph_Syn_SymbIdent (Syn_SymbIdent _ x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_SymbIdent :: Syn_SymbIdent -> (SymbIdent)
copy_Syn_SymbIdent (Syn_SymbIdent x _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_SymbIdent :: T_SymbIdent  Inh_SymbIdent  -> (Syn_SymbIdent )
wrap_SymbIdent (T_SymbIdent act) (Inh_SymbIdent alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_SymbIdent_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbIdent_s53 sem arg) >>= \ (T_SymbIdent_vOut52 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_SymbIdent alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
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
             v52 :: T_SymbIdent_v52 
             v52 = \ (T_SymbIdent_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           st_symb_identX44 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_symb_ident_))
                           (T_Ident_vOut43 asymb_identIcopy asymb_identIgraph asymb_identIhasRecs asymb_identIident asymb_identImEntryId asymb_identImExitId asymb_identIppAg asymb_identIppAgs asymb_identIppDebug asymb_identIppDebugs asymb_identIrecNode) = inv_Ident_s44 st_symb_identX44 (T_Ident_vIn43 asymb_identOcaseExpr asymb_identOcurrTaskName asymb_identOgraph asymb_identOmergeId asymb_identOmoduleEnv)
                           alhsOmFunDef :: Maybe GFunDef
                           alhsOmFunDef = rule886 alhsImoduleEnv asymb_identIcopy
                           alhsOmSymbolType :: Maybe SymbolType
                           alhsOmSymbolType = rule887 alhsImoduleEnv asymb_identIcopy
                           lident = rule888 asymb_identIident
                           alhsOident :: String
                           alhsOident = rule889 lident
                           alhsOisCurrTask :: Bool
                           alhsOisCurrTask = rule890 alhsIcurrTaskName lident
                           alhsOisInfix :: Bool
                           alhsOisInfix = rule891 alhsImoduleEnv asymb_identIcopy asymb_identIppAg
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule892 asymb_identIppDebug
                           alhsOppAg :: Doc
                           alhsOppAg = rule893 asymb_identIppAg
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule894 asymb_identIhasRecs
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule895 asymb_identImEntryId
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule896 asymb_identImExitId
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule897 asymb_identIppAgs
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule898 asymb_identIppDebugs
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule899 asymb_identIrecNode
                           lcopy = rule900 asymb_identIcopy arg_symb_kind_
                           alhsOcopy :: SymbIdent
                           alhsOcopy = rule901 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule902 asymb_identIgraph
                           asymb_identOcaseExpr = rule903 alhsIcaseExpr
                           asymb_identOcurrTaskName = rule904 alhsIcurrTaskName
                           asymb_identOgraph = rule905 alhsIgraph
                           asymb_identOmergeId = rule906 alhsImergeId
                           asymb_identOmoduleEnv = rule907 alhsImoduleEnv
                           ag__result_ = T_SymbIdent_vOut52 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOisInfix alhsOmEntryId alhsOmExitId alhsOmFunDef alhsOmSymbolType alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_SymbIdent_s53 v52
   /*# LINE 56 "./frontend/Tonic/MkGraph.ag" #*/
   rule886 = \ ((alhsImoduleEnv)) ((asymb_identIcopy)) ->
                          /*# LINE 56 "./frontend/Tonic/MkGraph.ag" #*/
                          reifyFunDef alhsImoduleEnv asymb_identIcopy
                          /*# LINE 5457 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 57 "./frontend/Tonic/MkGraph.ag" #*/
   rule887 = \ ((alhsImoduleEnv)) ((asymb_identIcopy)) ->
                          /*# LINE 57 "./frontend/Tonic/MkGraph.ag" #*/
                          reifySymbolType alhsImoduleEnv asymb_identIcopy
                          /*# LINE 5462 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 59 "./frontend/Tonic/MkGraph.ag" #*/
   rule888 = \ ((asymb_identIident)) ->
                          /*# LINE 59 "./frontend/Tonic/MkGraph.ag" #*/
                          asymb_identIident
                          /*# LINE 5467 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 60 "./frontend/Tonic/MkGraph.ag" #*/
   rule889 = \ lident ->
                          /*# LINE 60 "./frontend/Tonic/MkGraph.ag" #*/
                          lident
                          /*# LINE 5472 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 61 "./frontend/Tonic/MkGraph.ag" #*/
   rule890 = \ ((alhsIcurrTaskName)) lident ->
                          /*# LINE 61 "./frontend/Tonic/MkGraph.ag" #*/
                          lident     == alhsIcurrTaskName
                          /*# LINE 5477 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 34 "./frontend/Tonic/Pretty.ag" #*/
   rule891 = \ ((alhsImoduleEnv)) ((asymb_identIcopy)) ((asymb_identIppAg)) ->
                                 /*# LINE 34 "./frontend/Tonic/Pretty.ag" #*/
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
                                 /*# LINE 5491 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 116 "./frontend/Tonic/Pretty.ag" #*/
   rule892 = \ ((asymb_identIppDebug)) ->
                              /*# LINE 116 "./frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppDebug
                              /*# LINE 5496 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 117 "./frontend/Tonic/Pretty.ag" #*/
   rule893 = \ ((asymb_identIppAg)) ->
                              /*# LINE 117 "./frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppAg
                              /*# LINE 5501 "frontend/Tonic/Tonic.icl"#*/
   rule894 = \ ((asymb_identIhasRecs)) ->
     asymb_identIhasRecs
   rule895 = \ ((asymb_identImEntryId)) ->
     asymb_identImEntryId
   rule896 = \ ((asymb_identImExitId)) ->
     asymb_identImExitId
   rule897 = \ ((asymb_identIppAgs)) ->
     asymb_identIppAgs
   rule898 = \ ((asymb_identIppDebugs)) ->
     asymb_identIppDebugs
   rule899 = \ ((asymb_identIrecNode)) ->
     asymb_identIrecNode
   rule900 = \ ((asymb_identIcopy)) symb_kind_ ->
     {SymbIdent|symb_ident = asymb_identIcopy , symb_kind = symb_kind_}
   rule901 = \ lcopy ->
     lcopy
   rule902 = \ ((asymb_identIgraph)) ->
     asymb_identIgraph
   rule903 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule904 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule905 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule906 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule907 = \ ((alhsImoduleEnv)) ->
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
recNode_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppDebugs_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_SymbolType :: Syn_SymbolType -> (Doc)
ppDebug_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_SymbolType :: Syn_SymbolType -> ([Doc])
ppAgs_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_SymbolType :: Syn_SymbolType -> (Doc)
ppAg_Syn_SymbolType (Syn_SymbolType _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
mExitId_Syn_SymbolType (Syn_SymbolType _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_SymbolType :: Syn_SymbolType -> (Maybe Int)
mEntryId_Syn_SymbolType (Syn_SymbolType _ _ _ x _ _ _ _ _ _) = x
hasRecs_Syn_SymbolType :: Syn_SymbolType -> (Bool)
hasRecs_Syn_SymbolType (Syn_SymbolType _ _ x _ _ _ _ _ _ _) = x
graph_Syn_SymbolType :: Syn_SymbolType -> (GinGraph)
graph_Syn_SymbolType (Syn_SymbolType _ x _ _ _ _ _ _ _ _) = x
copy_Syn_SymbolType :: Syn_SymbolType -> (SymbolType)
copy_Syn_SymbolType (Syn_SymbolType x _ _ _ _ _ _ _ _ _) = x
wrap_SymbolType :: T_SymbolType  Inh_SymbolType  -> (Syn_SymbolType )
wrap_SymbolType (T_SymbolType act) (Inh_SymbolType alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_SymbolType_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbolType_s56 sem arg) >>= \ (T_SymbolType_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_SymbolType alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
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
             v55 :: T_SymbolType_v55 
             v55 = \ (T_SymbolType_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                       let
                           alhsOhasRecs :: Bool
                           alhsOhasRecs = rule908  Void
                           alhsOmEntryId :: Maybe Int
                           alhsOmEntryId = rule909  Void
                           alhsOmExitId :: Maybe Int
                           alhsOmExitId = rule910  Void
                           alhsOppAg :: Doc
                           alhsOppAg = rule911  Void
                           alhsOppAgs :: [Doc]
                           alhsOppAgs = rule912  Void
                           alhsOppDebug :: Doc
                           alhsOppDebug = rule913  Void
                           alhsOppDebugs :: [Doc]
                           alhsOppDebugs = rule914  Void
                           alhsOrecNode :: Bool
                           alhsOrecNode = rule915  Void
                           lcopy = rule916 arg_st_args_ arg_st_args_strictness_ arg_st_arity_ arg_st_attr_env_ arg_st_attr_vars_ arg_st_context_ arg_st_result_ arg_st_vars_
                           alhsOcopy :: SymbolType
                           alhsOcopy = rule917 lcopy
                           alhsOgraph :: GinGraph
                           alhsOgraph = rule918 alhsIgraph
                           ag__result_ = T_SymbolType_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_ )
         in C_SymbolType_s56 v55
   rule908 = \  (_) ->
     False
   rule909 = \  (_) ->
     Nothing
   rule910 = \  (_) ->
     Nothing
   rule911 = \  (_) ->
     empty
   rule912 = \  (_) ->
     []
   rule913 = \  (_) ->
     empty
   rule914 = \  (_) ->
     []
   rule915 = \  (_) ->
     False
   rule916 = \ st_args_ st_args_strictness_ st_arity_ st_attr_env_ st_attr_vars_ st_context_ st_result_ st_vars_ ->
     {SymbolType|st_vars = st_vars_ , st_args = st_args_ , st_args_strictness = st_args_strictness_ , st_arity = st_arity_ , st_result = st_result_ , st_context = st_context_ , st_attr_vars = st_attr_vars_ , st_attr_env = st_attr_env_}
   rule917 = \ lcopy ->
     lcopy
   rule918 = \ ((alhsIgraph)) ->
     alhsIgraph
