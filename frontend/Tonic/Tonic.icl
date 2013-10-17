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
from Data.Functor import class Functor (..)
import Data.List

import Data.Graph
import Data.Maybe
import Text.PPrint
import Tonic.AbsSyn
import Tonic.Util
import StdDebug
import _SystemArray

from syntax import :: Optional (..), :: FunDef {..}, :: DclModule {..},
  :: IclModule {..}, :: ForeignExport, :: ImportedObject, :: QualifiedDeclaration,
  :: Declaration, :: IclFunctionIndices, :: ModuleIdent,
  :: FunInfo, :: FunKind, :: FunctionBody {..}, :: TransformedBody {..},
  :: CheckedBody, :: ParsedBody, :: AType {..}, :: TypeAttribute, :: Type {..},
  :: TypeKind, :: TempVarId, :: ATypeVar, :: BasicType, :: ConsVariable,
  :: TypeSymbIdent {..}, :: TypeSymbProperties, :: NumberSet, :: ModuleKind,
  :: Declarations, :: DictionaryInfo, :: CommonDefs, :: IndexRange
// 36 "frontend/Tonic/Tonic.icl"

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
// 57 "frontend/Tonic/Tonic.icl"

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

import qualified Data.Maybe as Data.Maybe
import Tonic.AbsSyn
// 77 "frontend/Tonic/Tonic.icl"
from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// 308 "./frontend/Tonic/MkGraph.ag"


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

instance Functor Optional where
  fmap _ No      = No
  fmap f (Yes x) = Yes $ f x
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
// 182 "frontend/Tonic/Tonic.icl"

// 145 "./frontend/Tonic/Pretty.ag"

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
// 283 "frontend/Tonic/Tonic.icl"
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
secondArgRecNode_Syn_App :: Syn_App -> (Bool)
secondArgRecNode_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
secondArgMExitId_Syn_App :: Syn_App -> (Maybe Int)
secondArgMExitId_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
secondArgMEntryId_Syn_App :: Syn_App -> (Maybe Int)
secondArgMEntryId_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
secondArgIdent_Syn_App :: Syn_App -> (String)
secondArgIdent_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
secondArgHasRecs_Syn_App :: Syn_App -> (Bool)
secondArgHasRecs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
secondArgGraph_Syn_App :: Syn_App -> (GinGraph)
secondArgGraph_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
secondArg_Syn_App :: Syn_App -> (MaybeExpression)
secondArg_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
recNode_Syn_App :: Syn_App -> (Bool)
recNode_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
ppDebugs_Syn_App :: Syn_App -> ([Doc])
ppDebugs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
ppDebug_Syn_App :: Syn_App -> (Doc)
ppDebug_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
ppAgs_Syn_App :: Syn_App -> ([Doc])
ppAgs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
ppAg_Syn_App :: Syn_App -> (Doc)
ppAg_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
mExitId_Syn_App :: Syn_App -> (Maybe Int)
mExitId_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
mEntryId_Syn_App :: Syn_App -> (Maybe Int)
mEntryId_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_App :: Syn_App -> (Bool)
hasRecs_Syn_App (Syn_App _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_App :: Syn_App -> (GinGraph)
graph_Syn_App (Syn_App _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgRecNode_Syn_App :: Syn_App -> (Bool)
firstArgRecNode_Syn_App (Syn_App _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgMExitId_Syn_App :: Syn_App -> (Maybe Int)
firstArgMExitId_Syn_App (Syn_App _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgMEntryId_Syn_App :: Syn_App -> (Maybe Int)
firstArgMEntryId_Syn_App (Syn_App _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgIdent_Syn_App :: Syn_App -> (String)
firstArgIdent_Syn_App (Syn_App _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgHasRecs_Syn_App :: Syn_App -> (Bool)
firstArgHasRecs_Syn_App (Syn_App _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgGraph_Syn_App :: Syn_App -> (GinGraph)
firstArgGraph_Syn_App (Syn_App _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArg_Syn_App :: Syn_App -> (MaybeExpression)
firstArg_Syn_App (Syn_App _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_App :: Syn_App -> (App)
copy_Syn_App (Syn_App x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_App :: T_App  Inh_App  -> (Syn_App )
wrap_App (T_App act) (Inh_App alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_App_s2 sem arg) >>= \ (T_App_vOut1 alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode) ->
     lift (Syn_App alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode)
   )

// cata
sem_App :: App  -> T_App 
sem_App { App | app_symb = app_symb_,app_args = app_args_,app_info_ptr = app_info_ptr_ } = sem_App_App ( sem_SymbIdent app_symb_ ) ( sem_Expressions app_args_ ) app_info_ptr_ 

// semantic domain
:: T_App  = T_App (Identity (T_App_s2 ))
attach_T_App (T_App t_App) = t_App
inv_App_s2 (C_App_s2 x) = x
sem_App_App  :: (T_SymbIdent ) (T_Expressions ) (ExprInfoPtr)  -> T_App 
sem_App_App arg_app_symb_ arg_app_args_ arg_app_info_ptr_  = T_App (lift st2) where
   st2 =
        let
            v1 (T_App_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          st_app_symbX62 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_app_symb_))
                          st_app_argsX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_app_args_))
                          st_foobarX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression foobar_val_)))
                          (T_SymbIdent_vOut61 aapp_symbIcopy aapp_symbIgraph aapp_symbIhasRecs aapp_symbIident aapp_symbIisCurrTask aapp_symbImEntryId aapp_symbImExitId aapp_symbIppAg aapp_symbIppAgs aapp_symbIppDebug aapp_symbIppDebugs aapp_symbIrecNode) = inv_SymbIdent_s62 st_app_symbX62 (T_SymbIdent_vIn61 aapp_symbOcaseExpr aapp_symbOcurrTaskName aapp_symbOgraph aapp_symbOmergeId aapp_symbOmoduleEnv)
                          (T_Expressions_vOut16 aapp_argsIcopy aapp_argsIfirstArg aapp_argsIfirstArgGraph aapp_argsIfirstArgHasRecs aapp_argsIfirstArgIdent aapp_argsIfirstArgMEntryId aapp_argsIfirstArgMExitId aapp_argsIfirstArgRecNode aapp_argsIgraph aapp_argsIhasRecs aapp_argsImEntryId aapp_argsImExitId aapp_argsIppAg aapp_argsIppAgs aapp_argsIppDebug aapp_argsIppDebugs aapp_argsIppInfix aapp_argsIppPrefix aapp_argsIppTail aapp_argsIrecNode aapp_argsIsecondArg aapp_argsIsecondArgGraph aapp_argsIsecondArgHasRecs aapp_argsIsecondArgIdent aapp_argsIsecondArgMEntryId aapp_argsIsecondArgMExitId aapp_argsIsecondArgRecNode) = inv_Expressions_s17 st_app_argsX17 (T_Expressions_vIn16 aapp_argsOappSymbDoc aapp_argsOcaseExpr aapp_argsOcurrTaskName aapp_argsOgraph aapp_argsOmergeId aapp_argsOmoduleEnv aapp_argsOnumContexts)
                          (T_Expression_vOut13 afoobarIcopy afoobarIgraph afoobarIhasRecs afoobarImEntryId afoobarImExitId afoobarIppAg afoobarIppAgs afoobarIppDebug afoobarIppDebugs afoobarIrecNode) = inv_Expression_s14 st_foobarX14 (T_Expression_vIn13 afoobarOcaseExpr afoobarOcurrTaskName afoobarOgraph afoobarOmergeId afoobarOmoduleEnv)
                          aapp_argsOnumContexts = rule0 aapp_symbIident alhsImoduleEnv lisListApp
                          alhsOfirstArg = rule1 lfirstArg
                          lfirstArg = rule2 aapp_argsIfirstArg
                          alhsOsecondArg = rule3 lsecondArg
                          lsecondArg = rule4 aapp_argsIfirstArg
                          alhsOgraph = rule5 aapp_symbIident alhsIgraph alhsImoduleEnv ltaskGraph
                          alhsOmEntryId = rule6 ltaskEntryId
                          alhsOmExitId = rule7 ltaskExitId
                          (ltaskGraph,ltaskEntryId,ltaskExitId) = rule8 aapp_symbIident lassignGraph lassignId lbinAppGraph lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId
                          lisListApp = rule9 aapp_symbIident
                          lbindRhsAppIdent = rule10 aapp_argsIfirstArg
                          lbindRhsSymbolType = rule11 alhsImoduleEnv lbindRhsAppIdent
                          foobar_val_ = rule12  Void
                          (lreturnId,lreturnGraph) = rule13  Void
                          lbinAppGraph = rule14  Void
                          (lassignId,lassignGraph) = rule15  Void
                          lstepGraph = rule16  Void
                          lstepEntryId = rule17  Void
                          lstepExitId = rule18  Void
                          lparBinAppGraph = rule19  Void
                          lparListAppGraph = rule20  Void
                          lparListAppEntryId = rule21  Void
                          lparListAppExitId = rule22  Void
                          (ltaskAppId,ltaskAppGraph) = rule23 aapp_argsIppAgs aapp_symbIident aapp_symbIisCurrTask alhsIgraph
                          alhsOppDebug = rule24 aapp_argsIppAgs aapp_symbIppAg
                          alhsOppAg = rule25 aapp_argsIppInfix aapp_argsIppPrefix aapp_symbIident alhsImoduleEnv
                          aapp_argsOappSymbDoc = rule26 aapp_symbIppAg
                          alhsOfirstArgHasRecs = rule27 aapp_argsIfirstArgHasRecs
                          alhsOfirstArgMEntryId = rule28 aapp_argsIfirstArgMEntryId
                          alhsOfirstArgMExitId = rule29 aapp_argsIfirstArgMExitId
                          alhsOfirstArgRecNode = rule30 aapp_argsIfirstArgRecNode
                          alhsOhasRecs = rule31 aapp_argsIhasRecs aapp_symbIhasRecs afoobarIhasRecs
                          alhsOppAgs = rule32 aapp_argsIppAgs aapp_symbIppAgs afoobarIppAgs
                          alhsOppDebugs = rule33 aapp_argsIppDebugs aapp_symbIppDebugs afoobarIppDebugs
                          alhsOrecNode = rule34 aapp_argsIrecNode aapp_symbIrecNode afoobarIrecNode
                          alhsOsecondArgHasRecs = rule35 aapp_argsIsecondArgHasRecs
                          alhsOsecondArgMEntryId = rule36 aapp_argsIsecondArgMEntryId
                          alhsOsecondArgMExitId = rule37 aapp_argsIsecondArgMExitId
                          alhsOsecondArgRecNode = rule38 aapp_argsIsecondArgRecNode
                          lcopy = rule39 aapp_argsIcopy aapp_symbIcopy arg_app_info_ptr_
                          alhsOcopy = rule40 lcopy
                          alhsOfirstArgGraph = rule41 aapp_argsIfirstArgGraph
                          alhsOfirstArgIdent = rule42 aapp_argsIfirstArgIdent
                          alhsOsecondArgGraph = rule43 aapp_argsIsecondArgGraph
                          alhsOsecondArgIdent = rule44 aapp_argsIsecondArgIdent
                          aapp_symbOcaseExpr = rule45 alhsIcaseExpr
                          aapp_symbOcurrTaskName = rule46 alhsIcurrTaskName
                          aapp_symbOgraph = rule47 alhsIgraph
                          aapp_symbOmergeId = rule48 alhsImergeId
                          aapp_symbOmoduleEnv = rule49 alhsImoduleEnv
                          aapp_argsOcaseExpr = rule50 alhsIcaseExpr
                          aapp_argsOcurrTaskName = rule51 alhsIcurrTaskName
                          aapp_argsOgraph = rule52 aapp_symbIgraph
                          aapp_argsOmergeId = rule53 alhsImergeId
                          aapp_argsOmoduleEnv = rule54 alhsImoduleEnv
                          afoobarOcaseExpr = rule55 alhsIcaseExpr
                          afoobarOcurrTaskName = rule56 alhsIcurrTaskName
                          afoobarOgraph = rule57 aapp_argsIgraph
                          afoobarOmergeId = rule58 alhsImergeId
                          afoobarOmoduleEnv = rule59 alhsImoduleEnv
                          ag__result_ = T_App_vOut1 alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode
                      in ag__result_
        in C_App_s2 v1
   /*# LINE 129 "./frontend/Tonic/MkGraph.ag" #*/
   rule0 ((aapp_symbIident)) ((alhsImoduleEnv)) lisListApp =
                               /*# LINE 129 "./frontend/Tonic/MkGraph.ag" #*/
                               if lisListApp     0
                               (let funTy  = fromMaybe (abort err) (reifySymbolType alhsImoduleEnv aapp_symbIident)
                                    err    = "numContexts : failed to find symbol type for " +++ aapp_symbIident
                                in  numContexts funTy)
                               /*# LINE 443 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 134 "./frontend/Tonic/MkGraph.ag" #*/
   rule1 lfirstArg =
                        /*# LINE 134 "./frontend/Tonic/MkGraph.ag" #*/
                        lfirstArg
                        /*# LINE 448 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 135 "./frontend/Tonic/MkGraph.ag" #*/
   rule2 ((aapp_argsIfirstArg)) =
                        /*# LINE 135 "./frontend/Tonic/MkGraph.ag" #*/
                        aapp_argsIfirstArg
                        /*# LINE 453 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 136 "./frontend/Tonic/MkGraph.ag" #*/
   rule3 lsecondArg =
                        /*# LINE 136 "./frontend/Tonic/MkGraph.ag" #*/
                        lsecondArg
                        /*# LINE 458 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 137 "./frontend/Tonic/MkGraph.ag" #*/
   rule4 ((aapp_argsIfirstArg)) =
                        /*# LINE 137 "./frontend/Tonic/MkGraph.ag" #*/
                        aapp_argsIfirstArg
                        /*# LINE 463 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 139 "./frontend/Tonic/MkGraph.ag" #*/
   rule5 ((aapp_symbIident)) ((alhsIgraph)) ((alhsImoduleEnv)) ltaskGraph =
                    /*# LINE 139 "./frontend/Tonic/MkGraph.ag" #*/
                    if (trace_n ("App.graph.symb:" +++ aapp_symbIident) $ identIsTask alhsImoduleEnv aapp_symbIident)
                      ltaskGraph
                      alhsIgraph
                    /*# LINE 470 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 142 "./frontend/Tonic/MkGraph.ag" #*/
   rule6 ltaskEntryId =
                       /*# LINE 142 "./frontend/Tonic/MkGraph.ag" #*/
                       ltaskEntryId
                       /*# LINE 475 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 143 "./frontend/Tonic/MkGraph.ag" #*/
   rule7 ltaskExitId =
                       /*# LINE 143 "./frontend/Tonic/MkGraph.ag" #*/
                       ltaskExitId
                       /*# LINE 480 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 146 "./frontend/Tonic/MkGraph.ag" #*/
   rule8 ((aapp_symbIident)) lassignGraph lassignId lbinAppGraph lparBinAppGraph lparListAppEntryId lparListAppExitId lparListAppGraph lreturnGraph lreturnId lstepEntryId lstepExitId lstepGraph ltaskAppGraph ltaskAppId =
                /*# LINE 146 "./frontend/Tonic/MkGraph.ag" #*/
                case aapp_symbIident of
                  "return"    -> trace_n "App: return"    $ (lreturnGraph    ,                  Just lreturnId    ,                 Just lreturnId    )
                  ">>|"       -> trace_n "App: >>|"       $ (lbinAppGraph     Nothing,          Nothing,                            Nothing)
                  "@:"        -> trace_n "App: @:"        $ (lassignGraph    ,                  Just lassignId    ,                 Just lassignId    )
                  ">>*"       -> trace_n "App: >>*"       $ (lstepGraph    ,                    lstepEntryId    ,                   lstepExitId    )
                  "-||-"      -> trace_n "App: -||-"      $ (lparBinAppGraph     DisFirstBin,   Nothing,                            Nothing)
                  "||-"       -> trace_n "App: ||-"       $ (lparBinAppGraph     DisRight,      Nothing,                            Nothing)
                  "-||"       -> trace_n "App: -||"       $ (lparBinAppGraph     DisLeft,       Nothing,                            Nothing)
                  "-&&-"      -> trace_n "App: -&&-"      $ (lparBinAppGraph     ConPair,       Nothing,                            Nothing)
                  "anyTask"   -> trace_n "App: anyTask"   $ (lparListAppGraph     DisFirstList, lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                  "allTasks"  -> trace_n "App: allTasks"  $ (lparListAppGraph     ConAll,       lparListAppEntryId     DisFirstBin, lparListAppExitId     DisFirstBin)
                  _           -> trace_n "App: _"         $ (ltaskAppGraph    ,                 ltaskAppId    ,                     ltaskAppId    )
                /*# LINE 496 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 160 "./frontend/Tonic/MkGraph.ag" #*/
   rule9 ((aapp_symbIident)) =
                        /*# LINE 160 "./frontend/Tonic/MkGraph.ag" #*/
                        aapp_symbIident == "_Cons" || aapp_symbIident == "_Nil"
                        /*# LINE 501 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 167 "./frontend/Tonic/MkGraph.ag" #*/
   rule10 ((aapp_argsIfirstArg)) =
                              /*# LINE 167 "./frontend/Tonic/MkGraph.ag" #*/
                              case aapp_argsIfirstArg of
                                Just (App a)  -> a.app_symb.symb_ident.id_name
                                _             -> abort "Invalid bind"
                              /*# LINE 508 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 171 "./frontend/Tonic/MkGraph.ag" #*/
   rule11 ((alhsImoduleEnv)) lbindRhsAppIdent =
                                /*# LINE 171 "./frontend/Tonic/MkGraph.ag" #*/
                                fromMaybe (abort "mkGraphAlg #2: failed to find symbol type")
                                (reifySymbolType alhsImoduleEnv lbindRhsAppIdent    )
                                /*# LINE 514 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 174 "./frontend/Tonic/MkGraph.ag" #*/
   rule12  (_) =
                      /*# LINE 174 "./frontend/Tonic/MkGraph.ag" #*/
                      Var { BoundVar | var_ident = {Ident | id_name = "", id_info = abort "This should _not_ be evaluated 1" }
                                     , var_info_ptr = abort "This should _not_ be evaluated 2"
                                     , var_expr_ptr = abort "This should _not_ be evaluated 3" }
                      /*# LINE 521 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 198 "./frontend/Tonic/MkGraph.ag" #*/
   rule13  (_) =
                                      /*# LINE 198 "./frontend/Tonic/MkGraph.ag" #*/
                                      undef
                                      /*# LINE 526 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 211 "./frontend/Tonic/MkGraph.ag" #*/
   rule14  (_) =
                          /*# LINE 211 "./frontend/Tonic/MkGraph.ag" #*/
                          \mPat -> undef
                          /*# LINE 531 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 221 "./frontend/Tonic/MkGraph.ag" #*/
   rule15  (_) =
                                      /*# LINE 221 "./frontend/Tonic/MkGraph.ag" #*/
                                      undef
                                      /*# LINE 536 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 231 "./frontend/Tonic/MkGraph.ag" #*/
   rule16  (_) =
                          /*# LINE 231 "./frontend/Tonic/MkGraph.ag" #*/
                          abort "Step not implemented yet"
                          /*# LINE 541 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 232 "./frontend/Tonic/MkGraph.ag" #*/
   rule17  (_) =
                          /*# LINE 232 "./frontend/Tonic/MkGraph.ag" #*/
                          Nothing
                          /*# LINE 546 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 233 "./frontend/Tonic/MkGraph.ag" #*/
   rule18  (_) =
                          /*# LINE 233 "./frontend/Tonic/MkGraph.ag" #*/
                          Nothing
                          /*# LINE 551 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 240 "./frontend/Tonic/MkGraph.ag" #*/
   rule19  (_) =
                             /*# LINE 240 "./frontend/Tonic/MkGraph.ag" #*/
                             undef
                             /*# LINE 556 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 256 "./frontend/Tonic/MkGraph.ag" #*/
   rule20  (_) =
                                /*# LINE 256 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 561 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 257 "./frontend/Tonic/MkGraph.ag" #*/
   rule21  (_) =
                                /*# LINE 257 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 566 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 258 "./frontend/Tonic/MkGraph.ag" #*/
   rule22  (_) =
                                /*# LINE 258 "./frontend/Tonic/MkGraph.ag" #*/
                                \join -> undef
                                /*# LINE 571 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 265 "./frontend/Tonic/MkGraph.ag" #*/
   rule23 ((aapp_argsIppAgs)) ((aapp_symbIident)) ((aapp_symbIisCurrTask)) ((alhsIgraph)) =
                                        /*# LINE 265 "./frontend/Tonic/MkGraph.ag" #*/
                                        if aapp_symbIisCurrTask
                                          (Nothing, alhsIgraph)
                                          (let appArgs = map (GCleanExpression o ppCompact) aapp_argsIppAgs
                                               (n, g)  = addNode (GTaskApp aapp_symbIident appArgs) alhsIgraph
                                           in (Just n, g))
                                        /*# LINE 580 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 32 "./frontend/Tonic/Pretty.ag" #*/
   rule24 ((aapp_argsIppAgs)) ((aapp_symbIppAg)) =
                      /*# LINE 32 "./frontend/Tonic/Pretty.ag" #*/
                      let argsPP = hcat $ intersperse (text ", ") aapp_argsIppAgs
                      in  text "<App>" <+> aapp_symbIppAg <+> brackets argsPP
                      /*# LINE 586 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 35 "./frontend/Tonic/Pretty.ag" #*/
   rule25 ((aapp_argsIppInfix)) ((aapp_argsIppPrefix)) ((aapp_symbIident)) ((alhsImoduleEnv)) =
                      /*# LINE 35 "./frontend/Tonic/Pretty.ag" #*/
                      if (isInfix alhsImoduleEnv aapp_symbIident)
                        aapp_argsIppInfix
                        aapp_argsIppPrefix
                      /*# LINE 593 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 39 "./frontend/Tonic/Pretty.ag" #*/
   rule26 ((aapp_symbIppAg)) =
                              /*# LINE 39 "./frontend/Tonic/Pretty.ag" #*/
                              aapp_symbIppAg
                              /*# LINE 598 "frontend/Tonic/Tonic.icl"#*/
   rule27 ((aapp_argsIfirstArgHasRecs)) =
     aapp_argsIfirstArgHasRecs
   rule28 ((aapp_argsIfirstArgMEntryId)) =
     aapp_argsIfirstArgMEntryId
   rule29 ((aapp_argsIfirstArgMExitId)) =
     aapp_argsIfirstArgMExitId
   rule30 ((aapp_argsIfirstArgRecNode)) =
     aapp_argsIfirstArgRecNode
   rule31 ((aapp_argsIhasRecs)) ((aapp_symbIhasRecs)) ((afoobarIhasRecs)) =
     aapp_symbIhasRecs || aapp_argsIhasRecs || afoobarIhasRecs
   rule32 ((aapp_argsIppAgs)) ((aapp_symbIppAgs)) ((afoobarIppAgs)) =
     aapp_symbIppAgs ++ aapp_argsIppAgs ++ afoobarIppAgs
   rule33 ((aapp_argsIppDebugs)) ((aapp_symbIppDebugs)) ((afoobarIppDebugs)) =
     aapp_symbIppDebugs ++ aapp_argsIppDebugs ++ afoobarIppDebugs
   rule34 ((aapp_argsIrecNode)) ((aapp_symbIrecNode)) ((afoobarIrecNode)) =
     aapp_symbIrecNode || aapp_argsIrecNode || afoobarIrecNode
   rule35 ((aapp_argsIsecondArgHasRecs)) =
     aapp_argsIsecondArgHasRecs
   rule36 ((aapp_argsIsecondArgMEntryId)) =
     aapp_argsIsecondArgMEntryId
   rule37 ((aapp_argsIsecondArgMExitId)) =
     aapp_argsIsecondArgMExitId
   rule38 ((aapp_argsIsecondArgRecNode)) =
     aapp_argsIsecondArgRecNode
   rule39 ((aapp_argsIcopy)) ((aapp_symbIcopy)) app_info_ptr_ =
     {App|app_symb = aapp_symbIcopy , app_args = aapp_argsIcopy , app_info_ptr = app_info_ptr_}
   rule40 lcopy =
     lcopy
   rule41 ((aapp_argsIfirstArgGraph)) =
     aapp_argsIfirstArgGraph
   rule42 ((aapp_argsIfirstArgIdent)) =
     aapp_argsIfirstArgIdent
   rule43 ((aapp_argsIsecondArgGraph)) =
     aapp_argsIsecondArgGraph
   rule44 ((aapp_argsIsecondArgIdent)) =
     aapp_argsIsecondArgIdent
   rule45 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule46 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule47 ((alhsIgraph)) =
     alhsIgraph
   rule48 ((alhsImergeId)) =
     alhsImergeId
   rule49 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule50 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule51 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule52 ((aapp_symbIgraph)) =
     aapp_symbIgraph
   rule53 ((alhsImergeId)) =
     alhsImergeId
   rule54 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule55 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule56 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule57 ((aapp_argsIgraph)) =
     aapp_argsIgraph
   rule58 ((alhsImergeId)) =
     alhsImergeId
   rule59 ((alhsImoduleEnv)) =
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
:: T_BasicValue  = T_BasicValue (Identity (T_BasicValue_s5 ))
attach_T_BasicValue (T_BasicValue t_BasicValue) = t_BasicValue
inv_BasicValue_s5 (C_BasicValue_s5 x) = x
sem_BasicValue_BVI  :: (String) -> T_BasicValue 
sem_BasicValue_BVI arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule60 arg_str_
                          alhsOppAg = rule61 arg_str_
                          alhsOhasRecs = rule62  Void
                          alhsOmEntryId = rule63  Void
                          alhsOmExitId = rule64  Void
                          alhsOppAgs = rule65  Void
                          alhsOppDebugs = rule66  Void
                          alhsOrecNode = rule67  Void
                          lcopy = rule68 arg_str_
                          alhsOcopy = rule69 lcopy
                          alhsOgraph = rule70 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 102 "./frontend/Tonic/Pretty.ag" #*/
   rule60 str_ =
                        /*# LINE 102 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 744 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 103 "./frontend/Tonic/Pretty.ag" #*/
   rule61 str_ =
                        /*# LINE 103 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 749 "frontend/Tonic/Tonic.icl"#*/
   rule62  (_) =
     False
   rule63  (_) =
     Nothing
   rule64  (_) =
     Nothing
   rule65  (_) =
     []
   rule66  (_) =
     []
   rule67  (_) =
     False
   rule68 str_ =
     BVI str_
   rule69 lcopy =
     lcopy
   rule70 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVInt  :: (Int) -> T_BasicValue 
sem_BasicValue_BVInt arg_i_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule71 arg_i_
                          alhsOppAg = rule72 arg_i_
                          alhsOhasRecs = rule73  Void
                          alhsOmEntryId = rule74  Void
                          alhsOmExitId = rule75  Void
                          alhsOppAgs = rule76  Void
                          alhsOppDebugs = rule77  Void
                          alhsOrecNode = rule78  Void
                          lcopy = rule79 arg_i_
                          alhsOcopy = rule80 lcopy
                          alhsOgraph = rule81 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 104 "./frontend/Tonic/Pretty.ag" #*/
   rule71 i_ =
                          /*# LINE 104 "./frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 792 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 105 "./frontend/Tonic/Pretty.ag" #*/
   rule72 i_ =
                          /*# LINE 105 "./frontend/Tonic/Pretty.ag" #*/
                          int i_
                          /*# LINE 797 "frontend/Tonic/Tonic.icl"#*/
   rule73  (_) =
     False
   rule74  (_) =
     Nothing
   rule75  (_) =
     Nothing
   rule76  (_) =
     []
   rule77  (_) =
     []
   rule78  (_) =
     False
   rule79 i_ =
     BVInt i_
   rule80 lcopy =
     lcopy
   rule81 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVC  :: (String) -> T_BasicValue 
sem_BasicValue_BVC arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule82 arg_str_
                          alhsOppAg = rule83 arg_str_
                          alhsOhasRecs = rule84  Void
                          alhsOmEntryId = rule85  Void
                          alhsOmExitId = rule86  Void
                          alhsOppAgs = rule87  Void
                          alhsOppDebugs = rule88  Void
                          alhsOrecNode = rule89  Void
                          lcopy = rule90 arg_str_
                          alhsOcopy = rule91 lcopy
                          alhsOgraph = rule92 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 106 "./frontend/Tonic/Pretty.ag" #*/
   rule82 str_ =
                        /*# LINE 106 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 840 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 107 "./frontend/Tonic/Pretty.ag" #*/
   rule83 str_ =
                        /*# LINE 107 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 845 "frontend/Tonic/Tonic.icl"#*/
   rule84  (_) =
     False
   rule85  (_) =
     Nothing
   rule86  (_) =
     Nothing
   rule87  (_) =
     []
   rule88  (_) =
     []
   rule89  (_) =
     False
   rule90 str_ =
     BVC str_
   rule91 lcopy =
     lcopy
   rule92 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVB  :: (Bool) -> T_BasicValue 
sem_BasicValue_BVB arg_b_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule93 arg_b_
                          alhsOppAg = rule94 arg_b_
                          alhsOhasRecs = rule95  Void
                          alhsOmEntryId = rule96  Void
                          alhsOmExitId = rule97  Void
                          alhsOppAgs = rule98  Void
                          alhsOppDebugs = rule99  Void
                          alhsOrecNode = rule100  Void
                          lcopy = rule101 arg_b_
                          alhsOcopy = rule102 lcopy
                          alhsOgraph = rule103 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 108 "./frontend/Tonic/Pretty.ag" #*/
   rule93 b_ =
                        /*# LINE 108 "./frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 888 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 109 "./frontend/Tonic/Pretty.ag" #*/
   rule94 b_ =
                        /*# LINE 109 "./frontend/Tonic/Pretty.ag" #*/
                        bool b_
                        /*# LINE 893 "frontend/Tonic/Tonic.icl"#*/
   rule95  (_) =
     False
   rule96  (_) =
     Nothing
   rule97  (_) =
     Nothing
   rule98  (_) =
     []
   rule99  (_) =
     []
   rule100  (_) =
     False
   rule101 b_ =
     BVB b_
   rule102 lcopy =
     lcopy
   rule103 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVR  :: (String) -> T_BasicValue 
sem_BasicValue_BVR arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule104 arg_str_
                          alhsOppAg = rule105 arg_str_
                          alhsOhasRecs = rule106  Void
                          alhsOmEntryId = rule107  Void
                          alhsOmExitId = rule108  Void
                          alhsOppAgs = rule109  Void
                          alhsOppDebugs = rule110  Void
                          alhsOrecNode = rule111  Void
                          lcopy = rule112 arg_str_
                          alhsOcopy = rule113 lcopy
                          alhsOgraph = rule114 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 110 "./frontend/Tonic/Pretty.ag" #*/
   rule104 str_ =
                        /*# LINE 110 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 936 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 111 "./frontend/Tonic/Pretty.ag" #*/
   rule105 str_ =
                        /*# LINE 111 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 941 "frontend/Tonic/Tonic.icl"#*/
   rule106  (_) =
     False
   rule107  (_) =
     Nothing
   rule108  (_) =
     Nothing
   rule109  (_) =
     []
   rule110  (_) =
     []
   rule111  (_) =
     False
   rule112 str_ =
     BVR str_
   rule113 lcopy =
     lcopy
   rule114 ((alhsIgraph)) =
     alhsIgraph
sem_BasicValue_BVS  :: (String) -> T_BasicValue 
sem_BasicValue_BVS arg_str_ = T_BasicValue (lift st5) where
   st5 =
        let
            v4 (T_BasicValue_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          alhsOppDebug = rule115 arg_str_
                          alhsOppAg = rule116 arg_str_
                          alhsOhasRecs = rule117  Void
                          alhsOmEntryId = rule118  Void
                          alhsOmExitId = rule119  Void
                          alhsOppAgs = rule120  Void
                          alhsOppDebugs = rule121  Void
                          alhsOrecNode = rule122  Void
                          lcopy = rule123 arg_str_
                          alhsOcopy = rule124 lcopy
                          alhsOgraph = rule125 alhsIgraph
                          ag__result_ = T_BasicValue_vOut4 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BasicValue_s5 v4
   /*# LINE 112 "./frontend/Tonic/Pretty.ag" #*/
   rule115 str_ =
                        /*# LINE 112 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 984 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 113 "./frontend/Tonic/Pretty.ag" #*/
   rule116 str_ =
                        /*# LINE 113 "./frontend/Tonic/Pretty.ag" #*/
                        text str_
                        /*# LINE 989 "frontend/Tonic/Tonic.icl"#*/
   rule117  (_) =
     False
   rule118  (_) =
     Nothing
   rule119  (_) =
     Nothing
   rule120  (_) =
     []
   rule121  (_) =
     []
   rule122  (_) =
     False
   rule123 str_ =
     BVS str_
   rule124 lcopy =
     lcopy
   rule125 ((alhsIgraph)) =
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
:: T_BoundVar  = T_BoundVar (Identity (T_BoundVar_s8 ))
attach_T_BoundVar (T_BoundVar t_BoundVar) = t_BoundVar
inv_BoundVar_s8 (C_BoundVar_s8 x) = x
sem_BoundVar_BoundVar  :: (T_Ident ) (VarInfoPtr) (ExprInfoPtr) -> T_BoundVar 
sem_BoundVar_BoundVar arg_var_ident_ arg_var_info_ptr_ arg_var_expr_ptr_ = T_BoundVar (lift st8) where
   st8 =
        let
            v7 (T_BoundVar_vIn7 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                      let
                          st_var_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_var_ident_))
                          (T_Ident_vOut46 avar_identIcopy avar_identIgraph avar_identIhasRecs avar_identIident avar_identIisCurrTask avar_identImEntryId avar_identImExitId avar_identIppAg avar_identIppAgs avar_identIppDebug avar_identIppDebugs avar_identIrecNode) = inv_Ident_s47 st_var_identX47 (T_Ident_vIn46 avar_identOcaseExpr avar_identOcurrTaskName avar_identOgraph avar_identOmergeId avar_identOmoduleEnv)
                          alhsOppDebug = rule126 avar_identIppDebug
                          alhsOppAg = rule127 avar_identIppAg
                          alhsOhasRecs = rule128 avar_identIhasRecs
                          alhsOmEntryId = rule129 avar_identImEntryId
                          alhsOmExitId = rule130 avar_identImExitId
                          alhsOppAgs = rule131 avar_identIppAgs
                          alhsOppDebugs = rule132 avar_identIppDebugs
                          alhsOrecNode = rule133 avar_identIrecNode
                          lcopy = rule134 avar_identIcopy arg_var_expr_ptr_ arg_var_info_ptr_
                          alhsOcopy = rule135 lcopy
                          alhsOgraph = rule136 avar_identIgraph
                          avar_identOcaseExpr = rule137 alhsIcaseExpr
                          avar_identOcurrTaskName = rule138 alhsIcurrTaskName
                          avar_identOgraph = rule139 alhsIgraph
                          avar_identOmergeId = rule140 alhsImergeId
                          avar_identOmoduleEnv = rule141 alhsImoduleEnv
                          ag__result_ = T_BoundVar_vOut7 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                      in ag__result_
        in C_BoundVar_s8 v7
   /*# LINE 90 "./frontend/Tonic/Pretty.ag" #*/
   rule126 ((avar_identIppDebug)) =
                             /*# LINE 90 "./frontend/Tonic/Pretty.ag" #*/
                             avar_identIppDebug
                             /*# LINE 1089 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 91 "./frontend/Tonic/Pretty.ag" #*/
   rule127 ((avar_identIppAg)) =
                             /*# LINE 91 "./frontend/Tonic/Pretty.ag" #*/
                             avar_identIppAg
                             /*# LINE 1094 "frontend/Tonic/Tonic.icl"#*/
   rule128 ((avar_identIhasRecs)) =
     avar_identIhasRecs
   rule129 ((avar_identImEntryId)) =
     avar_identImEntryId
   rule130 ((avar_identImExitId)) =
     avar_identImExitId
   rule131 ((avar_identIppAgs)) =
     avar_identIppAgs
   rule132 ((avar_identIppDebugs)) =
     avar_identIppDebugs
   rule133 ((avar_identIrecNode)) =
     avar_identIrecNode
   rule134 ((avar_identIcopy)) var_expr_ptr_ var_info_ptr_ =
     {BoundVar|var_ident = avar_identIcopy , var_info_ptr = var_info_ptr_ , var_expr_ptr = var_expr_ptr_}
   rule135 lcopy =
     lcopy
   rule136 ((avar_identIgraph)) =
     avar_identIgraph
   rule137 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule138 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule139 ((alhsIgraph)) =
     alhsIgraph
   rule140 ((alhsImergeId)) =
     alhsImergeId
   rule141 ((alhsImoduleEnv)) =
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
:: T_DefinedSymbol  = T_DefinedSymbol (Identity (T_DefinedSymbol_s11 ))
attach_T_DefinedSymbol (T_DefinedSymbol t_DefinedSymbol) = t_DefinedSymbol
inv_DefinedSymbol_s11 (C_DefinedSymbol_s11 x) = x
sem_DefinedSymbol_DefinedSymbol  :: (T_Ident ) (Int) (Index) -> T_DefinedSymbol 
sem_DefinedSymbol_DefinedSymbol arg_ds_ident_ arg_ds_arity_ arg_ds_index_ = T_DefinedSymbol (lift st11) where
   st11 =
         let
             v10 (T_DefinedSymbol_vIn10 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_ds_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ds_ident_))
                           (T_Ident_vOut46 ads_identIcopy ads_identIgraph ads_identIhasRecs ads_identIident ads_identIisCurrTask ads_identImEntryId ads_identImExitId ads_identIppAg ads_identIppAgs ads_identIppDebug ads_identIppDebugs ads_identIrecNode) = inv_Ident_s47 st_ds_identX47 (T_Ident_vIn46 ads_identOcaseExpr ads_identOcurrTaskName ads_identOgraph ads_identOmergeId ads_identOmoduleEnv)
                           alhsOppDebug = rule142 ads_identIppDebug
                           alhsOppAg = rule143 ads_identIppAg
                           alhsOhasRecs = rule144 ads_identIhasRecs
                           alhsOmEntryId = rule145 ads_identImEntryId
                           alhsOmExitId = rule146 ads_identImExitId
                           alhsOppAgs = rule147 ads_identIppAgs
                           alhsOppDebugs = rule148 ads_identIppDebugs
                           alhsOrecNode = rule149 ads_identIrecNode
                           lcopy = rule150 ads_identIcopy arg_ds_arity_ arg_ds_index_
                           alhsOcopy = rule151 lcopy
                           alhsOgraph = rule152 ads_identIgraph
                           ads_identOcaseExpr = rule153 alhsIcaseExpr
                           ads_identOcurrTaskName = rule154 alhsIcurrTaskName
                           ads_identOgraph = rule155 alhsIgraph
                           ads_identOmergeId = rule156 alhsImergeId
                           ads_identOmoduleEnv = rule157 alhsImoduleEnv
                           ag__result_ = T_DefinedSymbol_vOut10 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_DefinedSymbol_s11 v10
   /*# LINE 116 "./frontend/Tonic/Pretty.ag" #*/
   rule142 ((ads_identIppDebug)) =
                                  /*# LINE 116 "./frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppDebug
                                  /*# LINE 1204 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 117 "./frontend/Tonic/Pretty.ag" #*/
   rule143 ((ads_identIppAg)) =
                                  /*# LINE 117 "./frontend/Tonic/Pretty.ag" #*/
                                  ads_identIppAg
                                  /*# LINE 1209 "frontend/Tonic/Tonic.icl"#*/
   rule144 ((ads_identIhasRecs)) =
     ads_identIhasRecs
   rule145 ((ads_identImEntryId)) =
     ads_identImEntryId
   rule146 ((ads_identImExitId)) =
     ads_identImExitId
   rule147 ((ads_identIppAgs)) =
     ads_identIppAgs
   rule148 ((ads_identIppDebugs)) =
     ads_identIppDebugs
   rule149 ((ads_identIrecNode)) =
     ads_identIrecNode
   rule150 ((ads_identIcopy)) ds_arity_ ds_index_ =
     {DefinedSymbol|ds_ident = ads_identIcopy , ds_arity = ds_arity_ , ds_index = ds_index_}
   rule151 lcopy =
     lcopy
   rule152 ((ads_identIgraph)) =
     ads_identIgraph
   rule153 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule154 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule155 ((alhsIgraph)) =
     alhsIgraph
   rule156 ((alhsImergeId)) =
     alhsImergeId
   rule157 ((alhsImoduleEnv)) =
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
:: T_Expression  = T_Expression (Identity (T_Expression_s14 ))
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
                           alhsOppDebug = rule158 abvIppDebug
                           alhsOppAg = rule159 abvIppAg
                           alhsOhasRecs = rule160 abvIhasRecs
                           alhsOmEntryId = rule161 abvImEntryId
                           alhsOmExitId = rule162 abvImExitId
                           alhsOppAgs = rule163 abvIppAgs
                           alhsOppDebugs = rule164 abvIppDebugs
                           alhsOrecNode = rule165 abvIrecNode
                           lcopy = rule166 abvIcopy
                           alhsOcopy = rule167 lcopy
                           alhsOgraph = rule168 abvIgraph
                           abvOcaseExpr = rule169 alhsIcaseExpr
                           abvOcurrTaskName = rule170 alhsIcurrTaskName
                           abvOgraph = rule171 alhsIgraph
                           abvOmergeId = rule172 alhsImergeId
                           abvOmoduleEnv = rule173 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 57 "./frontend/Tonic/Pretty.ag" #*/
   rule158 ((abvIppDebug)) =
                      /*# LINE 57 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Var>" <+> abvIppDebug
                      /*# LINE 1343 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 58 "./frontend/Tonic/Pretty.ag" #*/
   rule159 ((abvIppAg)) =
                      /*# LINE 58 "./frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 1348 "frontend/Tonic/Tonic.icl"#*/
   rule160 ((abvIhasRecs)) =
     abvIhasRecs
   rule161 ((abvImEntryId)) =
     abvImEntryId
   rule162 ((abvImExitId)) =
     abvImExitId
   rule163 ((abvIppAgs)) =
     abvIppAgs
   rule164 ((abvIppDebugs)) =
     abvIppDebugs
   rule165 ((abvIrecNode)) =
     abvIrecNode
   rule166 ((abvIcopy)) =
     Var abvIcopy
   rule167 lcopy =
     lcopy
   rule168 ((abvIgraph)) =
     abvIgraph
   rule169 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule170 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule171 ((alhsIgraph)) =
     alhsIgraph
   rule172 ((alhsImergeId)) =
     alhsImergeId
   rule173 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_App  :: (T_App ) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_appX2 = 'Control.Monad.Identity'.runIdentity (attach_T_App (arg_app_))
                           (T_App_vOut1 aappIcopy aappIfirstArg aappIfirstArgGraph aappIfirstArgHasRecs aappIfirstArgIdent aappIfirstArgMEntryId aappIfirstArgMExitId aappIfirstArgRecNode aappIgraph aappIhasRecs aappImEntryId aappImExitId aappIppAg aappIppAgs aappIppDebug aappIppDebugs aappIrecNode aappIsecondArg aappIsecondArgGraph aappIsecondArgHasRecs aappIsecondArgIdent aappIsecondArgMEntryId aappIsecondArgMExitId aappIsecondArgRecNode) = inv_App_s2 st_appX2 (T_App_vIn1 aappOcaseExpr aappOcurrTaskName aappOgraph aappOmergeId aappOmoduleEnv)
                           alhsOgraph = rule174 aappIgraph
                           alhsOppDebug = rule175 aappIppDebug
                           alhsOppAg = rule176 aappIppAg
                           alhsOhasRecs = rule177 aappIhasRecs
                           alhsOmEntryId = rule178 aappImEntryId
                           alhsOmExitId = rule179 aappImExitId
                           alhsOppAgs = rule180 aappIppAgs
                           alhsOppDebugs = rule181 aappIppDebugs
                           alhsOrecNode = rule182 aappIrecNode
                           lcopy = rule183 aappIcopy
                           alhsOcopy = rule184 lcopy
                           aappOcaseExpr = rule185 alhsIcaseExpr
                           aappOcurrTaskName = rule186 alhsIcurrTaskName
                           aappOgraph = rule187 alhsIgraph
                           aappOmergeId = rule188 alhsImergeId
                           aappOmoduleEnv = rule189 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 273 "./frontend/Tonic/MkGraph.ag" #*/
   rule174 ((aappIgraph)) =
                    /*# LINE 273 "./frontend/Tonic/MkGraph.ag" #*/
                    aappIgraph
                    /*# LINE 1408 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 60 "./frontend/Tonic/Pretty.ag" #*/
   rule175 ((aappIppDebug)) =
                        /*# LINE 60 "./frontend/Tonic/Pretty.ag" #*/
                        aappIppDebug
                        /*# LINE 1413 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 61 "./frontend/Tonic/Pretty.ag" #*/
   rule176 ((aappIppAg)) =
                        /*# LINE 61 "./frontend/Tonic/Pretty.ag" #*/
                        aappIppAg
                        /*# LINE 1418 "frontend/Tonic/Tonic.icl"#*/
   rule177 ((aappIhasRecs)) =
     aappIhasRecs
   rule178 ((aappImEntryId)) =
     aappImEntryId
   rule179 ((aappImExitId)) =
     aappImExitId
   rule180 ((aappIppAgs)) =
     aappIppAgs
   rule181 ((aappIppDebugs)) =
     aappIppDebugs
   rule182 ((aappIrecNode)) =
     aappIrecNode
   rule183 ((aappIcopy)) =
     App aappIcopy
   rule184 lcopy =
     lcopy
   rule185 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule186 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule187 ((alhsIgraph)) =
     alhsIgraph
   rule188 ((alhsImergeId)) =
     alhsImergeId
   rule189 ((alhsImoduleEnv)) =
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
                           (T_Expressions_vOut16 aexprsIcopy aexprsIfirstArg aexprsIfirstArgGraph aexprsIfirstArgHasRecs aexprsIfirstArgIdent aexprsIfirstArgMEntryId aexprsIfirstArgMExitId aexprsIfirstArgRecNode aexprsIgraph aexprsIhasRecs aexprsImEntryId aexprsImExitId aexprsIppAg aexprsIppAgs aexprsIppDebug aexprsIppDebugs aexprsIppInfix aexprsIppPrefix aexprsIppTail aexprsIrecNode aexprsIsecondArg aexprsIsecondArgGraph aexprsIsecondArgHasRecs aexprsIsecondArgIdent aexprsIsecondArgMEntryId aexprsIsecondArgMExitId aexprsIsecondArgRecNode) = inv_Expressions_s17 st_exprsX17 (T_Expressions_vIn16 aexprsOappSymbDoc aexprsOcaseExpr aexprsOcurrTaskName aexprsOgraph aexprsOmergeId aexprsOmoduleEnv aexprsOnumContexts)
                           alhsOhasRecs = rule190 aexprIhasRecs aexprsIhasRecs
                           alhsOmEntryId = rule191 aexprImEntryId aexprsImEntryId
                           alhsOmExitId = rule192 aexprImExitId aexprsImExitId
                           alhsOppAg = rule193 aexprIppAg aexprsIppAg
                           alhsOppAgs = rule194 aexprIppAgs aexprsIppAgs
                           alhsOppDebug = rule195 aexprIppDebug aexprsIppDebug
                           alhsOppDebugs = rule196 aexprIppDebugs aexprsIppDebugs
                           alhsOrecNode = rule197 aexprIrecNode aexprsIrecNode
                           lcopy = rule198 aexprIcopy aexprsIcopy
                           alhsOcopy = rule199 lcopy
                           alhsOgraph = rule200 aexprsIgraph
                           aexprOcaseExpr = rule201 alhsIcaseExpr
                           aexprOcurrTaskName = rule202 alhsIcurrTaskName
                           aexprOgraph = rule203 alhsIgraph
                           aexprOmergeId = rule204 alhsImergeId
                           aexprOmoduleEnv = rule205 alhsImoduleEnv
                           aexprsOappSymbDoc = rule206  Void
                           aexprsOcaseExpr = rule207 alhsIcaseExpr
                           aexprsOcurrTaskName = rule208 alhsIcurrTaskName
                           aexprsOgraph = rule209 aexprIgraph
                           aexprsOmergeId = rule210 alhsImergeId
                           aexprsOmoduleEnv = rule211 alhsImoduleEnv
                           aexprsOnumContexts = rule212  Void
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule190 ((aexprIhasRecs)) ((aexprsIhasRecs)) =
     aexprIhasRecs || aexprsIhasRecs
   rule191 ((aexprImEntryId)) ((aexprsImEntryId)) =
     aexprImEntryId <> aexprsImEntryId
   rule192 ((aexprImExitId)) ((aexprsImExitId)) =
     aexprImExitId <> aexprsImExitId
   rule193 ((aexprIppAg)) ((aexprsIppAg)) =
     aexprIppAg <$$> aexprsIppAg
   rule194 ((aexprIppAgs)) ((aexprsIppAgs)) =
     aexprIppAgs ++ aexprsIppAgs
   rule195 ((aexprIppDebug)) ((aexprsIppDebug)) =
     aexprIppDebug <$$> aexprsIppDebug
   rule196 ((aexprIppDebugs)) ((aexprsIppDebugs)) =
     aexprIppDebugs ++ aexprsIppDebugs
   rule197 ((aexprIrecNode)) ((aexprsIrecNode)) =
     aexprIrecNode || aexprsIrecNode
   rule198 ((aexprIcopy)) ((aexprsIcopy)) =
     At aexprIcopy aexprsIcopy
   rule199 lcopy =
     lcopy
   rule200 ((aexprsIgraph)) =
     aexprsIgraph
   rule201 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule202 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule203 ((alhsIgraph)) =
     alhsIgraph
   rule204 ((alhsImergeId)) =
     alhsImergeId
   rule205 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule206  (_) =
     abort "missing rule: Expression.At.exprs.appSymbDoc"
   rule207 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule208 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule209 ((aexprIgraph)) =
     aexprIgraph
   rule210 ((alhsImergeId)) =
     alhsImergeId
   rule211 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule212  (_) =
     abort "missing rule: Expression.At.exprs.numContexts"
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Let arg_let__  = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gletX35 = 'Control.Monad.Identity'.runIdentity (attach_T_GLet ((sem_GLet glet_val_)))
                           (T_GLet_vOut34 agletIcopy agletIgraph agletIhasRecs agletImEntryId agletImExitId agletIppAg agletIppAgs agletIppDebug agletIppDebugs agletIrecNode) = inv_GLet_s35 st_gletX35 (T_GLet_vIn34 agletOcaseExpr agletOcurrTaskName agletOgraph agletOmergeId agletOmoduleEnv)
                           alhsOgraph = rule213 agletIgraph
                           glet_val_ = rule214 alhsImoduleEnv arg_let__
                           alhsOhasRecs = rule215 agletIhasRecs
                           alhsOmEntryId = rule216 agletImEntryId
                           alhsOmExitId = rule217 agletImExitId
                           alhsOppAg = rule218 agletIppAg
                           alhsOppAgs = rule219 agletIppAgs
                           alhsOppDebug = rule220 agletIppDebug
                           alhsOppDebugs = rule221 agletIppDebugs
                           alhsOrecNode = rule222 agletIrecNode
                           lcopy = rule223 arg_let__
                           alhsOcopy = rule224 lcopy
                           agletOcaseExpr = rule225 alhsIcaseExpr
                           agletOcurrTaskName = rule226 alhsIcurrTaskName
                           agletOgraph = rule227 alhsIgraph
                           agletOmergeId = rule228 alhsImergeId
                           agletOmoduleEnv = rule229 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 276 "./frontend/Tonic/MkGraph.ag" #*/
   rule213 ((agletIgraph)) =
                    /*# LINE 276 "./frontend/Tonic/MkGraph.ag" #*/
                    agletIgraph
                    /*# LINE 1559 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 279 "./frontend/Tonic/MkGraph.ag" #*/
   rule214 ((alhsImoduleEnv)) let__ =
                    /*# LINE 279 "./frontend/Tonic/MkGraph.ag" #*/
                    mkGLet alhsImoduleEnv let__
                    /*# LINE 1564 "frontend/Tonic/Tonic.icl"#*/
   rule215 ((agletIhasRecs)) =
     agletIhasRecs
   rule216 ((agletImEntryId)) =
     agletImEntryId
   rule217 ((agletImExitId)) =
     agletImExitId
   rule218 ((agletIppAg)) =
     agletIppAg
   rule219 ((agletIppAgs)) =
     agletIppAgs
   rule220 ((agletIppDebug)) =
     agletIppDebug
   rule221 ((agletIppDebugs)) =
     agletIppDebugs
   rule222 ((agletIrecNode)) =
     agletIrecNode
   rule223 let__ =
     Let let__
   rule224 lcopy =
     lcopy
   rule225 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule226 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule227 ((alhsIgraph)) =
     alhsIgraph
   rule228 ((alhsImergeId)) =
     alhsImergeId
   rule229 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Case arg_case__ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule230  Void
                           alhsOmEntryId = rule231  Void
                           alhsOmExitId = rule232  Void
                           alhsOppAg = rule233  Void
                           alhsOppAgs = rule234  Void
                           alhsOppDebug = rule235  Void
                           alhsOppDebugs = rule236  Void
                           alhsOrecNode = rule237  Void
                           lcopy = rule238 arg_case__
                           alhsOcopy = rule239 lcopy
                           alhsOgraph = rule240 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule230  (_) =
     False
   rule231  (_) =
     Nothing
   rule232  (_) =
     Nothing
   rule233  (_) =
     empty
   rule234  (_) =
     []
   rule235  (_) =
     empty
   rule236  (_) =
     []
   rule237  (_) =
     False
   rule238 case__ =
     Case case__
   rule239 lcopy =
     lcopy
   rule240 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) (T_Selections ) -> T_Expression 
sem_Expression_Selection arg_skind_ arg_expr_ arg_sels_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_selsX59 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_Selections_vOut58 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s59 st_selsX59 (T_Selections_vIn58 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           alhsOppDebug = rule241 aexprIppDebug lrecsel
                           alhsOppAg = rule242 aexprIppAg lrecsel
                           lrecsel = rule243 aselsIppAgs
                           alhsOhasRecs = rule244 aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule245 aexprImEntryId aselsImEntryId
                           alhsOmExitId = rule246 aexprImExitId aselsImExitId
                           alhsOppAgs = rule247 aexprIppAgs aselsIppAgs
                           alhsOppDebugs = rule248 aexprIppDebugs aselsIppDebugs
                           alhsOrecNode = rule249 aexprIrecNode aselsIrecNode
                           lcopy = rule250 aexprIcopy aselsIcopy arg_skind_
                           alhsOcopy = rule251 lcopy
                           alhsOgraph = rule252 aselsIgraph
                           aexprOcaseExpr = rule253 alhsIcaseExpr
                           aexprOcurrTaskName = rule254 alhsIcurrTaskName
                           aexprOgraph = rule255 alhsIgraph
                           aexprOmergeId = rule256 alhsImergeId
                           aexprOmoduleEnv = rule257 alhsImoduleEnv
                           aselsOcaseExpr = rule258 alhsIcaseExpr
                           aselsOcurrTaskName = rule259 alhsIcurrTaskName
                           aselsOgraph = rule260 aexprIgraph
                           aselsOmergeId = rule261 alhsImergeId
                           aselsOmoduleEnv = rule262 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 64 "./frontend/Tonic/Pretty.ag" #*/
   rule241 ((aexprIppDebug)) lrecsel =
                      /*# LINE 64 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Selection>" <+> aexprIppDebug <-> lrecsel
                      /*# LINE 1676 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 66 "./frontend/Tonic/Pretty.ag" #*/
   rule242 ((aexprIppAg)) lrecsel =
                      /*# LINE 66 "./frontend/Tonic/Pretty.ag" #*/
                      aexprIppAg <-> lrecsel
                      /*# LINE 1681 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 67 "./frontend/Tonic/Pretty.ag" #*/
   rule243 ((aselsIppAgs)) =
                      /*# LINE 67 "./frontend/Tonic/Pretty.ag" #*/
                      char '.' <-> hcat (intersperse (char '.') $ aselsIppAgs)
                      /*# LINE 1686 "frontend/Tonic/Tonic.icl"#*/
   rule244 ((aexprIhasRecs)) ((aselsIhasRecs)) =
     aexprIhasRecs || aselsIhasRecs
   rule245 ((aexprImEntryId)) ((aselsImEntryId)) =
     aexprImEntryId <> aselsImEntryId
   rule246 ((aexprImExitId)) ((aselsImExitId)) =
     aexprImExitId <> aselsImExitId
   rule247 ((aexprIppAgs)) ((aselsIppAgs)) =
     aexprIppAgs ++ aselsIppAgs
   rule248 ((aexprIppDebugs)) ((aselsIppDebugs)) =
     aexprIppDebugs ++ aselsIppDebugs
   rule249 ((aexprIrecNode)) ((aselsIrecNode)) =
     aexprIrecNode || aselsIrecNode
   rule250 ((aexprIcopy)) ((aselsIcopy)) skind_ =
     Selection skind_ aexprIcopy aselsIcopy
   rule251 lcopy =
     lcopy
   rule252 ((aselsIgraph)) =
     aselsIgraph
   rule253 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule254 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule255 ((alhsIgraph)) =
     alhsIgraph
   rule256 ((alhsImergeId)) =
     alhsImergeId
   rule257 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule258 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule259 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule260 ((aexprIgraph)) =
     aexprIgraph
   rule261 ((alhsImergeId)) =
     alhsImergeId
   rule262 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Update  :: (T_Expression ) (T_Selections ) (T_Expression ) -> T_Expression 
sem_Expression_Update arg_exprl_ arg_sels_ arg_exprr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprlX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprl_))
                           st_selsX59 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprrX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprr_))
                           (T_Expression_vOut13 aexprlIcopy aexprlIgraph aexprlIhasRecs aexprlImEntryId aexprlImExitId aexprlIppAg aexprlIppAgs aexprlIppDebug aexprlIppDebugs aexprlIrecNode) = inv_Expression_s14 st_exprlX14 (T_Expression_vIn13 aexprlOcaseExpr aexprlOcurrTaskName aexprlOgraph aexprlOmergeId aexprlOmoduleEnv)
                           (T_Selections_vOut58 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s59 st_selsX59 (T_Selections_vIn58 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprrIcopy aexprrIgraph aexprrIhasRecs aexprrImEntryId aexprrImExitId aexprrIppAg aexprrIppAgs aexprrIppDebug aexprrIppDebugs aexprrIrecNode) = inv_Expression_s14 st_exprrX14 (T_Expression_vIn13 aexprrOcaseExpr aexprrOcurrTaskName aexprrOgraph aexprrOmergeId aexprrOmoduleEnv)
                           alhsOppDebug = rule263  Void
                           alhsOppAg = rule264  Void
                           alhsOhasRecs = rule265 aexprlIhasRecs aexprrIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule266 aexprlImEntryId aexprrImEntryId aselsImEntryId
                           alhsOmExitId = rule267 aexprlImExitId aexprrImExitId aselsImExitId
                           alhsOppAgs = rule268 aexprlIppAgs aexprrIppAgs aselsIppAgs
                           alhsOppDebugs = rule269 aexprlIppDebugs aexprrIppDebugs aselsIppDebugs
                           alhsOrecNode = rule270 aexprlIrecNode aexprrIrecNode aselsIrecNode
                           lcopy = rule271 aexprlIcopy aexprrIcopy aselsIcopy
                           alhsOcopy = rule272 lcopy
                           alhsOgraph = rule273 aexprrIgraph
                           aexprlOcaseExpr = rule274 alhsIcaseExpr
                           aexprlOcurrTaskName = rule275 alhsIcurrTaskName
                           aexprlOgraph = rule276 alhsIgraph
                           aexprlOmergeId = rule277 alhsImergeId
                           aexprlOmoduleEnv = rule278 alhsImoduleEnv
                           aselsOcaseExpr = rule279 alhsIcaseExpr
                           aselsOcurrTaskName = rule280 alhsIcurrTaskName
                           aselsOgraph = rule281 aexprlIgraph
                           aselsOmergeId = rule282 alhsImergeId
                           aselsOmoduleEnv = rule283 alhsImoduleEnv
                           aexprrOcaseExpr = rule284 alhsIcaseExpr
                           aexprrOcurrTaskName = rule285 alhsIcurrTaskName
                           aexprrOgraph = rule286 aselsIgraph
                           aexprrOmergeId = rule287 alhsImergeId
                           aexprrOmoduleEnv = rule288 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 70 "./frontend/Tonic/Pretty.ag" #*/
   rule263  (_) =
                      /*# LINE 70 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1770 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 71 "./frontend/Tonic/Pretty.ag" #*/
   rule264  (_) =
                      /*# LINE 71 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 1775 "frontend/Tonic/Tonic.icl"#*/
   rule265 ((aexprlIhasRecs)) ((aexprrIhasRecs)) ((aselsIhasRecs)) =
     aexprlIhasRecs || aselsIhasRecs || aexprrIhasRecs
   rule266 ((aexprlImEntryId)) ((aexprrImEntryId)) ((aselsImEntryId)) =
     aexprlImEntryId <> aselsImEntryId <> aexprrImEntryId
   rule267 ((aexprlImExitId)) ((aexprrImExitId)) ((aselsImExitId)) =
     aexprlImExitId <> aselsImExitId <> aexprrImExitId
   rule268 ((aexprlIppAgs)) ((aexprrIppAgs)) ((aselsIppAgs)) =
     aexprlIppAgs ++ aselsIppAgs ++ aexprrIppAgs
   rule269 ((aexprlIppDebugs)) ((aexprrIppDebugs)) ((aselsIppDebugs)) =
     aexprlIppDebugs ++ aselsIppDebugs ++ aexprrIppDebugs
   rule270 ((aexprlIrecNode)) ((aexprrIrecNode)) ((aselsIrecNode)) =
     aexprlIrecNode || aselsIrecNode || aexprrIrecNode
   rule271 ((aexprlIcopy)) ((aexprrIcopy)) ((aselsIcopy)) =
     Update aexprlIcopy aselsIcopy aexprrIcopy
   rule272 lcopy =
     lcopy
   rule273 ((aexprrIgraph)) =
     aexprrIgraph
   rule274 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule275 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule276 ((alhsIgraph)) =
     alhsIgraph
   rule277 ((alhsImergeId)) =
     alhsImergeId
   rule278 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule279 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule280 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule281 ((aexprlIgraph)) =
     aexprlIgraph
   rule282 ((alhsImergeId)) =
     alhsImergeId
   rule283 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule284 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule285 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule286 ((aselsIgraph)) =
     aselsIgraph
   rule287 ((alhsImergeId)) =
     alhsImergeId
   rule288 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_RecordUpdate  :: (T_GlobalDefinedSymbol ) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate arg_gdsym_ arg_expr_ arg_binds_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsymX44 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdsym_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut43 agdsymIcopy agdsymIgraph agdsymIhasRecs agdsymImEntryId agdsymImExitId agdsymIppAg agdsymIppAgs agdsymIppDebug agdsymIppDebugs agdsymIrecNode) = inv_GlobalDefinedSymbol_s44 st_gdsymX44 (T_GlobalDefinedSymbol_vIn43 agdsymOcaseExpr agdsymOcurrTaskName agdsymOgraph agdsymOmergeId agdsymOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule289  Void
                           alhsOppAg = rule290  Void
                           alhsOhasRecs = rule291 aexprIhasRecs agdsymIhasRecs
                           alhsOmEntryId = rule292 aexprImEntryId agdsymImEntryId
                           alhsOmExitId = rule293 aexprImExitId agdsymImExitId
                           alhsOppAgs = rule294 aexprIppAgs agdsymIppAgs
                           alhsOppDebugs = rule295 aexprIppDebugs agdsymIppDebugs
                           alhsOrecNode = rule296 aexprIrecNode agdsymIrecNode
                           lcopy = rule297 aexprIcopy agdsymIcopy arg_binds_
                           alhsOcopy = rule298 lcopy
                           alhsOgraph = rule299 aexprIgraph
                           agdsymOcaseExpr = rule300 alhsIcaseExpr
                           agdsymOcurrTaskName = rule301 alhsIcurrTaskName
                           agdsymOgraph = rule302 alhsIgraph
                           agdsymOmergeId = rule303 alhsImergeId
                           agdsymOmoduleEnv = rule304 alhsImoduleEnv
                           aexprOcaseExpr = rule305 alhsIcaseExpr
                           aexprOcurrTaskName = rule306 alhsIcurrTaskName
                           aexprOgraph = rule307 agdsymIgraph
                           aexprOmergeId = rule308 alhsImergeId
                           aexprOmoduleEnv = rule309 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 74 "./frontend/Tonic/Pretty.ag" #*/
   rule289  (_) =
                      /*# LINE 74 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 1862 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 75 "./frontend/Tonic/Pretty.ag" #*/
   rule290  (_) =
                      /*# LINE 75 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 1867 "frontend/Tonic/Tonic.icl"#*/
   rule291 ((aexprIhasRecs)) ((agdsymIhasRecs)) =
     agdsymIhasRecs || aexprIhasRecs
   rule292 ((aexprImEntryId)) ((agdsymImEntryId)) =
     agdsymImEntryId <> aexprImEntryId
   rule293 ((aexprImExitId)) ((agdsymImExitId)) =
     agdsymImExitId <> aexprImExitId
   rule294 ((aexprIppAgs)) ((agdsymIppAgs)) =
     agdsymIppAgs ++ aexprIppAgs
   rule295 ((aexprIppDebugs)) ((agdsymIppDebugs)) =
     agdsymIppDebugs ++ aexprIppDebugs
   rule296 ((aexprIrecNode)) ((agdsymIrecNode)) =
     agdsymIrecNode || aexprIrecNode
   rule297 ((aexprIcopy)) ((agdsymIcopy)) binds_ =
     RecordUpdate agdsymIcopy aexprIcopy binds_
   rule298 lcopy =
     lcopy
   rule299 ((aexprIgraph)) =
     aexprIgraph
   rule300 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule301 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule302 ((alhsIgraph)) =
     alhsIgraph
   rule303 ((alhsImergeId)) =
     alhsImergeId
   rule304 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule305 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule306 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule307 ((agdsymIgraph)) =
     agdsymIgraph
   rule308 ((alhsImergeId)) =
     alhsImergeId
   rule309 ((alhsImoduleEnv)) =
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
                           alhsOppDebug = rule310  Void
                           alhsOppAg = rule311  Void
                           alhsOhasRecs = rule312 adsymIhasRecs aexprIhasRecs
                           alhsOmEntryId = rule313 adsymImEntryId aexprImEntryId
                           alhsOmExitId = rule314 adsymImExitId aexprImExitId
                           alhsOppAgs = rule315 adsymIppAgs aexprIppAgs
                           alhsOppDebugs = rule316 adsymIppDebugs aexprIppDebugs
                           alhsOrecNode = rule317 adsymIrecNode aexprIrecNode
                           lcopy = rule318 adsymIcopy aexprIcopy arg_n_
                           alhsOcopy = rule319 lcopy
                           alhsOgraph = rule320 aexprIgraph
                           adsymOcaseExpr = rule321 alhsIcaseExpr
                           adsymOcurrTaskName = rule322 alhsIcurrTaskName
                           adsymOgraph = rule323 alhsIgraph
                           adsymOmergeId = rule324 alhsImergeId
                           adsymOmoduleEnv = rule325 alhsImoduleEnv
                           aexprOcaseExpr = rule326 alhsIcaseExpr
                           aexprOcurrTaskName = rule327 alhsIcurrTaskName
                           aexprOgraph = rule328 adsymIgraph
                           aexprOmergeId = rule329 alhsImergeId
                           aexprOmoduleEnv = rule330 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 78 "./frontend/Tonic/Pretty.ag" #*/
   rule310  (_) =
                      /*# LINE 78 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 1944 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 79 "./frontend/Tonic/Pretty.ag" #*/
   rule311  (_) =
                      /*# LINE 79 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 1949 "frontend/Tonic/Tonic.icl"#*/
   rule312 ((adsymIhasRecs)) ((aexprIhasRecs)) =
     adsymIhasRecs || aexprIhasRecs
   rule313 ((adsymImEntryId)) ((aexprImEntryId)) =
     adsymImEntryId <> aexprImEntryId
   rule314 ((adsymImExitId)) ((aexprImExitId)) =
     adsymImExitId <> aexprImExitId
   rule315 ((adsymIppAgs)) ((aexprIppAgs)) =
     adsymIppAgs ++ aexprIppAgs
   rule316 ((adsymIppDebugs)) ((aexprIppDebugs)) =
     adsymIppDebugs ++ aexprIppDebugs
   rule317 ((adsymIrecNode)) ((aexprIrecNode)) =
     adsymIrecNode || aexprIrecNode
   rule318 ((adsymIcopy)) ((aexprIcopy)) n_ =
     TupleSelect adsymIcopy n_ aexprIcopy
   rule319 lcopy =
     lcopy
   rule320 ((aexprIgraph)) =
     aexprIgraph
   rule321 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule322 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule323 ((alhsIgraph)) =
     alhsIgraph
   rule324 ((alhsImergeId)) =
     alhsImergeId
   rule325 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule326 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule327 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule328 ((adsymIgraph)) =
     adsymIgraph
   rule329 ((alhsImergeId)) =
     alhsImergeId
   rule330 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_BasicExpr  :: (T_BasicValue ) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_bvX5 = 'Control.Monad.Identity'.runIdentity (attach_T_BasicValue (arg_bv_))
                           (T_BasicValue_vOut4 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BasicValue_s5 st_bvX5 (T_BasicValue_vIn4 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           alhsOppDebug = rule331 abvIppDebug
                           alhsOppAg = rule332 abvIppAg
                           alhsOhasRecs = rule333 abvIhasRecs
                           alhsOmEntryId = rule334 abvImEntryId
                           alhsOmExitId = rule335 abvImExitId
                           alhsOppAgs = rule336 abvIppAgs
                           alhsOppDebugs = rule337 abvIppDebugs
                           alhsOrecNode = rule338 abvIrecNode
                           lcopy = rule339 abvIcopy
                           alhsOcopy = rule340 lcopy
                           alhsOgraph = rule341 abvIgraph
                           abvOcaseExpr = rule342 alhsIcaseExpr
                           abvOcurrTaskName = rule343 alhsIcurrTaskName
                           abvOgraph = rule344 alhsIgraph
                           abvOmergeId = rule345 alhsImergeId
                           abvOmoduleEnv = rule346 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   /*# LINE 82 "./frontend/Tonic/Pretty.ag" #*/
   rule331 ((abvIppDebug)) =
                      /*# LINE 82 "./frontend/Tonic/Pretty.ag" #*/
                      text "<BasicValue>" <+> abvIppDebug
                      /*# LINE 2019 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 83 "./frontend/Tonic/Pretty.ag" #*/
   rule332 ((abvIppAg)) =
                      /*# LINE 83 "./frontend/Tonic/Pretty.ag" #*/
                      abvIppAg
                      /*# LINE 2024 "frontend/Tonic/Tonic.icl"#*/
   rule333 ((abvIhasRecs)) =
     abvIhasRecs
   rule334 ((abvImEntryId)) =
     abvImEntryId
   rule335 ((abvImExitId)) =
     abvImExitId
   rule336 ((abvIppAgs)) =
     abvIppAgs
   rule337 ((abvIppDebugs)) =
     abvIppDebugs
   rule338 ((abvIrecNode)) =
     abvIrecNode
   rule339 ((abvIcopy)) =
     BasicExpr abvIcopy
   rule340 lcopy =
     lcopy
   rule341 ((abvIgraph)) =
     abvIgraph
   rule342 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule343 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule344 ((alhsIgraph)) =
     alhsIgraph
   rule345 ((alhsImergeId)) =
     alhsImergeId
   rule346 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_Conditional arg_cond_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule347  Void
                           alhsOmEntryId = rule348  Void
                           alhsOmExitId = rule349  Void
                           alhsOppAg = rule350  Void
                           alhsOppAgs = rule351  Void
                           alhsOppDebug = rule352  Void
                           alhsOppDebugs = rule353  Void
                           alhsOrecNode = rule354  Void
                           lcopy = rule355 arg_cond_
                           alhsOcopy = rule356 lcopy
                           alhsOgraph = rule357 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule347  (_) =
     False
   rule348  (_) =
     Nothing
   rule349  (_) =
     Nothing
   rule350  (_) =
     empty
   rule351  (_) =
     []
   rule352  (_) =
     empty
   rule353  (_) =
     []
   rule354  (_) =
     False
   rule355 cond_ =
     Conditional cond_
   rule356 lcopy =
     lcopy
   rule357 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr arg_cbbv_ arg_cbfv_ arg_ss_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule358  Void
                           alhsOmEntryId = rule359  Void
                           alhsOmExitId = rule360  Void
                           alhsOppAg = rule361  Void
                           alhsOppAgs = rule362  Void
                           alhsOppDebug = rule363  Void
                           alhsOppDebugs = rule364  Void
                           alhsOrecNode = rule365  Void
                           lcopy = rule366 arg_cbbv_ arg_cbfv_ arg_ss_
                           alhsOcopy = rule367 lcopy
                           alhsOgraph = rule368 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule358  (_) =
     False
   rule359  (_) =
     Nothing
   rule360  (_) =
     Nothing
   rule361  (_) =
     empty
   rule362  (_) =
     []
   rule363  (_) =
     empty
   rule364  (_) =
     []
   rule365  (_) =
     False
   rule366 cbbv_ cbfv_ ss_ =
     AnyCodeExpr cbbv_ cbfv_ ss_
   rule367 lcopy =
     lcopy
   rule368 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr arg_ss_ arg_bl_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule369  Void
                           alhsOmEntryId = rule370  Void
                           alhsOmExitId = rule371  Void
                           alhsOppAg = rule372  Void
                           alhsOppAgs = rule373  Void
                           alhsOppDebug = rule374  Void
                           alhsOppDebugs = rule375  Void
                           alhsOrecNode = rule376  Void
                           lcopy = rule377 arg_bl_ arg_ss_
                           alhsOcopy = rule378 lcopy
                           alhsOgraph = rule379 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule369  (_) =
     False
   rule370  (_) =
     Nothing
   rule371  (_) =
     Nothing
   rule372  (_) =
     empty
   rule373  (_) =
     []
   rule374  (_) =
     empty
   rule375  (_) =
     []
   rule376  (_) =
     False
   rule377 bl_ ss_ =
     ABCCodeExpr ss_ bl_
   rule378 lcopy =
     lcopy
   rule379 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr arg_gdfs_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule380 aexprIhasRecs
                           alhsOmEntryId = rule381 aexprImEntryId
                           alhsOmExitId = rule382 aexprImExitId
                           alhsOppAg = rule383 aexprIppAg
                           alhsOppAgs = rule384 aexprIppAgs
                           alhsOppDebug = rule385 aexprIppDebug
                           alhsOppDebugs = rule386 aexprIppDebugs
                           alhsOrecNode = rule387 aexprIrecNode
                           lcopy = rule388 aexprIcopy arg_gdfs_
                           alhsOcopy = rule389 lcopy
                           alhsOgraph = rule390 aexprIgraph
                           aexprOcaseExpr = rule391 alhsIcaseExpr
                           aexprOcurrTaskName = rule392 alhsIcurrTaskName
                           aexprOgraph = rule393 alhsIgraph
                           aexprOmergeId = rule394 alhsImergeId
                           aexprOmoduleEnv = rule395 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule380 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule381 ((aexprImEntryId)) =
     aexprImEntryId
   rule382 ((aexprImExitId)) =
     aexprImExitId
   rule383 ((aexprIppAg)) =
     aexprIppAg
   rule384 ((aexprIppAgs)) =
     aexprIppAgs
   rule385 ((aexprIppDebug)) =
     aexprIppDebug
   rule386 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule387 ((aexprIrecNode)) =
     aexprIrecNode
   rule388 ((aexprIcopy)) gdfs_ =
     MatchExpr gdfs_ aexprIcopy
   rule389 lcopy =
     lcopy
   rule390 ((aexprIgraph)) =
     aexprIgraph
   rule391 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule392 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule393 ((alhsIgraph)) =
     alhsIgraph
   rule394 ((alhsImergeId)) =
     alhsImergeId
   rule395 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_IsConstructor  :: (T_Expression ) (T_GlobalDefinedSymbol ) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ arg_gdfs_ arg_arity_ arg_gidx_ arg_ident_ arg_pos_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           st_gdfsX44 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gdfs_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           (T_GlobalDefinedSymbol_vOut43 agdfsIcopy agdfsIgraph agdfsIhasRecs agdfsImEntryId agdfsImExitId agdfsIppAg agdfsIppAgs agdfsIppDebug agdfsIppDebugs agdfsIrecNode) = inv_GlobalDefinedSymbol_s44 st_gdfsX44 (T_GlobalDefinedSymbol_vIn43 agdfsOcaseExpr agdfsOcurrTaskName agdfsOgraph agdfsOmergeId agdfsOmoduleEnv)
                           alhsOhasRecs = rule396 aexprIhasRecs agdfsIhasRecs
                           alhsOmEntryId = rule397 aexprImEntryId agdfsImEntryId
                           alhsOmExitId = rule398 aexprImExitId agdfsImExitId
                           alhsOppAg = rule399 aexprIppAg agdfsIppAg
                           alhsOppAgs = rule400 aexprIppAgs agdfsIppAgs
                           alhsOppDebug = rule401 aexprIppDebug agdfsIppDebug
                           alhsOppDebugs = rule402 aexprIppDebugs agdfsIppDebugs
                           alhsOrecNode = rule403 aexprIrecNode agdfsIrecNode
                           lcopy = rule404 aexprIcopy agdfsIcopy arg_arity_ arg_gidx_ arg_ident_ arg_pos_
                           alhsOcopy = rule405 lcopy
                           alhsOgraph = rule406 agdfsIgraph
                           aexprOcaseExpr = rule407 alhsIcaseExpr
                           aexprOcurrTaskName = rule408 alhsIcurrTaskName
                           aexprOgraph = rule409 alhsIgraph
                           aexprOmergeId = rule410 alhsImergeId
                           aexprOmoduleEnv = rule411 alhsImoduleEnv
                           agdfsOcaseExpr = rule412 alhsIcaseExpr
                           agdfsOcurrTaskName = rule413 alhsIcurrTaskName
                           agdfsOgraph = rule414 aexprIgraph
                           agdfsOmergeId = rule415 alhsImergeId
                           agdfsOmoduleEnv = rule416 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule396 ((aexprIhasRecs)) ((agdfsIhasRecs)) =
     aexprIhasRecs || agdfsIhasRecs
   rule397 ((aexprImEntryId)) ((agdfsImEntryId)) =
     aexprImEntryId <> agdfsImEntryId
   rule398 ((aexprImExitId)) ((agdfsImExitId)) =
     aexprImExitId <> agdfsImExitId
   rule399 ((aexprIppAg)) ((agdfsIppAg)) =
     aexprIppAg <$$> agdfsIppAg
   rule400 ((aexprIppAgs)) ((agdfsIppAgs)) =
     aexprIppAgs ++ agdfsIppAgs
   rule401 ((aexprIppDebug)) ((agdfsIppDebug)) =
     aexprIppDebug <$$> agdfsIppDebug
   rule402 ((aexprIppDebugs)) ((agdfsIppDebugs)) =
     aexprIppDebugs ++ agdfsIppDebugs
   rule403 ((aexprIrecNode)) ((agdfsIrecNode)) =
     aexprIrecNode || agdfsIrecNode
   rule404 ((aexprIcopy)) ((agdfsIcopy)) arity_ gidx_ ident_ pos_ =
     IsConstructor aexprIcopy agdfsIcopy arity_ gidx_ ident_ pos_
   rule405 lcopy =
     lcopy
   rule406 ((agdfsIgraph)) =
     agdfsIgraph
   rule407 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule408 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule409 ((alhsIgraph)) =
     alhsIgraph
   rule410 ((alhsImergeId)) =
     alhsImergeId
   rule411 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule412 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule413 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule414 ((aexprIgraph)) =
     aexprIgraph
   rule415 ((alhsImergeId)) =
     alhsImergeId
   rule416 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_FreeVar  :: (T_FreeVar ) -> T_Expression 
sem_Expression_FreeVar arg_fv_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_fvX20 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVar (arg_fv_))
                           (T_FreeVar_vOut19 afvIcopy afvIgraph afvIhasRecs afvImEntryId afvImExitId afvIppAg afvIppAgs afvIppDebug afvIppDebugs afvIrecNode) = inv_FreeVar_s20 st_fvX20 (T_FreeVar_vIn19 afvOcaseExpr afvOcurrTaskName afvOgraph afvOmergeId afvOmoduleEnv)
                           alhsOhasRecs = rule417 afvIhasRecs
                           alhsOmEntryId = rule418 afvImEntryId
                           alhsOmExitId = rule419 afvImExitId
                           alhsOppAg = rule420 afvIppAg
                           alhsOppAgs = rule421 afvIppAgs
                           alhsOppDebug = rule422 afvIppDebug
                           alhsOppDebugs = rule423 afvIppDebugs
                           alhsOrecNode = rule424 afvIrecNode
                           lcopy = rule425 afvIcopy
                           alhsOcopy = rule426 lcopy
                           alhsOgraph = rule427 afvIgraph
                           afvOcaseExpr = rule428 alhsIcaseExpr
                           afvOcurrTaskName = rule429 alhsIcurrTaskName
                           afvOgraph = rule430 alhsIgraph
                           afvOmergeId = rule431 alhsImergeId
                           afvOmoduleEnv = rule432 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule417 ((afvIhasRecs)) =
     afvIhasRecs
   rule418 ((afvImEntryId)) =
     afvImEntryId
   rule419 ((afvImExitId)) =
     afvImExitId
   rule420 ((afvIppAg)) =
     afvIppAg
   rule421 ((afvIppAgs)) =
     afvIppAgs
   rule422 ((afvIppDebug)) =
     afvIppDebug
   rule423 ((afvIppDebugs)) =
     afvIppDebugs
   rule424 ((afvIrecNode)) =
     afvIrecNode
   rule425 ((afvIcopy)) =
     FreeVar afvIcopy
   rule426 lcopy =
     lcopy
   rule427 ((afvIgraph)) =
     afvIgraph
   rule428 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule429 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule430 ((alhsIgraph)) =
     alhsIgraph
   rule431 ((alhsImergeId)) =
     alhsImergeId
   rule432 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction arg_fvat_ arg_expr_ arg_aty_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule433 aexprIhasRecs
                           alhsOmEntryId = rule434 aexprImEntryId
                           alhsOmExitId = rule435 aexprImExitId
                           alhsOppAg = rule436 aexprIppAg
                           alhsOppAgs = rule437 aexprIppAgs
                           alhsOppDebug = rule438 aexprIppDebug
                           alhsOppDebugs = rule439 aexprIppDebugs
                           alhsOrecNode = rule440 aexprIrecNode
                           lcopy = rule441 aexprIcopy arg_aty_ arg_fvat_
                           alhsOcopy = rule442 lcopy
                           alhsOgraph = rule443 aexprIgraph
                           aexprOcaseExpr = rule444 alhsIcaseExpr
                           aexprOcurrTaskName = rule445 alhsIcurrTaskName
                           aexprOgraph = rule446 alhsIgraph
                           aexprOmergeId = rule447 alhsImergeId
                           aexprOmoduleEnv = rule448 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule433 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule434 ((aexprImEntryId)) =
     aexprImEntryId
   rule435 ((aexprImExitId)) =
     aexprImExitId
   rule436 ((aexprIppAg)) =
     aexprIppAg
   rule437 ((aexprIppAgs)) =
     aexprIppAgs
   rule438 ((aexprIppDebug)) =
     aexprIppDebug
   rule439 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule440 ((aexprIrecNode)) =
     aexprIrecNode
   rule441 ((aexprIcopy)) aty_ fvat_ =
     DictionariesFunction fvat_ aexprIcopy aty_
   rule442 lcopy =
     lcopy
   rule443 ((aexprIgraph)) =
     aexprIgraph
   rule444 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule445 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule446 ((alhsIgraph)) =
     alhsIgraph
   rule447 ((alhsImergeId)) =
     alhsImergeId
   rule448 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_Constant  :: (T_SymbIdent ) (Int) (Priority) -> T_Expression 
sem_Expression_Constant arg_symid_ arg_n_ arg_prio_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_symidX62 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbIdent (arg_symid_))
                           (T_SymbIdent_vOut61 asymidIcopy asymidIgraph asymidIhasRecs asymidIident asymidIisCurrTask asymidImEntryId asymidImExitId asymidIppAg asymidIppAgs asymidIppDebug asymidIppDebugs asymidIrecNode) = inv_SymbIdent_s62 st_symidX62 (T_SymbIdent_vIn61 asymidOcaseExpr asymidOcurrTaskName asymidOgraph asymidOmergeId asymidOmoduleEnv)
                           alhsOhasRecs = rule449 asymidIhasRecs
                           alhsOmEntryId = rule450 asymidImEntryId
                           alhsOmExitId = rule451 asymidImExitId
                           alhsOppAg = rule452 asymidIppAg
                           alhsOppAgs = rule453 asymidIppAgs
                           alhsOppDebug = rule454 asymidIppDebug
                           alhsOppDebugs = rule455 asymidIppDebugs
                           alhsOrecNode = rule456 asymidIrecNode
                           lcopy = rule457 asymidIcopy arg_n_ arg_prio_
                           alhsOcopy = rule458 lcopy
                           alhsOgraph = rule459 asymidIgraph
                           asymidOcaseExpr = rule460 alhsIcaseExpr
                           asymidOcurrTaskName = rule461 alhsIcurrTaskName
                           asymidOgraph = rule462 alhsIgraph
                           asymidOmergeId = rule463 alhsImergeId
                           asymidOmoduleEnv = rule464 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule449 ((asymidIhasRecs)) =
     asymidIhasRecs
   rule450 ((asymidImEntryId)) =
     asymidImEntryId
   rule451 ((asymidImExitId)) =
     asymidImExitId
   rule452 ((asymidIppAg)) =
     asymidIppAg
   rule453 ((asymidIppAgs)) =
     asymidIppAgs
   rule454 ((asymidIppDebug)) =
     asymidIppDebug
   rule455 ((asymidIppDebugs)) =
     asymidIppDebugs
   rule456 ((asymidIrecNode)) =
     asymidIrecNode
   rule457 ((asymidIcopy)) n_ prio_ =
     Constant asymidIcopy n_ prio_
   rule458 lcopy =
     lcopy
   rule459 ((asymidIgraph)) =
     asymidIgraph
   rule460 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule461 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule462 ((alhsIgraph)) =
     alhsIgraph
   rule463 ((alhsImergeId)) =
     alhsImergeId
   rule464 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable arg_varinfptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule465  Void
                           alhsOmEntryId = rule466  Void
                           alhsOmExitId = rule467  Void
                           alhsOppAg = rule468  Void
                           alhsOppAgs = rule469  Void
                           alhsOppDebug = rule470  Void
                           alhsOppDebugs = rule471  Void
                           alhsOrecNode = rule472  Void
                           lcopy = rule473 arg_varinfptr_
                           alhsOcopy = rule474 lcopy
                           alhsOgraph = rule475 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule465  (_) =
     False
   rule466  (_) =
     Nothing
   rule467  (_) =
     Nothing
   rule468  (_) =
     empty
   rule469  (_) =
     []
   rule470  (_) =
     empty
   rule471  (_) =
     []
   rule472  (_) =
     False
   rule473 varinfptr_ =
     ClassVariable varinfptr_
   rule474 lcopy =
     lcopy
   rule475 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr arg_dynexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule476  Void
                           alhsOmEntryId = rule477  Void
                           alhsOmExitId = rule478  Void
                           alhsOppAg = rule479  Void
                           alhsOppAgs = rule480  Void
                           alhsOppDebug = rule481  Void
                           alhsOppDebugs = rule482  Void
                           alhsOrecNode = rule483  Void
                           lcopy = rule484 arg_dynexpr_
                           alhsOcopy = rule485 lcopy
                           alhsOgraph = rule486 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule476  (_) =
     False
   rule477  (_) =
     Nothing
   rule478  (_) =
     Nothing
   rule479  (_) =
     empty
   rule480  (_) =
     []
   rule481  (_) =
     empty
   rule482  (_) =
     []
   rule483  (_) =
     False
   rule484 dynexpr_ =
     DynamicExpr dynexpr_
   rule485 lcopy =
     lcopy
   rule486 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression arg_tycodeexpr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule487  Void
                           alhsOmEntryId = rule488  Void
                           alhsOmExitId = rule489  Void
                           alhsOppAg = rule490  Void
                           alhsOppAgs = rule491  Void
                           alhsOppDebug = rule492  Void
                           alhsOppDebugs = rule493  Void
                           alhsOrecNode = rule494  Void
                           lcopy = rule495 arg_tycodeexpr_
                           alhsOcopy = rule496 lcopy
                           alhsOgraph = rule497 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule487  (_) =
     False
   rule488  (_) =
     Nothing
   rule489  (_) =
     Nothing
   rule490  (_) =
     empty
   rule491  (_) =
     []
   rule492  (_) =
     empty
   rule493  (_) =
     []
   rule494  (_) =
     False
   rule495 tycodeexpr_ =
     TypeCodeExpression tycodeexpr_
   rule496 lcopy =
     lcopy
   rule497 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature arg_sigfun_ arg_expr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOhasRecs = rule498 aexprIhasRecs
                           alhsOmEntryId = rule499 aexprImEntryId
                           alhsOmExitId = rule500 aexprImExitId
                           alhsOppAg = rule501 aexprIppAg
                           alhsOppAgs = rule502 aexprIppAgs
                           alhsOppDebug = rule503 aexprIppDebug
                           alhsOppDebugs = rule504 aexprIppDebugs
                           alhsOrecNode = rule505 aexprIrecNode
                           lcopy = rule506 aexprIcopy arg_sigfun_
                           alhsOcopy = rule507 lcopy
                           alhsOgraph = rule508 aexprIgraph
                           aexprOcaseExpr = rule509 alhsIcaseExpr
                           aexprOcurrTaskName = rule510 alhsIcurrTaskName
                           aexprOgraph = rule511 alhsIgraph
                           aexprOmergeId = rule512 alhsImergeId
                           aexprOmoduleEnv = rule513 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule498 ((aexprIhasRecs)) =
     aexprIhasRecs
   rule499 ((aexprImEntryId)) =
     aexprImEntryId
   rule500 ((aexprImExitId)) =
     aexprImExitId
   rule501 ((aexprIppAg)) =
     aexprIppAg
   rule502 ((aexprIppAgs)) =
     aexprIppAgs
   rule503 ((aexprIppDebug)) =
     aexprIppDebug
   rule504 ((aexprIppDebugs)) =
     aexprIppDebugs
   rule505 ((aexprIrecNode)) =
     aexprIrecNode
   rule506 ((aexprIcopy)) sigfun_ =
     TypeSignature sigfun_ aexprIcopy
   rule507 lcopy =
     lcopy
   rule508 ((aexprIgraph)) =
     aexprIgraph
   rule509 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule510 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule511 ((alhsIgraph)) =
     alhsIgraph
   rule512 ((alhsImergeId)) =
     alhsImergeId
   rule513 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expression_EE  ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule514  Void
                           alhsOmEntryId = rule515  Void
                           alhsOmExitId = rule516  Void
                           alhsOppAg = rule517  Void
                           alhsOppAgs = rule518  Void
                           alhsOppDebug = rule519  Void
                           alhsOppDebugs = rule520  Void
                           alhsOrecNode = rule521  Void
                           lcopy = rule522  Void
                           alhsOcopy = rule523 lcopy
                           alhsOgraph = rule524 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule514  (_) =
     False
   rule515  (_) =
     Nothing
   rule516  (_) =
     Nothing
   rule517  (_) =
     empty
   rule518  (_) =
     []
   rule519  (_) =
     empty
   rule520  (_) =
     []
   rule521  (_) =
     False
   rule522  (_) =
     EE
   rule523 lcopy =
     lcopy
   rule524 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind arg_exprinfoptr_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule525  Void
                           alhsOmEntryId = rule526  Void
                           alhsOmExitId = rule527  Void
                           alhsOppAg = rule528  Void
                           alhsOppAgs = rule529  Void
                           alhsOppDebug = rule530  Void
                           alhsOppDebugs = rule531  Void
                           alhsOrecNode = rule532  Void
                           lcopy = rule533 arg_exprinfoptr_
                           alhsOcopy = rule534 lcopy
                           alhsOgraph = rule535 alhsIgraph
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule525  (_) =
     False
   rule526  (_) =
     Nothing
   rule527  (_) =
     Nothing
   rule528  (_) =
     empty
   rule529  (_) =
     []
   rule530  (_) =
     empty
   rule531  (_) =
     []
   rule532  (_) =
     False
   rule533 exprinfoptr_ =
     NoBind exprinfoptr_
   rule534 lcopy =
     lcopy
   rule535 ((alhsIgraph)) =
     alhsIgraph
sem_Expression_FailExpr  :: (T_Ident ) -> T_Expression 
sem_Expression_FailExpr arg_ident_ = T_Expression (lift st14) where
   st14 =
         let
             v13 (T_Expression_vIn13 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ident_))
                           (T_Ident_vOut46 aidentIcopy aidentIgraph aidentIhasRecs aidentIident aidentIisCurrTask aidentImEntryId aidentImExitId aidentIppAg aidentIppAgs aidentIppDebug aidentIppDebugs aidentIrecNode) = inv_Ident_s47 st_identX47 (T_Ident_vIn46 aidentOcaseExpr aidentOcurrTaskName aidentOgraph aidentOmergeId aidentOmoduleEnv)
                           alhsOhasRecs = rule536 aidentIhasRecs
                           alhsOmEntryId = rule537 aidentImEntryId
                           alhsOmExitId = rule538 aidentImExitId
                           alhsOppAg = rule539 aidentIppAg
                           alhsOppAgs = rule540 aidentIppAgs
                           alhsOppDebug = rule541 aidentIppDebug
                           alhsOppDebugs = rule542 aidentIppDebugs
                           alhsOrecNode = rule543 aidentIrecNode
                           lcopy = rule544 aidentIcopy
                           alhsOcopy = rule545 lcopy
                           alhsOgraph = rule546 aidentIgraph
                           aidentOcaseExpr = rule547 alhsIcaseExpr
                           aidentOcurrTaskName = rule548 alhsIcurrTaskName
                           aidentOgraph = rule549 alhsIgraph
                           aidentOmergeId = rule550 alhsImergeId
                           aidentOmoduleEnv = rule551 alhsImoduleEnv
                           ag__result_ = T_Expression_vOut13 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Expression_s14 v13
   rule536 ((aidentIhasRecs)) =
     aidentIhasRecs
   rule537 ((aidentImEntryId)) =
     aidentImEntryId
   rule538 ((aidentImExitId)) =
     aidentImExitId
   rule539 ((aidentIppAg)) =
     aidentIppAg
   rule540 ((aidentIppAgs)) =
     aidentIppAgs
   rule541 ((aidentIppDebug)) =
     aidentIppDebug
   rule542 ((aidentIppDebugs)) =
     aidentIppDebugs
   rule543 ((aidentIrecNode)) =
     aidentIrecNode
   rule544 ((aidentIcopy)) =
     FailExpr aidentIcopy
   rule545 lcopy =
     lcopy
   rule546 ((aidentIgraph)) =
     aidentIgraph
   rule547 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule548 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule549 ((alhsIgraph)) =
     alhsIgraph
   rule550 ((alhsImergeId)) =
     alhsImergeId
   rule551 ((alhsImoduleEnv)) =
     alhsImoduleEnv

// Expressions -------------------------------------------------
// wrapper
numContexts_Inh_Expressions :: Inh_Expressions -> (Int)
numContexts_Inh_Expressions (Inh_Expressions _ _ _ _ _ _ x) = x
moduleEnv_Inh_Expressions :: Inh_Expressions -> (ModuleEnv)
moduleEnv_Inh_Expressions (Inh_Expressions _ _ _ _ _ x _) = x
mergeId_Inh_Expressions :: Inh_Expressions -> (Int)
mergeId_Inh_Expressions (Inh_Expressions _ _ _ _ x _ _) = x
graph_Inh_Expressions :: Inh_Expressions -> (GinGraph)
graph_Inh_Expressions (Inh_Expressions _ _ _ x _ _ _) = x
currTaskName_Inh_Expressions :: Inh_Expressions -> (String)
currTaskName_Inh_Expressions (Inh_Expressions _ _ x _ _ _ _) = x
caseExpr_Inh_Expressions :: Inh_Expressions -> (Maybe Expression)
caseExpr_Inh_Expressions (Inh_Expressions _ x _ _ _ _ _) = x
appSymbDoc_Inh_Expressions :: Inh_Expressions -> (Doc)
appSymbDoc_Inh_Expressions (Inh_Expressions x _ _ _ _ _ _) = x
secondArgRecNode_Syn_Expressions :: Syn_Expressions -> (Bool)
secondArgRecNode_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) = x
secondArgMExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
secondArgMExitId_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _) = x
secondArgMEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
secondArgMEntryId_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _) = x
secondArgIdent_Syn_Expressions :: Syn_Expressions -> (String)
secondArgIdent_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _) = x
secondArgHasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
secondArgHasRecs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _) = x
secondArgGraph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
secondArgGraph_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _) = x
secondArg_Syn_Expressions :: Syn_Expressions -> (MaybeExpression)
secondArg_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _) = x
recNode_Syn_Expressions :: Syn_Expressions -> (Bool)
recNode_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _) = x
ppTail_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppTail_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _) = x
ppPrefix_Syn_Expressions :: Syn_Expressions -> (Doc)
ppPrefix_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _) = x
ppInfix_Syn_Expressions :: Syn_Expressions -> (Doc)
ppInfix_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _) = x
ppDebugs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppDebugs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _) = x
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebug_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _) = x
ppAgs_Syn_Expressions :: Syn_Expressions -> ([Doc])
ppAgs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _) = x
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAg_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
mExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mExitId_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
mEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mEntryId_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
hasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
hasRecs_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
graph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
graph_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgRecNode_Syn_Expressions :: Syn_Expressions -> (Bool)
firstArgRecNode_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgMExitId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
firstArgMExitId_Syn_Expressions (Syn_Expressions _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgMEntryId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
firstArgMEntryId_Syn_Expressions (Syn_Expressions _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgIdent_Syn_Expressions :: Syn_Expressions -> (String)
firstArgIdent_Syn_Expressions (Syn_Expressions _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgHasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
firstArgHasRecs_Syn_Expressions (Syn_Expressions _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArgGraph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
firstArgGraph_Syn_Expressions (Syn_Expressions _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
firstArg_Syn_Expressions :: Syn_Expressions -> (MaybeExpression)
firstArg_Syn_Expressions (Syn_Expressions _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_Expressions :: Syn_Expressions -> (Expressions)
copy_Syn_Expressions (Syn_Expressions x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = x
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions alhsIappSymbDoc alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv alhsInumContexts) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expressions_vIn16 alhsIappSymbDoc alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv alhsInumContexts) >>= \ arg ->
     lift (inv_Expressions_s17 sem arg) >>= \ (T_Expressions_vOut16 alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOppInfix alhsOppPrefix alhsOppTail alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode) ->
     lift (Syn_Expressions alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOppInfix alhsOppPrefix alhsOppTail alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode)
   )

// cata
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = foldr sem_Expressions_Cons sem_Expressions_Nil (map sem_Expression list)

// semantic domain
:: T_Expressions  = T_Expressions (Identity (T_Expressions_s17 ))
attach_T_Expressions (T_Expressions t_Expressions) = t_Expressions
inv_Expressions_s17 (C_Expressions_s17 x) = x
sem_Expressions_Cons  :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (lift st17) where
   st17 =
         let
             v16 (T_Expressions_vIn16 alhsIappSymbDoc alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv alhsInumContexts) =
                       let
                           st_hdX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_hd_))
                           st_tlX17 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_tl_))
                           (T_Expression_vOut13 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Expression_s14 st_hdX14 (T_Expression_vIn13 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Expressions_vOut16 atlIcopy atlIfirstArg atlIfirstArgGraph atlIfirstArgHasRecs atlIfirstArgIdent atlIfirstArgMEntryId atlIfirstArgMExitId atlIfirstArgRecNode atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIppInfix atlIppPrefix atlIppTail atlIrecNode atlIsecondArg atlIsecondArgGraph atlIsecondArgHasRecs atlIsecondArgIdent atlIsecondArgMEntryId atlIsecondArgMExitId atlIsecondArgRecNode) = inv_Expressions_s17 st_tlX17 (T_Expressions_vIn16 atlOappSymbDoc atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv atlOnumContexts)
                           lhasContexts = rule552 alhsInumContexts
                           alhsOfirstArg = rule553 ahdIcopy atlIfirstArg lhasContexts
                           alhsOsecondArg = rule554 atlIfirstArg atlIsecondArg lhasContexts
                           alhsOfirstArgGraph = rule555 ahdIgraph atlIfirstArgGraph lhasContexts
                           alhsOsecondArgGraph = rule556 atlIfirstArgGraph atlIsecondArgGraph lhasContexts
                           atlOgraph = rule557 ahdIgraph alhsIgraph lhasContexts
                           alhsOgraph = rule558 atlIgraph
                           alhsOfirstArgMEntryId = rule559 ahdImEntryId atlIfirstArgMEntryId lhasContexts
                           alhsOsecondArgMEntryId = rule560 atlIfirstArgMEntryId atlIsecondArgMEntryId lhasContexts
                           alhsOfirstArgMExitId = rule561 ahdImExitId atlIfirstArgMExitId lhasContexts
                           alhsOsecondArgMExitId = rule562 atlIsecondArgMExitId lhasContexts
                           alhsOfirstArgHasRecs = rule563 ahdIhasRecs atlIfirstArgHasRecs lhasContexts
                           alhsOsecondArgHasRecs = rule564 atlIfirstArgHasRecs atlIsecondArgHasRecs lhasContexts
                           alhsOfirstArgRecNode = rule565 ahdIrecNode atlIfirstArgRecNode lhasContexts
                           alhsOsecondArgRecNode = rule566 atlIsecondArgRecNode lhasContexts
                           atlOnumContexts = rule567 alhsInumContexts
                           alhsOppInfix = rule568 ahdIppAg alhsIappSymbDoc atlIppTail
                           alhsOppPrefix = rule569 ahdIppAg alhsIappSymbDoc atlIppTail
                           alhsOppTail = rule570 ahdIppAg
                           alhsOhasRecs = rule571 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule572 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule573 ahdImExitId atlImExitId
                           alhsOppAg = rule574 ahdIppAg atlIppAg
                           alhsOppAgs = rule575 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule576 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule577 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule578 ahdIrecNode atlIrecNode
                           lcopy = rule579 ahdIcopy atlIcopy
                           alhsOcopy = rule580 lcopy
                           alhsOfirstArgIdent = rule581 atlIfirstArgIdent
                           alhsOsecondArgIdent = rule582 atlIsecondArgIdent
                           ahdOcaseExpr = rule583 alhsIcaseExpr
                           ahdOcurrTaskName = rule584 alhsIcurrTaskName
                           ahdOgraph = rule585 alhsIgraph
                           ahdOmergeId = rule586 alhsImergeId
                           ahdOmoduleEnv = rule587 alhsImoduleEnv
                           atlOappSymbDoc = rule588 alhsIappSymbDoc
                           atlOcaseExpr = rule589 alhsIcaseExpr
                           atlOcurrTaskName = rule590 alhsIcurrTaskName
                           atlOmergeId = rule591 alhsImergeId
                           atlOmoduleEnv = rule592 alhsImoduleEnv
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOppInfix alhsOppPrefix alhsOppTail alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode
                       in ag__result_
         in C_Expressions_s17 v16
   /*# LINE 69 "./frontend/Tonic/MkGraph.ag" #*/
   rule552 ((alhsInumContexts)) =
                             /*# LINE 69 "./frontend/Tonic/MkGraph.ag" #*/
                             alhsInumContexts > 0
                             /*# LINE 2965 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 71 "./frontend/Tonic/MkGraph.ag" #*/
   rule553 ((ahdIcopy)) ((atlIfirstArg)) lhasContexts =
                             /*# LINE 71 "./frontend/Tonic/MkGraph.ag" #*/
                             if lhasContexts atlIfirstArg (Just ahdIcopy)
                             /*# LINE 2970 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 72 "./frontend/Tonic/MkGraph.ag" #*/
   rule554 ((atlIfirstArg)) ((atlIsecondArg)) lhasContexts =
                             /*# LINE 72 "./frontend/Tonic/MkGraph.ag" #*/
                             if lhasContexts atlIsecondArg atlIfirstArg
                             /*# LINE 2975 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 74 "./frontend/Tonic/MkGraph.ag" #*/
   rule555 ((ahdIgraph)) ((atlIfirstArgGraph)) lhasContexts =
                                /*# LINE 74 "./frontend/Tonic/MkGraph.ag" #*/
                                if lhasContexts atlIfirstArgGraph ahdIgraph
                                /*# LINE 2980 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 75 "./frontend/Tonic/MkGraph.ag" #*/
   rule556 ((atlIfirstArgGraph)) ((atlIsecondArgGraph)) lhasContexts =
                                /*# LINE 75 "./frontend/Tonic/MkGraph.ag" #*/
                                if lhasContexts atlIsecondArgGraph atlIfirstArgGraph
                                /*# LINE 2985 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 77 "./frontend/Tonic/MkGraph.ag" #*/
   rule557 ((ahdIgraph)) ((alhsIgraph)) lhasContexts =
                       /*# LINE 77 "./frontend/Tonic/MkGraph.ag" #*/
                       if lhasContexts alhsIgraph ahdIgraph
                       /*# LINE 2990 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 78 "./frontend/Tonic/MkGraph.ag" #*/
   rule558 ((atlIgraph)) =
                       /*# LINE 78 "./frontend/Tonic/MkGraph.ag" #*/
                       atlIgraph
                       /*# LINE 2995 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 80 "./frontend/Tonic/MkGraph.ag" #*/
   rule559 ((ahdImEntryId)) ((atlIfirstArgMEntryId)) lhasContexts =
                                    /*# LINE 80 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIfirstArgMEntryId ahdImEntryId
                                    /*# LINE 3000 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
   rule560 ((atlIfirstArgMEntryId)) ((atlIsecondArgMEntryId)) lhasContexts =
                                    /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIsecondArgMEntryId atlIfirstArgMEntryId
                                    /*# LINE 3005 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 82 "./frontend/Tonic/MkGraph.ag" #*/
   rule561 ((ahdImExitId)) ((atlIfirstArgMExitId)) lhasContexts =
                                    /*# LINE 82 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIfirstArgMExitId ahdImExitId
                                    /*# LINE 3010 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
   rule562 ((atlIsecondArgMExitId)) lhasContexts =
                                    /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIsecondArgMExitId atlIsecondArgMExitId
                                    /*# LINE 3015 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 84 "./frontend/Tonic/MkGraph.ag" #*/
   rule563 ((ahdIhasRecs)) ((atlIfirstArgHasRecs)) lhasContexts =
                                    /*# LINE 84 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIfirstArgHasRecs ahdIhasRecs
                                    /*# LINE 3020 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 85 "./frontend/Tonic/MkGraph.ag" #*/
   rule564 ((atlIfirstArgHasRecs)) ((atlIsecondArgHasRecs)) lhasContexts =
                                    /*# LINE 85 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIsecondArgHasRecs atlIfirstArgHasRecs
                                    /*# LINE 3025 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 86 "./frontend/Tonic/MkGraph.ag" #*/
   rule565 ((ahdIrecNode)) ((atlIfirstArgRecNode)) lhasContexts =
                                    /*# LINE 86 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIfirstArgRecNode ahdIrecNode
                                    /*# LINE 3030 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 87 "./frontend/Tonic/MkGraph.ag" #*/
   rule566 ((atlIsecondArgRecNode)) lhasContexts =
                                    /*# LINE 87 "./frontend/Tonic/MkGraph.ag" #*/
                                    if lhasContexts atlIsecondArgRecNode atlIsecondArgRecNode
                                    /*# LINE 3035 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 89 "./frontend/Tonic/MkGraph.ag" #*/
   rule567 ((alhsInumContexts)) =
                             /*# LINE 89 "./frontend/Tonic/MkGraph.ag" #*/
                             alhsInumContexts - 1
                             /*# LINE 3040 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 48 "./frontend/Tonic/Pretty.ag" #*/
   rule568 ((ahdIppAg)) ((alhsIappSymbDoc)) ((atlIppTail)) =
                          /*# LINE 48 "./frontend/Tonic/Pretty.ag" #*/
                          ahdIppAg <+> alhsIappSymbDoc <+> hcat (intersperse (text " ") atlIppTail
                          /*# LINE 3045 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 49 "./frontend/Tonic/Pretty.ag" #*/
   rule569 ((ahdIppAg)) ((alhsIappSymbDoc)) ((atlIppTail)) =
                          /*# LINE 49 "./frontend/Tonic/Pretty.ag" #*/
                          alhsIappSymbDoc <+> ahdIppAg <+> hcat (intersperse (text " ") atlIppTail
                          /*# LINE 3050 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 50 "./frontend/Tonic/Pretty.ag" #*/
   rule570 ((ahdIppAg)) =
                          /*# LINE 50 "./frontend/Tonic/Pretty.ag" #*/
                          [ahdIppAg:@tl.ppTail]
                          /*# LINE 3055 "frontend/Tonic/Tonic.icl"#*/
   rule571 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule572 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule573 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule574 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule575 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule576 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule577 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule578 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule579 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule580 lcopy =
     lcopy
   rule581 ((atlIfirstArgIdent)) =
     atlIfirstArgIdent
   rule582 ((atlIsecondArgIdent)) =
     atlIsecondArgIdent
   rule583 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule584 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule585 ((alhsIgraph)) =
     alhsIgraph
   rule586 ((alhsImergeId)) =
     alhsImergeId
   rule587 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule588 ((alhsIappSymbDoc)) =
     alhsIappSymbDoc
   rule589 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule590 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule591 ((alhsImergeId)) =
     alhsImergeId
   rule592 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Expressions_Nil  ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st17) where
   st17 =
         let
             v16 (T_Expressions_vIn16 alhsIappSymbDoc alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv alhsInumContexts) =
                       let
                           alhsOfirstArg = rule593  Void
                           alhsOsecondArg = rule594  Void
                           alhsOfirstArgIdent = rule595  Void
                           alhsOsecondArgIdent = rule596  Void
                           alhsOfirstArgGraph = rule597  Void
                           alhsOsecondArgGraph = rule598  Void
                           alhsOgraph = rule599 alhsIgraph
                           alhsOppInfix = rule600  Void
                           alhsOppPrefix = rule601  Void
                           alhsOppTail = rule602  Void
                           alhsOfirstArgHasRecs = rule603  Void
                           alhsOfirstArgMEntryId = rule604  Void
                           alhsOfirstArgMExitId = rule605  Void
                           alhsOfirstArgRecNode = rule606  Void
                           alhsOhasRecs = rule607  Void
                           alhsOmEntryId = rule608  Void
                           alhsOmExitId = rule609  Void
                           alhsOppAg = rule610  Void
                           alhsOppAgs = rule611  Void
                           alhsOppDebug = rule612  Void
                           alhsOppDebugs = rule613  Void
                           alhsOrecNode = rule614  Void
                           alhsOsecondArgHasRecs = rule615  Void
                           alhsOsecondArgMEntryId = rule616  Void
                           alhsOsecondArgMExitId = rule617  Void
                           alhsOsecondArgRecNode = rule618  Void
                           lcopy = rule619  Void
                           alhsOcopy = rule620 lcopy
                           ag__result_ = T_Expressions_vOut16 alhsOcopy alhsOfirstArg alhsOfirstArgGraph alhsOfirstArgHasRecs alhsOfirstArgIdent alhsOfirstArgMEntryId alhsOfirstArgMExitId alhsOfirstArgRecNode alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOppInfix alhsOppPrefix alhsOppTail alhsOrecNode alhsOsecondArg alhsOsecondArgGraph alhsOsecondArgHasRecs alhsOsecondArgIdent alhsOsecondArgMEntryId alhsOsecondArgMExitId alhsOsecondArgRecNode
                       in ag__result_
         in C_Expressions_s17 v16
   /*# LINE 91 "./frontend/Tonic/MkGraph.ag" #*/
   rule593  (_) =
                           /*# LINE 91 "./frontend/Tonic/MkGraph.ag" #*/
                           Nothing
                           /*# LINE 3141 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 92 "./frontend/Tonic/MkGraph.ag" #*/
   rule594  (_) =
                           /*# LINE 92 "./frontend/Tonic/MkGraph.ag" #*/
                           Nothing
                           /*# LINE 3146 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 94 "./frontend/Tonic/MkGraph.ag" #*/
   rule595  (_) =
                                  /*# LINE 94 "./frontend/Tonic/MkGraph.ag" #*/
                                  abort "firstArgIdent: no args"
                                  /*# LINE 3151 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 95 "./frontend/Tonic/MkGraph.ag" #*/
   rule596  (_) =
                                  /*# LINE 95 "./frontend/Tonic/MkGraph.ag" #*/
                                  abort "secondArgIdent: no args"
                                  /*# LINE 3156 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 97 "./frontend/Tonic/MkGraph.ag" #*/
   rule597  (_) =
                                /*# LINE 97 "./frontend/Tonic/MkGraph.ag" #*/
                                abort "firstArgGraph: no args"
                                /*# LINE 3161 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 98 "./frontend/Tonic/MkGraph.ag" #*/
   rule598  (_) =
                                /*# LINE 98 "./frontend/Tonic/MkGraph.ag" #*/
                                abort "secondArgGraph: no args"
                                /*# LINE 3166 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 100 "./frontend/Tonic/MkGraph.ag" #*/
   rule599 ((alhsIgraph)) =
                       /*# LINE 100 "./frontend/Tonic/MkGraph.ag" #*/
                       alhsIgraph
                       /*# LINE 3171 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 51 "./frontend/Tonic/Pretty.ag" #*/
   rule600  (_) =
                          /*# LINE 51 "./frontend/Tonic/Pretty.ag" #*/
                          empty
                          /*# LINE 3176 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 52 "./frontend/Tonic/Pretty.ag" #*/
   rule601  (_) =
                          /*# LINE 52 "./frontend/Tonic/Pretty.ag" #*/
                          empty
                          /*# LINE 3181 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 53 "./frontend/Tonic/Pretty.ag" #*/
   rule602  (_) =
                          /*# LINE 53 "./frontend/Tonic/Pretty.ag" #*/
                          []
                          /*# LINE 3186 "frontend/Tonic/Tonic.icl"#*/
   rule603  (_) =
     False
   rule604  (_) =
     Nothing
   rule605  (_) =
     Nothing
   rule606  (_) =
     False
   rule607  (_) =
     False
   rule608  (_) =
     Nothing
   rule609  (_) =
     Nothing
   rule610  (_) =
     empty
   rule611  (_) =
     []
   rule612  (_) =
     empty
   rule613  (_) =
     []
   rule614  (_) =
     False
   rule615  (_) =
     False
   rule616  (_) =
     Nothing
   rule617  (_) =
     Nothing
   rule618  (_) =
     False
   rule619  (_) =
     []
   rule620 lcopy =
     lcopy

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
:: T_FreeVar  = T_FreeVar (Identity (T_FreeVar_s20 ))
attach_T_FreeVar (T_FreeVar t_FreeVar) = t_FreeVar
inv_FreeVar_s20 (C_FreeVar_s20 x) = x
sem_FreeVar_FreeVar  :: (Level) (T_Ident ) (VarInfoPtr) (Int) -> T_FreeVar 
sem_FreeVar_FreeVar arg_fv_def_level_ arg_fv_ident_ arg_fv_info_ptr_ arg_fv_count_ = T_FreeVar (lift st20) where
   st20 =
         let
             v19 (T_FreeVar_vIn19 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_fv_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_fv_ident_))
                           (T_Ident_vOut46 afv_identIcopy afv_identIgraph afv_identIhasRecs afv_identIident afv_identIisCurrTask afv_identImEntryId afv_identImExitId afv_identIppAg afv_identIppAgs afv_identIppDebug afv_identIppDebugs afv_identIrecNode) = inv_Ident_s47 st_fv_identX47 (T_Ident_vIn46 afv_identOcaseExpr afv_identOcurrTaskName afv_identOgraph afv_identOmergeId afv_identOmoduleEnv)
                           alhsOppDebug = rule621 afv_identIppDebug
                           alhsOppAg = rule622 afv_identIppAg
                           alhsOhasRecs = rule623 afv_identIhasRecs
                           alhsOmEntryId = rule624 afv_identImEntryId
                           alhsOmExitId = rule625 afv_identImExitId
                           alhsOppAgs = rule626 afv_identIppAgs
                           alhsOppDebugs = rule627 afv_identIppDebugs
                           alhsOrecNode = rule628 afv_identIrecNode
                           lcopy = rule629 afv_identIcopy arg_fv_count_ arg_fv_def_level_ arg_fv_info_ptr_
                           alhsOcopy = rule630 lcopy
                           alhsOgraph = rule631 afv_identIgraph
                           afv_identOcaseExpr = rule632 alhsIcaseExpr
                           afv_identOcurrTaskName = rule633 alhsIcurrTaskName
                           afv_identOgraph = rule634 alhsIgraph
                           afv_identOmergeId = rule635 alhsImergeId
                           afv_identOmoduleEnv = rule636 alhsImoduleEnv
                           ag__result_ = T_FreeVar_vOut19 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_FreeVar_s20 v19
   /*# LINE 94 "./frontend/Tonic/Pretty.ag" #*/
   rule621 ((afv_identIppDebug)) =
                            /*# LINE 94 "./frontend/Tonic/Pretty.ag" #*/
                            afv_identIppDebug
                            /*# LINE 3304 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 95 "./frontend/Tonic/Pretty.ag" #*/
   rule622 ((afv_identIppAg)) =
                            /*# LINE 95 "./frontend/Tonic/Pretty.ag" #*/
                            afv_identIppAg
                            /*# LINE 3309 "frontend/Tonic/Tonic.icl"#*/
   rule623 ((afv_identIhasRecs)) =
     afv_identIhasRecs
   rule624 ((afv_identImEntryId)) =
     afv_identImEntryId
   rule625 ((afv_identImExitId)) =
     afv_identImExitId
   rule626 ((afv_identIppAgs)) =
     afv_identIppAgs
   rule627 ((afv_identIppDebugs)) =
     afv_identIppDebugs
   rule628 ((afv_identIrecNode)) =
     afv_identIrecNode
   rule629 ((afv_identIcopy)) fv_count_ fv_def_level_ fv_info_ptr_ =
     {FreeVar|fv_def_level = fv_def_level_ , fv_ident = afv_identIcopy , fv_info_ptr = fv_info_ptr_ , fv_count = fv_count_}
   rule630 lcopy =
     lcopy
   rule631 ((afv_identIgraph)) =
     afv_identIgraph
   rule632 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule633 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule634 ((alhsIgraph)) =
     alhsIgraph
   rule635 ((alhsImergeId)) =
     alhsImergeId
   rule636 ((alhsImoduleEnv)) =
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
:: T_FreeVars  = T_FreeVars (Identity (T_FreeVars_s23 ))
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
                           alhsOhasRecs = rule637 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule638 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule639 ahdImExitId atlImExitId
                           alhsOrecNode = rule640 ahdIrecNode atlIrecNode
                           lcopy = rule641 ahdIcopy atlIcopy
                           alhsOcopy = rule642 lcopy
                           alhsOgraph = rule643 atlIgraph
                           ahdOcaseExpr = rule644 alhsIcaseExpr
                           ahdOcurrTaskName = rule645 alhsIcurrTaskName
                           ahdOgraph = rule646 alhsIgraph
                           ahdOmergeId = rule647 alhsImergeId
                           ahdOmoduleEnv = rule648 alhsImoduleEnv
                           atlOcaseExpr = rule649 alhsIcaseExpr
                           atlOcurrTaskName = rule650 alhsIcurrTaskName
                           atlOgraph = rule651 ahdIgraph
                           atlOmergeId = rule652 alhsImergeId
                           atlOmoduleEnv = rule653 alhsImoduleEnv
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_FreeVars_s23 v22
   rule637 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule638 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule639 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule640 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule641 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule642 lcopy =
     lcopy
   rule643 ((atlIgraph)) =
     atlIgraph
   rule644 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule645 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule646 ((alhsIgraph)) =
     alhsIgraph
   rule647 ((alhsImergeId)) =
     alhsImergeId
   rule648 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule649 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule650 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule651 ((ahdIgraph)) =
     ahdIgraph
   rule652 ((alhsImergeId)) =
     alhsImergeId
   rule653 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_FreeVars_Nil  ::   T_FreeVars 
sem_FreeVars_Nil  = T_FreeVars (lift st23) where
   st23 =
         let
             v22 (T_FreeVars_vIn22 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule654  Void
                           alhsOmEntryId = rule655  Void
                           alhsOmExitId = rule656  Void
                           alhsOrecNode = rule657  Void
                           lcopy = rule658  Void
                           alhsOcopy = rule659 lcopy
                           alhsOgraph = rule660 alhsIgraph
                           ag__result_ = T_FreeVars_vOut22 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_FreeVars_s23 v22
   rule654  (_) =
     False
   rule655  (_) =
     Nothing
   rule656  (_) =
     Nothing
   rule657  (_) =
     False
   rule658  (_) =
     []
   rule659 lcopy =
     lcopy
   rule660 ((alhsIgraph)) =
     alhsIgraph

// FunType -----------------------------------------------------
// wrapper
moduleEnv_Inh_FunType :: Inh_FunType -> (ModuleEnv)
moduleEnv_Inh_FunType (Inh_FunType _ _ _ _ x) = x
mergeId_Inh_FunType :: Inh_FunType -> (Int)
mergeId_Inh_FunType (Inh_FunType _ _ _ x _) = x
graph_Inh_FunType :: Inh_FunType -> (GinGraph)
graph_Inh_FunType (Inh_FunType _ _ x _ _) = x
currTaskName_Inh_FunType :: Inh_FunType -> (String)
currTaskName_Inh_FunType (Inh_FunType _ x _ _ _) = x
caseExpr_Inh_FunType :: Inh_FunType -> (Maybe Expression)
caseExpr_Inh_FunType (Inh_FunType x _ _ _ _) = x
recNode_Syn_FunType :: Syn_FunType -> (Bool)
recNode_Syn_FunType (Syn_FunType _ _ _ _ _ x) = x
mExitId_Syn_FunType :: Syn_FunType -> (Maybe Int)
mExitId_Syn_FunType (Syn_FunType _ _ _ _ x _) = x
mEntryId_Syn_FunType :: Syn_FunType -> (Maybe Int)
mEntryId_Syn_FunType (Syn_FunType _ _ _ x _ _) = x
hasRecs_Syn_FunType :: Syn_FunType -> (Bool)
hasRecs_Syn_FunType (Syn_FunType _ _ x _ _ _) = x
graph_Syn_FunType :: Syn_FunType -> (GinGraph)
graph_Syn_FunType (Syn_FunType _ x _ _ _ _) = x
copy_Syn_FunType :: Syn_FunType -> (FunType)
copy_Syn_FunType (Syn_FunType x _ _ _ _ _) = x
wrap_FunType :: T_FunType  Inh_FunType  -> (Syn_FunType )
wrap_FunType (T_FunType act) (Inh_FunType alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_FunType_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_FunType_s26 sem arg) >>= \ (T_FunType_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode) ->
     lift (Syn_FunType alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode)
   )

// cata
sem_FunType :: FunType  -> T_FunType 
sem_FunType { FunType | ft_ident = ft_ident_,ft_arity = ft_arity_,ft_priority = ft_priority_,ft_type = ft_type_,ft_pos = ft_pos_,ft_specials = ft_specials_,ft_type_ptr = ft_type_ptr_ } = sem_FunType_FunType ( sem_Ident ft_ident_ ) ft_arity_ ( sem_Priority ft_priority_ ) ( sem_SymbolType ft_type_ ) ft_pos_ ft_specials_ ft_type_ptr_

// semantic domain
:: T_FunType  = T_FunType (Identity (T_FunType_s26 ))
attach_T_FunType (T_FunType t_FunType) = t_FunType
inv_FunType_s26 (C_FunType_s26 x) = x
sem_FunType_FunType  :: (T_Ident ) (Int) (T_Priority ) (T_SymbolType ) (Position) (FunSpecials) (VarInfoPtr) -> T_FunType 
sem_FunType_FunType arg_ft_ident_ arg_ft_arity_ arg_ft_priority_ arg_ft_type_ arg_ft_pos_ arg_ft_specials_ arg_ft_type_ptr_ = T_FunType (lift st26) where
   st26 =
         let
             v25 (T_FunType_vIn25 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_ft_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_ft_ident_))
                           st_ft_priorityX53 = 'Control.Monad.Identity'.runIdentity (attach_T_Priority (arg_ft_priority_))
                           st_ft_typeX65 = 'Control.Monad.Identity'.runIdentity (attach_T_SymbolType (arg_ft_type_))
                           (T_Ident_vOut46 aft_identIcopy aft_identIgraph aft_identIhasRecs aft_identIident aft_identIisCurrTask aft_identImEntryId aft_identImExitId aft_identIppAg aft_identIppAgs aft_identIppDebug aft_identIppDebugs aft_identIrecNode) = inv_Ident_s47 st_ft_identX47 (T_Ident_vIn46 aft_identOcaseExpr aft_identOcurrTaskName aft_identOgraph aft_identOmergeId aft_identOmoduleEnv)
                           (T_Priority_vOut52 aft_priorityIcopy aft_priorityIgraph) = inv_Priority_s53 st_ft_priorityX53 (T_Priority_vIn52 aft_priorityOcaseExpr aft_priorityOcurrTaskName aft_priorityOgraph aft_priorityOmergeId aft_priorityOmoduleEnv)
                           (T_SymbolType_vOut64 aft_typeIcopy aft_typeIgraph aft_typeIhasRecs aft_typeImEntryId aft_typeImExitId aft_typeIppAg aft_typeIppAgs aft_typeIppDebug aft_typeIppDebugs aft_typeIrecNode) = inv_SymbolType_s65 st_ft_typeX65 (T_SymbolType_vIn64 aft_typeOcaseExpr aft_typeOcurrTaskName aft_typeOgraph aft_typeOmergeId aft_typeOmoduleEnv)
                           alhsOhasRecs = rule661 aft_identIhasRecs aft_typeIhasRecs
                           alhsOmEntryId = rule662 aft_identImEntryId aft_typeImEntryId
                           alhsOmExitId = rule663 aft_identImExitId aft_typeImExitId
                           alhsOrecNode = rule664 aft_identIrecNode aft_typeIrecNode
                           lcopy = rule665 aft_identIcopy aft_priorityIcopy aft_typeIcopy arg_ft_arity_ arg_ft_pos_ arg_ft_specials_ arg_ft_type_ptr_
                           alhsOcopy = rule666 lcopy
                           alhsOgraph = rule667 aft_typeIgraph
                           aft_identOcaseExpr = rule668 alhsIcaseExpr
                           aft_identOcurrTaskName = rule669 alhsIcurrTaskName
                           aft_identOgraph = rule670 alhsIgraph
                           aft_identOmergeId = rule671 alhsImergeId
                           aft_identOmoduleEnv = rule672 alhsImoduleEnv
                           aft_priorityOcaseExpr = rule673 alhsIcaseExpr
                           aft_priorityOcurrTaskName = rule674 alhsIcurrTaskName
                           aft_priorityOgraph = rule675 aft_identIgraph
                           aft_priorityOmergeId = rule676 alhsImergeId
                           aft_priorityOmoduleEnv = rule677 alhsImoduleEnv
                           aft_typeOcaseExpr = rule678 alhsIcaseExpr
                           aft_typeOcurrTaskName = rule679 alhsIcurrTaskName
                           aft_typeOgraph = rule680 aft_priorityIgraph
                           aft_typeOmergeId = rule681 alhsImergeId
                           aft_typeOmoduleEnv = rule682 alhsImoduleEnv
                           ag__result_ = T_FunType_vOut25 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_FunType_s26 v25
   rule661 ((aft_identIhasRecs)) ((aft_typeIhasRecs)) =
     aft_identIhasRecs || aft_typeIhasRecs
   rule662 ((aft_identImEntryId)) ((aft_typeImEntryId)) =
     aft_identImEntryId <> aft_typeImEntryId
   rule663 ((aft_identImExitId)) ((aft_typeImExitId)) =
     aft_identImExitId <> aft_typeImExitId
   rule664 ((aft_identIrecNode)) ((aft_typeIrecNode)) =
     aft_identIrecNode || aft_typeIrecNode
   rule665 ((aft_identIcopy)) ((aft_priorityIcopy)) ((aft_typeIcopy)) ft_arity_ ft_pos_ ft_specials_ ft_type_ptr_ =
     {FunType|ft_ident = aft_identIcopy , ft_arity = ft_arity_ , ft_priority = aft_priorityIcopy , ft_type = aft_typeIcopy , ft_pos = ft_pos_ , ft_specials = ft_specials_ , ft_type_ptr = ft_type_ptr_}
   rule666 lcopy =
     lcopy
   rule667 ((aft_typeIgraph)) =
     aft_typeIgraph
   rule668 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule669 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule670 ((alhsIgraph)) =
     alhsIgraph
   rule671 ((alhsImergeId)) =
     alhsImergeId
   rule672 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule673 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule674 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule675 ((aft_identIgraph)) =
     aft_identIgraph
   rule676 ((alhsImergeId)) =
     alhsImergeId
   rule677 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule678 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule679 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule680 ((aft_priorityIgraph)) =
     aft_priorityIgraph
   rule681 ((alhsImergeId)) =
     alhsImergeId
   rule682 ((alhsImoduleEnv)) =
     alhsImoduleEnv

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
     lift (T_GExpression_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GExpression_s29 sem arg) >>= \ (T_GExpression_vOut28 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GExpression alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GExpression :: GExpression  -> T_GExpression 
sem_GExpression ( GUndefinedExpression  ) = sem_GExpression_GUndefinedExpression 
sem_GExpression ( GGraphExpression gg_ ) = sem_GExpression_GGraphExpression gg_
sem_GExpression ( GListExpression gexprs_ ) = sem_GExpression_GListExpression gexprs_
sem_GExpression ( GCleanExpression gcexpr_ ) = sem_GExpression_GCleanExpression gcexpr_

// semantic domain
:: T_GExpression  = T_GExpression (Identity (T_GExpression_s29 ))
attach_T_GExpression (T_GExpression t_GExpression) = t_GExpression
inv_GExpression_s29 (C_GExpression_s29 x) = x
sem_GExpression_GUndefinedExpression  ::   T_GExpression 
sem_GExpression_GUndefinedExpression  = T_GExpression (lift st29) where
   st29 =
         let
             v28 (T_GExpression_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule683  Void
                           alhsOppAg = rule684  Void
                           alhsOhasRecs = rule685  Void
                           alhsOmEntryId = rule686  Void
                           alhsOmExitId = rule687  Void
                           alhsOppAgs = rule688  Void
                           alhsOppDebugs = rule689  Void
                           alhsOrecNode = rule690  Void
                           lcopy = rule691  Void
                           alhsOcopy = rule692 lcopy
                           alhsOgraph = rule693 alhsIgraph
                           ag__result_ = T_GExpression_vOut28 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s29 v28
   /*# LINE 128 "./frontend/Tonic/Pretty.ag" #*/
   rule683  (_) =
                                          /*# LINE 128 "./frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3674 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 129 "./frontend/Tonic/Pretty.ag" #*/
   rule684  (_) =
                                          /*# LINE 129 "./frontend/Tonic/Pretty.ag" #*/
                                          text "undef"
                                          /*# LINE 3679 "frontend/Tonic/Tonic.icl"#*/
   rule685  (_) =
     False
   rule686  (_) =
     Nothing
   rule687  (_) =
     Nothing
   rule688  (_) =
     []
   rule689  (_) =
     []
   rule690  (_) =
     False
   rule691  (_) =
     GUndefinedExpression
   rule692 lcopy =
     lcopy
   rule693 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GGraphExpression  :: (GGraph) -> T_GExpression 
sem_GExpression_GGraphExpression arg_gg_ = T_GExpression (lift st29) where
   st29 =
         let
             v28 (T_GExpression_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule694  Void
                           alhsOppAg = rule695  Void
                           alhsOhasRecs = rule696  Void
                           alhsOmEntryId = rule697  Void
                           alhsOmExitId = rule698  Void
                           alhsOppAgs = rule699  Void
                           alhsOppDebugs = rule700  Void
                           alhsOrecNode = rule701  Void
                           lcopy = rule702 arg_gg_
                           alhsOcopy = rule703 lcopy
                           alhsOgraph = rule704 alhsIgraph
                           ag__result_ = T_GExpression_vOut28 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s29 v28
   /*# LINE 130 "./frontend/Tonic/Pretty.ag" #*/
   rule694  (_) =
                                          /*# LINE 130 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3722 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 131 "./frontend/Tonic/Pretty.ag" #*/
   rule695  (_) =
                                          /*# LINE 131 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a subgraph (and don't PP one)"
                                          /*# LINE 3727 "frontend/Tonic/Tonic.icl"#*/
   rule696  (_) =
     False
   rule697  (_) =
     Nothing
   rule698  (_) =
     Nothing
   rule699  (_) =
     []
   rule700  (_) =
     []
   rule701  (_) =
     False
   rule702 gg_ =
     GGraphExpression gg_
   rule703 lcopy =
     lcopy
   rule704 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GListExpression  :: ([GExpression]) -> T_GExpression 
sem_GExpression_GListExpression arg_gexprs_ = T_GExpression (lift st29) where
   st29 =
         let
             v28 (T_GExpression_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule705  Void
                           alhsOppAg = rule706  Void
                           alhsOhasRecs = rule707  Void
                           alhsOmEntryId = rule708  Void
                           alhsOmExitId = rule709  Void
                           alhsOppAgs = rule710  Void
                           alhsOppDebugs = rule711  Void
                           alhsOrecNode = rule712  Void
                           lcopy = rule713 arg_gexprs_
                           alhsOcopy = rule714 lcopy
                           alhsOgraph = rule715 alhsIgraph
                           ag__result_ = T_GExpression_vOut28 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s29 v28
   /*# LINE 132 "./frontend/Tonic/Pretty.ag" #*/
   rule705  (_) =
                                          /*# LINE 132 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3770 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 133 "./frontend/Tonic/Pretty.ag" #*/
   rule706  (_) =
                                          /*# LINE 133 "./frontend/Tonic/Pretty.ag" #*/
                                          text "TODO: render a list expression (and don't PP one)"
                                          /*# LINE 3775 "frontend/Tonic/Tonic.icl"#*/
   rule707  (_) =
     False
   rule708  (_) =
     Nothing
   rule709  (_) =
     Nothing
   rule710  (_) =
     []
   rule711  (_) =
     []
   rule712  (_) =
     False
   rule713 gexprs_ =
     GListExpression gexprs_
   rule714 lcopy =
     lcopy
   rule715 ((alhsIgraph)) =
     alhsIgraph
sem_GExpression_GCleanExpression  :: (GCleanExpression) -> T_GExpression 
sem_GExpression_GCleanExpression arg_gcexpr_ = T_GExpression (lift st29) where
   st29 =
         let
             v28 (T_GExpression_vIn28 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOppDebug = rule716 arg_gcexpr_
                           alhsOppAg = rule717 arg_gcexpr_
                           alhsOhasRecs = rule718  Void
                           alhsOmEntryId = rule719  Void
                           alhsOmExitId = rule720  Void
                           alhsOppAgs = rule721  Void
                           alhsOppDebugs = rule722  Void
                           alhsOrecNode = rule723  Void
                           lcopy = rule724 arg_gcexpr_
                           alhsOcopy = rule725 lcopy
                           alhsOgraph = rule726 alhsIgraph
                           ag__result_ = T_GExpression_vOut28 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GExpression_s29 v28
   /*# LINE 134 "./frontend/Tonic/Pretty.ag" #*/
   rule716 gcexpr_ =
                                          /*# LINE 134 "./frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3818 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 135 "./frontend/Tonic/Pretty.ag" #*/
   rule717 gcexpr_ =
                                          /*# LINE 135 "./frontend/Tonic/Pretty.ag" #*/
                                          text gcexpr_
                                          /*# LINE 3823 "frontend/Tonic/Tonic.icl"#*/
   rule718  (_) =
     False
   rule719  (_) =
     Nothing
   rule720  (_) =
     Nothing
   rule721  (_) =
     []
   rule722  (_) =
     []
   rule723  (_) =
     False
   rule724 gcexpr_ =
     GCleanExpression gcexpr_
   rule725 lcopy =
     lcopy
   rule726 ((alhsIgraph)) =
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
recNode_Syn_GFunDef (Syn_GFunDef _ _ _ _ _ _ x) = x
mExitId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
mExitId_Syn_GFunDef (Syn_GFunDef _ _ _ _ _ x _) = x
mEntryId_Syn_GFunDef :: Syn_GFunDef -> (Maybe Int)
mEntryId_Syn_GFunDef (Syn_GFunDef _ _ _ _ x _ _) = x
hasRecs_Syn_GFunDef :: Syn_GFunDef -> (Bool)
hasRecs_Syn_GFunDef (Syn_GFunDef _ _ _ x _ _ _) = x
graph_Syn_GFunDef :: Syn_GFunDef -> (GinGraph)
graph_Syn_GFunDef (Syn_GFunDef _ _ x _ _ _ _) = x
funArgs_Syn_GFunDef :: Syn_GFunDef -> ([FreeVar])
funArgs_Syn_GFunDef (Syn_GFunDef _ x _ _ _ _ _) = x
copy_Syn_GFunDef :: Syn_GFunDef -> (GFunDef)
copy_Syn_GFunDef (Syn_GFunDef x _ _ _ _ _ _) = x
wrap_GFunDef :: T_GFunDef  Inh_GFunDef  -> (Syn_GFunDef )
wrap_GFunDef (T_GFunDef act) (Inh_GFunDef alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_GFunDef_vIn31 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GFunDef_s32 sem arg) >>= \ (T_GFunDef_vOut31 alhsOcopy alhsOfunArgs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode) ->
     lift (Syn_GFunDef alhsOcopy alhsOfunArgs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode)
   )

// cata
sem_GFunDef :: GFunDef  -> T_GFunDef 
sem_GFunDef { GFunDef | gfd_name = gfd_name_,gfd_args = gfd_args_,gfd_rhs = gfd_rhs_,gfd_type = gfd_type_,gfd_priority = gfd_priority_ } = sem_GFunDef_GFunDef gfd_name_ ( sem_FreeVars gfd_args_ ) ( sem_Expression gfd_rhs_ ) gfd_type_ ( sem_Priority gfd_priority_ )

// semantic domain
:: T_GFunDef  = T_GFunDef (Identity (T_GFunDef_s32 ))
attach_T_GFunDef (T_GFunDef t_GFunDef) = t_GFunDef
inv_GFunDef_s32 (C_GFunDef_s32 x) = x
sem_GFunDef_GFunDef  :: (String) (T_FreeVars ) (T_Expression ) (Optional SymbolType) (T_Priority ) -> T_GFunDef 
sem_GFunDef_GFunDef arg_gfd_name_ arg_gfd_args_ arg_gfd_rhs_ arg_gfd_type_ arg_gfd_priority_ = T_GFunDef (lift st32) where
   st32 =
         let
             v31 (T_GFunDef_vIn31 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gfd_argsX23 = 'Control.Monad.Identity'.runIdentity (attach_T_FreeVars (arg_gfd_args_))
                           st_gfd_rhsX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_gfd_rhs_))
                           st_gfd_priorityX53 = 'Control.Monad.Identity'.runIdentity (attach_T_Priority (arg_gfd_priority_))
                           (T_FreeVars_vOut22 agfd_argsIcopy agfd_argsIgraph agfd_argsIhasRecs agfd_argsImEntryId agfd_argsImExitId agfd_argsIrecNode) = inv_FreeVars_s23 st_gfd_argsX23 (T_FreeVars_vIn22 agfd_argsOcaseExpr agfd_argsOcurrTaskName agfd_argsOgraph agfd_argsOmergeId agfd_argsOmoduleEnv)
                           (T_Expression_vOut13 agfd_rhsIcopy agfd_rhsIgraph agfd_rhsIhasRecs agfd_rhsImEntryId agfd_rhsImExitId agfd_rhsIppAg agfd_rhsIppAgs agfd_rhsIppDebug agfd_rhsIppDebugs agfd_rhsIrecNode) = inv_Expression_s14 st_gfd_rhsX14 (T_Expression_vIn13 agfd_rhsOcaseExpr agfd_rhsOcurrTaskName agfd_rhsOgraph agfd_rhsOmergeId agfd_rhsOmoduleEnv)
                           (T_Priority_vOut52 agfd_priorityIcopy agfd_priorityIgraph) = inv_Priority_s53 st_gfd_priorityX53 (T_Priority_vIn52 agfd_priorityOcaseExpr agfd_priorityOcurrTaskName agfd_priorityOgraph agfd_priorityOmergeId agfd_priorityOmoduleEnv)
                           alhsOfunArgs = rule727 agfd_argsIcopy
                           alhsOmEntryId = rule728 agfd_rhsImEntryId
                           alhsOmExitId = rule729 agfd_rhsImExitId
                           alhsOgraph = rule730 agfd_rhsIgraph
                           alhsOhasRecs = rule731 agfd_argsIhasRecs agfd_rhsIhasRecs
                           alhsOrecNode = rule732 agfd_argsIrecNode agfd_rhsIrecNode
                           lcopy = rule733 agfd_argsIcopy agfd_priorityIcopy agfd_rhsIcopy arg_gfd_name_ arg_gfd_type_
                           alhsOcopy = rule734 lcopy
                           agfd_argsOcaseExpr = rule735 alhsIcaseExpr
                           agfd_argsOcurrTaskName = rule736 alhsIcurrTaskName
                           agfd_argsOgraph = rule737 alhsIgraph
                           agfd_argsOmergeId = rule738 alhsImergeId
                           agfd_argsOmoduleEnv = rule739 alhsImoduleEnv
                           agfd_rhsOcaseExpr = rule740 alhsIcaseExpr
                           agfd_rhsOcurrTaskName = rule741 alhsIcurrTaskName
                           agfd_rhsOgraph = rule742 agfd_argsIgraph
                           agfd_rhsOmergeId = rule743 alhsImergeId
                           agfd_rhsOmoduleEnv = rule744 alhsImoduleEnv
                           agfd_priorityOcaseExpr = rule745 alhsIcaseExpr
                           agfd_priorityOcurrTaskName = rule746 alhsIcurrTaskName
                           agfd_priorityOgraph = rule747 agfd_rhsIgraph
                           agfd_priorityOmergeId = rule748 alhsImergeId
                           agfd_priorityOmoduleEnv = rule749 alhsImoduleEnv
                           ag__result_ = T_GFunDef_vOut31 alhsOcopy alhsOfunArgs alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_GFunDef_s32 v31
   /*# LINE 117 "./frontend/Tonic/MkGraph.ag" #*/
   rule727 ((agfd_argsIcopy)) =
                       /*# LINE 117 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_argsIcopy
                       /*# LINE 3928 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 119 "./frontend/Tonic/MkGraph.ag" #*/
   rule728 ((agfd_rhsImEntryId)) =
                       /*# LINE 119 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImEntryId
                       /*# LINE 3933 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
   rule729 ((agfd_rhsImExitId)) =
                       /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsImExitId
                       /*# LINE 3938 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 122 "./frontend/Tonic/MkGraph.ag" #*/
   rule730 ((agfd_rhsIgraph)) =
                       /*# LINE 122 "./frontend/Tonic/MkGraph.ag" #*/
                       agfd_rhsIgraph
                       /*# LINE 3943 "frontend/Tonic/Tonic.icl"#*/
   rule731 ((agfd_argsIhasRecs)) ((agfd_rhsIhasRecs)) =
     agfd_argsIhasRecs || agfd_rhsIhasRecs
   rule732 ((agfd_argsIrecNode)) ((agfd_rhsIrecNode)) =
     agfd_argsIrecNode || agfd_rhsIrecNode
   rule733 ((agfd_argsIcopy)) ((agfd_priorityIcopy)) ((agfd_rhsIcopy)) gfd_name_ gfd_type_ =
     {GFunDef|gfd_name = gfd_name_ , gfd_args = agfd_argsIcopy , gfd_rhs = agfd_rhsIcopy , gfd_type = gfd_type_ , gfd_priority = agfd_priorityIcopy}
   rule734 lcopy =
     lcopy
   rule735 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule736 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule737 ((alhsIgraph)) =
     alhsIgraph
   rule738 ((alhsImergeId)) =
     alhsImergeId
   rule739 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule740 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule741 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule742 ((agfd_argsIgraph)) =
     agfd_argsIgraph
   rule743 ((alhsImergeId)) =
     alhsImergeId
   rule744 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule745 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule746 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule747 ((agfd_rhsIgraph)) =
     agfd_rhsIgraph
   rule748 ((alhsImergeId)) =
     alhsImergeId
   rule749 ((alhsImoduleEnv)) =
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
     lift (T_GLet_vIn34 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLet_s35 sem arg) >>= \ (T_GLet_vOut34 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLet alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLet :: GLet  -> T_GLet 
sem_GLet { GLet | glet_binds = glet_binds_,glet_expr = glet_expr_ } = sem_GLet_GLet ( sem_GLetBinds glet_binds_ ) ( sem_Expression glet_expr_ )

// semantic domain
:: T_GLet  = T_GLet (Identity (T_GLet_s35 ))
attach_T_GLet (T_GLet t_GLet) = t_GLet
inv_GLet_s35 (C_GLet_s35 x) = x
sem_GLet_GLet  :: (T_GLetBinds ) (T_Expression ) -> T_GLet 
sem_GLet_GLet arg_glet_binds_ arg_glet_expr_ = T_GLet (lift st35) where
   st35 =
         let
             v34 (T_GLet_vIn34 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_glet_bindsX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_glet_binds_))
                           st_glet_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glet_expr_))
                           (T_GLetBinds_vOut40 aglet_bindsIcopy aglet_bindsIgraph aglet_bindsIhasRecs aglet_bindsImCaseVarExpr aglet_bindsImEntryId aglet_bindsImExitId aglet_bindsIppAg aglet_bindsIppAgs aglet_bindsIppDebug aglet_bindsIppDebugs aglet_bindsIrecNode) = inv_GLetBinds_s41 st_glet_bindsX41 (T_GLetBinds_vIn40 aglet_bindsOcaseExpr aglet_bindsOcurrTaskName aglet_bindsOgraph aglet_bindsOmergeId aglet_bindsOmoduleEnv)
                           (T_Expression_vOut13 aglet_exprIcopy aglet_exprIgraph aglet_exprIhasRecs aglet_exprImEntryId aglet_exprImExitId aglet_exprIppAg aglet_exprIppAgs aglet_exprIppDebug aglet_exprIppDebugs aglet_exprIrecNode) = inv_Expression_s14 st_glet_exprX14 (T_Expression_vIn13 aglet_exprOcaseExpr aglet_exprOcurrTaskName aglet_exprOgraph aglet_exprOmergeId aglet_exprOmoduleEnv)
                           alhsOgraph = rule750 aglet_exprIgraph lconnId lmCaseVarExpr
                           lmCaseVarExpr = rule751 aglet_bindsImCaseVarExpr
                           aglet_exprOcaseExpr = rule752 lmCaseVarExpr
                           alhsOrecNode = rule753  Void
                           lconnId = rule754 aglet_exprImEntryId aglet_exprIrecNode alhsImergeId
                           alhsOppDebug = rule755 aglet_bindsIppDebugs
                           alhsOppAg = rule756 aglet_bindsIppAgs
                           alhsOhasRecs = rule757 aglet_bindsIhasRecs aglet_exprIhasRecs
                           alhsOmEntryId = rule758 aglet_bindsImEntryId aglet_exprImEntryId
                           alhsOmExitId = rule759 aglet_bindsImExitId aglet_exprImExitId
                           alhsOppAgs = rule760 aglet_bindsIppAgs aglet_exprIppAgs
                           alhsOppDebugs = rule761 aglet_bindsIppDebugs aglet_exprIppDebugs
                           lcopy = rule762 aglet_bindsIcopy aglet_exprIcopy
                           alhsOcopy = rule763 lcopy
                           aglet_bindsOcaseExpr = rule764 alhsIcaseExpr
                           aglet_bindsOcurrTaskName = rule765 alhsIcurrTaskName
                           aglet_bindsOgraph = rule766 alhsIgraph
                           aglet_bindsOmergeId = rule767 alhsImergeId
                           aglet_bindsOmoduleEnv = rule768 alhsImoduleEnv
                           aglet_exprOcurrTaskName = rule769 alhsIcurrTaskName
                           aglet_exprOgraph = rule770 aglet_bindsIgraph
                           aglet_exprOmergeId = rule771 alhsImergeId
                           aglet_exprOmoduleEnv = rule772 alhsImoduleEnv
                           ag__result_ = T_GLet_vOut34 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLet_s35 v34
   /*# LINE 283 "./frontend/Tonic/MkGraph.ag" #*/
   rule750 ((aglet_exprIgraph)) lconnId lmCaseVarExpr =
                    /*# LINE 283 "./frontend/Tonic/MkGraph.ag" #*/
                    case lmCaseVarExpr     of
                      Just e  -> aglet_exprIgraph
                      _       -> let (lid, g)  = undef
                                     err       = abort "Failed to add let edge; no synthesized ID from let body"
                                 in maybe err (\n -> addEmptyEdge (lid, n) g) lconnId
                    /*# LINE 4076 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 290 "./frontend/Tonic/MkGraph.ag" #*/
   rule751 ((aglet_bindsImCaseVarExpr)) =
                           /*# LINE 290 "./frontend/Tonic/MkGraph.ag" #*/
                           aglet_bindsImCaseVarExpr
                           /*# LINE 4081 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 292 "./frontend/Tonic/MkGraph.ag" #*/
   rule752 lmCaseVarExpr =
                             /*# LINE 292 "./frontend/Tonic/MkGraph.ag" #*/
                             lmCaseVarExpr
                             /*# LINE 4086 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 294 "./frontend/Tonic/MkGraph.ag" #*/
   rule753  (_) =
                      /*# LINE 294 "./frontend/Tonic/MkGraph.ag" #*/
                      False
                      /*# LINE 4091 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 296 "./frontend/Tonic/MkGraph.ag" #*/
   rule754 ((aglet_exprImEntryId)) ((aglet_exprIrecNode)) ((alhsImergeId)) =
                     /*# LINE 296 "./frontend/Tonic/MkGraph.ag" #*/
                     if aglet_exprIrecNode (Just alhsImergeId) aglet_exprImEntryId
                     /*# LINE 4096 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 138 "./frontend/Tonic/Pretty.ag" #*/
   rule755 ((aglet_bindsIppDebugs)) =
                         /*# LINE 138 "./frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppDebugs
                         /*# LINE 4101 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 139 "./frontend/Tonic/Pretty.ag" #*/
   rule756 ((aglet_bindsIppAgs)) =
                         /*# LINE 139 "./frontend/Tonic/Pretty.ag" #*/
                         vcat aglet_bindsIppAgs
                         /*# LINE 4106 "frontend/Tonic/Tonic.icl"#*/
   rule757 ((aglet_bindsIhasRecs)) ((aglet_exprIhasRecs)) =
     aglet_bindsIhasRecs || aglet_exprIhasRecs
   rule758 ((aglet_bindsImEntryId)) ((aglet_exprImEntryId)) =
     aglet_bindsImEntryId <> aglet_exprImEntryId
   rule759 ((aglet_bindsImExitId)) ((aglet_exprImExitId)) =
     aglet_bindsImExitId <> aglet_exprImExitId
   rule760 ((aglet_bindsIppAgs)) ((aglet_exprIppAgs)) =
     aglet_bindsIppAgs ++ aglet_exprIppAgs
   rule761 ((aglet_bindsIppDebugs)) ((aglet_exprIppDebugs)) =
     aglet_bindsIppDebugs ++ aglet_exprIppDebugs
   rule762 ((aglet_bindsIcopy)) ((aglet_exprIcopy)) =
     {GLet|glet_binds = aglet_bindsIcopy , glet_expr = aglet_exprIcopy}
   rule763 lcopy =
     lcopy
   rule764 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule765 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule766 ((alhsIgraph)) =
     alhsIgraph
   rule767 ((alhsImergeId)) =
     alhsImergeId
   rule768 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule769 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule770 ((aglet_bindsIgraph)) =
     aglet_bindsIgraph
   rule771 ((alhsImergeId)) =
     alhsImergeId
   rule772 ((alhsImoduleEnv)) =
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
     lift (T_GLetBind_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLetBind_s38 sem arg) >>= \ (T_GLetBind_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLetBind alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLetBind :: GLetBind  -> T_GLetBind 
sem_GLetBind { GLetBind | glb_dst = glb_dst_,glb_src = glb_src_ } = sem_GLetBind_GLetBind glb_dst_ ( sem_Expression glb_src_ )

// semantic domain
:: T_GLetBind  = T_GLetBind (Identity (T_GLetBind_s38 ))
attach_T_GLetBind (T_GLetBind t_GLetBind) = t_GLetBind
inv_GLetBind_s38 (C_GLetBind_s38 x) = x
sem_GLetBind_GLetBind  :: (String) (T_Expression ) -> T_GLetBind 
sem_GLetBind_GLetBind arg_glb_dst_ arg_glb_src_ = T_GLetBind (lift st38) where
   st38 =
         let
             v37 (T_GLetBind_vIn37 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_glb_srcX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_glb_src_))
                           (T_Expression_vOut13 aglb_srcIcopy aglb_srcIgraph aglb_srcIhasRecs aglb_srcImEntryId aglb_srcImExitId aglb_srcIppAg aglb_srcIppAgs aglb_srcIppDebug aglb_srcIppDebugs aglb_srcIrecNode) = inv_Expression_s14 st_glb_srcX14 (T_Expression_vIn13 aglb_srcOcaseExpr aglb_srcOcurrTaskName aglb_srcOgraph aglb_srcOmergeId aglb_srcOmoduleEnv)
                           alhsOmCaseVarExpr = rule773 arg_glb_dst_
                           alhsOppDebug = rule774 aglb_srcIppDebug arg_glb_dst_
                           alhsOppAg = rule775 aglb_srcIppAg arg_glb_dst_
                           alhsOhasRecs = rule776 aglb_srcIhasRecs
                           alhsOmEntryId = rule777 aglb_srcImEntryId
                           alhsOmExitId = rule778 aglb_srcImExitId
                           alhsOppAgs = rule779 aglb_srcIppAgs
                           alhsOppDebugs = rule780 aglb_srcIppDebugs
                           alhsOrecNode = rule781 aglb_srcIrecNode
                           lcopy = rule782 aglb_srcIcopy arg_glb_dst_
                           alhsOcopy = rule783 lcopy
                           alhsOgraph = rule784 aglb_srcIgraph
                           aglb_srcOcaseExpr = rule785 alhsIcaseExpr
                           aglb_srcOcurrTaskName = rule786 alhsIcurrTaskName
                           aglb_srcOgraph = rule787 alhsIgraph
                           aglb_srcOmergeId = rule788 alhsImergeId
                           aglb_srcOmoduleEnv = rule789 alhsImoduleEnv
                           ag__result_ = T_GLetBind_vOut37 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBind_s38 v37
   /*# LINE 306 "./frontend/Tonic/MkGraph.ag" #*/
   rule773 glb_dst_ =
                                  /*# LINE 306 "./frontend/Tonic/MkGraph.ag" #*/
                                  if (glb_dst_ == "_case_var") undef Nothing
                                  /*# LINE 4223 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 142 "./frontend/Tonic/Pretty.ag" #*/
   rule774 ((aglb_srcIppDebug)) glb_dst_ =
                             /*# LINE 142 "./frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppDebug
                             /*# LINE 4228 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 143 "./frontend/Tonic/Pretty.ag" #*/
   rule775 ((aglb_srcIppAg)) glb_dst_ =
                             /*# LINE 143 "./frontend/Tonic/Pretty.ag" #*/
                             text glb_dst_ <+> equals <+> aglb_srcIppAg
                             /*# LINE 4233 "frontend/Tonic/Tonic.icl"#*/
   rule776 ((aglb_srcIhasRecs)) =
     aglb_srcIhasRecs
   rule777 ((aglb_srcImEntryId)) =
     aglb_srcImEntryId
   rule778 ((aglb_srcImExitId)) =
     aglb_srcImExitId
   rule779 ((aglb_srcIppAgs)) =
     aglb_srcIppAgs
   rule780 ((aglb_srcIppDebugs)) =
     aglb_srcIppDebugs
   rule781 ((aglb_srcIrecNode)) =
     aglb_srcIrecNode
   rule782 ((aglb_srcIcopy)) glb_dst_ =
     {GLetBind|glb_dst = glb_dst_ , glb_src = aglb_srcIcopy}
   rule783 lcopy =
     lcopy
   rule784 ((aglb_srcIgraph)) =
     aglb_srcIgraph
   rule785 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule786 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule787 ((alhsIgraph)) =
     alhsIgraph
   rule788 ((alhsImergeId)) =
     alhsImergeId
   rule789 ((alhsImoduleEnv)) =
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
     lift (T_GLetBinds_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GLetBinds_s41 sem arg) >>= \ (T_GLetBinds_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GLetBinds alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GLetBinds :: GLetBinds  -> T_GLetBinds 
sem_GLetBinds list = foldr sem_GLetBinds_Cons sem_GLetBinds_Nil (map sem_GLetBind list)

// semantic domain
:: T_GLetBinds  = T_GLetBinds (Identity (T_GLetBinds_s41 ))
attach_T_GLetBinds (T_GLetBinds t_GLetBinds) = t_GLetBinds
inv_GLetBinds_s41 (C_GLetBinds_s41 x) = x
sem_GLetBinds_Cons  :: (T_GLetBind ) (T_GLetBinds ) -> T_GLetBinds 
sem_GLetBinds_Cons arg_hd_ arg_tl_ = T_GLetBinds (lift st41) where
   st41 =
         let
             v40 (T_GLetBinds_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX38 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBind (arg_hd_))
                           st_tlX41 = 'Control.Monad.Identity'.runIdentity (attach_T_GLetBinds (arg_tl_))
                           (T_GLetBind_vOut37 ahdIcopy ahdIgraph ahdIhasRecs ahdImCaseVarExpr ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_GLetBind_s38 st_hdX38 (T_GLetBind_vIn37 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_GLetBinds_vOut40 atlIcopy atlIgraph atlIhasRecs atlImCaseVarExpr atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_GLetBinds_s41 st_tlX41 (T_GLetBinds_vIn40 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOmCaseVarExpr = rule790 ahdImCaseVarExpr atlImCaseVarExpr
                           alhsOhasRecs = rule791 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule792 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule793 ahdImExitId atlImExitId
                           alhsOppAg = rule794 ahdIppAg atlIppAg
                           alhsOppAgs = rule795 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule796 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule797 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule798 ahdIrecNode atlIrecNode
                           lcopy = rule799 ahdIcopy atlIcopy
                           alhsOcopy = rule800 lcopy
                           alhsOgraph = rule801 atlIgraph
                           ahdOcaseExpr = rule802 alhsIcaseExpr
                           ahdOcurrTaskName = rule803 alhsIcurrTaskName
                           ahdOgraph = rule804 alhsIgraph
                           ahdOmergeId = rule805 alhsImergeId
                           ahdOmoduleEnv = rule806 alhsImoduleEnv
                           atlOcaseExpr = rule807 alhsIcaseExpr
                           atlOcurrTaskName = rule808 alhsIcurrTaskName
                           atlOgraph = rule809 ahdIgraph
                           atlOmergeId = rule810 alhsImergeId
                           atlOmoduleEnv = rule811 alhsImoduleEnv
                           ag__result_ = T_GLetBinds_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBinds_s41 v40
   /*# LINE 302 "./frontend/Tonic/MkGraph.ag" #*/
   rule790 ((ahdImCaseVarExpr)) ((atlImCaseVarExpr)) =
                               /*# LINE 302 "./frontend/Tonic/MkGraph.ag" #*/
                               ahdImCaseVarExpr <> atlImCaseVarExpr
                               /*# LINE 4353 "frontend/Tonic/Tonic.icl"#*/
   rule791 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule792 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule793 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule794 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule795 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule796 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule797 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule798 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule799 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule800 lcopy =
     lcopy
   rule801 ((atlIgraph)) =
     atlIgraph
   rule802 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule803 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule804 ((alhsIgraph)) =
     alhsIgraph
   rule805 ((alhsImergeId)) =
     alhsImergeId
   rule806 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule807 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule808 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule809 ((ahdIgraph)) =
     ahdIgraph
   rule810 ((alhsImergeId)) =
     alhsImergeId
   rule811 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_GLetBinds_Nil  ::   T_GLetBinds 
sem_GLetBinds_Nil  = T_GLetBinds (lift st41) where
   st41 =
         let
             v40 (T_GLetBinds_vIn40 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOmCaseVarExpr = rule812  Void
                           alhsOhasRecs = rule813  Void
                           alhsOmEntryId = rule814  Void
                           alhsOmExitId = rule815  Void
                           alhsOppAg = rule816  Void
                           alhsOppAgs = rule817  Void
                           alhsOppDebug = rule818  Void
                           alhsOppDebugs = rule819  Void
                           alhsOrecNode = rule820  Void
                           lcopy = rule821  Void
                           alhsOcopy = rule822 lcopy
                           alhsOgraph = rule823 alhsIgraph
                           ag__result_ = T_GLetBinds_vOut40 alhsOcopy alhsOgraph alhsOhasRecs alhsOmCaseVarExpr alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GLetBinds_s41 v40
   /*# LINE 303 "./frontend/Tonic/MkGraph.ag" #*/
   rule812  (_) =
                               /*# LINE 303 "./frontend/Tonic/MkGraph.ag" #*/
                               Nothing
                               /*# LINE 4421 "frontend/Tonic/Tonic.icl"#*/
   rule813  (_) =
     False
   rule814  (_) =
     Nothing
   rule815  (_) =
     Nothing
   rule816  (_) =
     empty
   rule817  (_) =
     []
   rule818  (_) =
     empty
   rule819  (_) =
     []
   rule820  (_) =
     False
   rule821  (_) =
     []
   rule822 lcopy =
     lcopy
   rule823 ((alhsIgraph)) =
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
     lift (T_GlobalDefinedSymbol_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_GlobalDefinedSymbol_s44 sem arg) >>= \ (T_GlobalDefinedSymbol_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_GlobalDefinedSymbol alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_GlobalDefinedSymbol :: GlobalDefinedSymbol  -> T_GlobalDefinedSymbol 
sem_GlobalDefinedSymbol (x1) = sem_GlobalDefinedSymbol_Tuple x1

// semantic domain
:: T_GlobalDefinedSymbol  = T_GlobalDefinedSymbol (Identity (T_GlobalDefinedSymbol_s44 ))
attach_T_GlobalDefinedSymbol (T_GlobalDefinedSymbol t_GlobalDefinedSymbol) = t_GlobalDefinedSymbol
inv_GlobalDefinedSymbol_s44 (C_GlobalDefinedSymbol_s44 x) = x
sem_GlobalDefinedSymbol_Tuple  :: (Global DefinedSymbol) -> T_GlobalDefinedSymbol 
sem_GlobalDefinedSymbol_Tuple arg_x1_ = T_GlobalDefinedSymbol (lift st44) where
   st44 =
         let
             v43 (T_GlobalDefinedSymbol_vIn43 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule824  Void
                           alhsOmEntryId = rule825  Void
                           alhsOmExitId = rule826  Void
                           alhsOppAg = rule827  Void
                           alhsOppAgs = rule828  Void
                           alhsOppDebug = rule829  Void
                           alhsOppDebugs = rule830  Void
                           alhsOrecNode = rule831  Void
                           lcopy = rule832 arg_x1_
                           alhsOcopy = rule833 lcopy
                           alhsOgraph = rule834 alhsIgraph
                           ag__result_ = T_GlobalDefinedSymbol_vOut43 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_GlobalDefinedSymbol_s44 v43
   rule824  (_) =
     False
   rule825  (_) =
     Nothing
   rule826  (_) =
     Nothing
   rule827  (_) =
     empty
   rule828  (_) =
     []
   rule829  (_) =
     empty
   rule830  (_) =
     []
   rule831  (_) =
     False
   rule832 x1_ =
     (x1_)
   rule833 lcopy =
     lcopy
   rule834 ((alhsIgraph)) =
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
recNode_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_Ident :: Syn_Ident -> ([Doc])
ppDebugs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_Ident :: Syn_Ident -> (Doc)
ppDebug_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_Ident :: Syn_Ident -> ([Doc])
ppAgs_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_Ident :: Syn_Ident -> (Doc)
ppAg_Syn_Ident (Syn_Ident _ _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mExitId_Syn_Ident (Syn_Ident _ _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_Ident :: Syn_Ident -> (Maybe Int)
mEntryId_Syn_Ident (Syn_Ident _ _ _ _ _ x _ _ _ _ _ _) = x
isCurrTask_Syn_Ident :: Syn_Ident -> (Bool)
isCurrTask_Syn_Ident (Syn_Ident _ _ _ _ x _ _ _ _ _ _ _) = x
ident_Syn_Ident :: Syn_Ident -> (String)
ident_Syn_Ident (Syn_Ident _ _ _ x _ _ _ _ _ _ _ _) = x
hasRecs_Syn_Ident :: Syn_Ident -> (Bool)
hasRecs_Syn_Ident (Syn_Ident _ _ x _ _ _ _ _ _ _ _ _) = x
graph_Syn_Ident :: Syn_Ident -> (GinGraph)
graph_Syn_Ident (Syn_Ident _ x _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_Ident :: Syn_Ident -> (Ident)
copy_Syn_Ident (Syn_Ident x _ _ _ _ _ _ _ _ _ _ _) = x
wrap_Ident :: T_Ident  Inh_Ident  -> (Syn_Ident )
wrap_Ident (T_Ident act) (Inh_Ident alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Ident_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Ident_s47 sem arg) >>= \ (T_Ident_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Ident alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Ident :: Ident  -> T_Ident 
sem_Ident { Ident | id_name = id_name_,id_info = id_info_ } = sem_Ident_Ident id_name_ id_info_

// semantic domain
:: T_Ident  = T_Ident (Identity (T_Ident_s47 ))
attach_T_Ident (T_Ident t_Ident) = t_Ident
inv_Ident_s47 (C_Ident_s47 x) = x
sem_Ident_Ident  :: (String) (SymbolPtr) -> T_Ident 
sem_Ident_Ident arg_id_name_ arg_id_info_ = T_Ident (lift st47) where
   st47 =
         let
             v46 (T_Ident_vIn46 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOisCurrTask = rule835 alhsIcurrTaskName arg_id_name_
                           alhsOident = rule836 arg_id_name_
                           alhsOppDebug = rule837 arg_id_name_
                           alhsOppAg = rule838 arg_id_name_
                           alhsOhasRecs = rule839  Void
                           alhsOmEntryId = rule840  Void
                           alhsOmExitId = rule841  Void
                           alhsOppAgs = rule842  Void
                           alhsOppDebugs = rule843  Void
                           alhsOrecNode = rule844  Void
                           lcopy = rule845 arg_id_info_ arg_id_name_
                           alhsOcopy = rule846 lcopy
                           alhsOgraph = rule847 alhsIgraph
                           ag__result_ = T_Ident_vOut46 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Ident_s47 v46
   /*# LINE 104 "./frontend/Tonic/MkGraph.ag" #*/
   rule835 ((alhsIcurrTaskName)) id_name_ =
                         /*# LINE 104 "./frontend/Tonic/MkGraph.ag" #*/
                         id_name_ == alhsIcurrTaskName
                         /*# LINE 4616 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 105 "./frontend/Tonic/MkGraph.ag" #*/
   rule836 id_name_ =
                         /*# LINE 105 "./frontend/Tonic/MkGraph.ag" #*/
                         id_name_
                         /*# LINE 4621 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 86 "./frontend/Tonic/Pretty.ag" #*/
   rule837 id_name_ =
                          /*# LINE 86 "./frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4626 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 87 "./frontend/Tonic/Pretty.ag" #*/
   rule838 id_name_ =
                          /*# LINE 87 "./frontend/Tonic/Pretty.ag" #*/
                          text id_name_
                          /*# LINE 4631 "frontend/Tonic/Tonic.icl"#*/
   rule839  (_) =
     False
   rule840  (_) =
     Nothing
   rule841  (_) =
     Nothing
   rule842  (_) =
     []
   rule843  (_) =
     []
   rule844  (_) =
     False
   rule845 id_info_ id_name_ =
     {Ident|id_name = id_name_ , id_info = id_info_}
   rule846 lcopy =
     lcopy
   rule847 ((alhsIgraph)) =
     alhsIgraph

// MaybeExpression ---------------------------------------------
// wrapper
moduleEnv_Inh_MaybeExpression :: Inh_MaybeExpression -> (ModuleEnv)
moduleEnv_Inh_MaybeExpression (Inh_MaybeExpression _ _ _ _ x) = x
mergeId_Inh_MaybeExpression :: Inh_MaybeExpression -> (Int)
mergeId_Inh_MaybeExpression (Inh_MaybeExpression _ _ _ x _) = x
graph_Inh_MaybeExpression :: Inh_MaybeExpression -> (GinGraph)
graph_Inh_MaybeExpression (Inh_MaybeExpression _ _ x _ _) = x
currTaskName_Inh_MaybeExpression :: Inh_MaybeExpression -> (String)
currTaskName_Inh_MaybeExpression (Inh_MaybeExpression _ x _ _ _) = x
caseExpr_Inh_MaybeExpression :: Inh_MaybeExpression -> (Maybe Expression)
caseExpr_Inh_MaybeExpression (Inh_MaybeExpression x _ _ _ _) = x
recNode_Syn_MaybeExpression :: Syn_MaybeExpression -> (Bool)
recNode_Syn_MaybeExpression (Syn_MaybeExpression _ _ _ _ x) = x
mExitId_Syn_MaybeExpression :: Syn_MaybeExpression -> (Maybe Int)
mExitId_Syn_MaybeExpression (Syn_MaybeExpression _ _ _ x _) = x
mEntryId_Syn_MaybeExpression :: Syn_MaybeExpression -> (Maybe Int)
mEntryId_Syn_MaybeExpression (Syn_MaybeExpression _ _ x _ _) = x
hasRecs_Syn_MaybeExpression :: Syn_MaybeExpression -> (Bool)
hasRecs_Syn_MaybeExpression (Syn_MaybeExpression _ x _ _ _) = x
graph_Syn_MaybeExpression :: Syn_MaybeExpression -> (GinGraph)
graph_Syn_MaybeExpression (Syn_MaybeExpression x _ _ _ _) = x
wrap_MaybeExpression :: T_MaybeExpression  Inh_MaybeExpression  -> (Syn_MaybeExpression )
wrap_MaybeExpression (T_MaybeExpression act) (Inh_MaybeExpression alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_MaybeExpression_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_MaybeExpression_s50 sem arg) >>= \ (T_MaybeExpression_vOut49 alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode) ->
     lift (Syn_MaybeExpression alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode)
   )

// cata
sem_MaybeExpression :: MaybeExpression  -> T_MaybeExpression 
sem_MaybeExpression 'Data.Maybe'.Nothing = sem_MaybeExpression_Nothing
sem_MaybeExpression ('Data.Maybe'.Just just) = sem_MaybeExpression_Just (sem_Expression just)

// semantic domain
:: T_MaybeExpression  = T_MaybeExpression (Identity (T_MaybeExpression_s50 ))
attach_T_MaybeExpression (T_MaybeExpression t_MaybeExpression) = t_MaybeExpression
inv_MaybeExpression_s50 (C_MaybeExpression_s50 x) = x
sem_MaybeExpression_Just  :: (T_Expression ) -> T_MaybeExpression 
sem_MaybeExpression_Just arg_just_ = T_MaybeExpression (lift st50) where
   st50 =
         let
             v49 (T_MaybeExpression_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_justX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_just_))
                           (T_Expression_vOut13 ajustIcopy ajustIgraph ajustIhasRecs ajustImEntryId ajustImExitId ajustIppAg ajustIppAgs ajustIppDebug ajustIppDebugs ajustIrecNode) = inv_Expression_s14 st_justX14 (T_Expression_vIn13 ajustOcaseExpr ajustOcurrTaskName ajustOgraph ajustOmergeId ajustOmoduleEnv)
                           alhsOhasRecs = rule848 ajustIhasRecs
                           alhsOmEntryId = rule849 ajustImEntryId
                           alhsOmExitId = rule850 ajustImExitId
                           alhsOrecNode = rule851 ajustIrecNode
                           alhsOgraph = rule852 ajustIgraph
                           ajustOcaseExpr = rule853 alhsIcaseExpr
                           ajustOcurrTaskName = rule854 alhsIcurrTaskName
                           ajustOgraph = rule855 alhsIgraph
                           ajustOmergeId = rule856 alhsImergeId
                           ajustOmoduleEnv = rule857 alhsImoduleEnv
                           ag__result_ = T_MaybeExpression_vOut49 alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_MaybeExpression_s50 v49
   rule848 ((ajustIhasRecs)) =
     ajustIhasRecs
   rule849 ((ajustImEntryId)) =
     ajustImEntryId
   rule850 ((ajustImExitId)) =
     ajustImExitId
   rule851 ((ajustIrecNode)) =
     ajustIrecNode
   rule852 ((ajustIgraph)) =
     ajustIgraph
   rule853 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule854 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule855 ((alhsIgraph)) =
     alhsIgraph
   rule856 ((alhsImergeId)) =
     alhsImergeId
   rule857 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_MaybeExpression_Nothing  ::   T_MaybeExpression 
sem_MaybeExpression_Nothing  = T_MaybeExpression (lift st50) where
   st50 =
         let
             v49 (T_MaybeExpression_vIn49 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule858  Void
                           alhsOmEntryId = rule859  Void
                           alhsOmExitId = rule860  Void
                           alhsOrecNode = rule861  Void
                           alhsOgraph = rule862 alhsIgraph
                           ag__result_ = T_MaybeExpression_vOut49 alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOrecNode
                       in ag__result_
         in C_MaybeExpression_s50 v49
   rule858  (_) =
     False
   rule859  (_) =
     Nothing
   rule860  (_) =
     Nothing
   rule861  (_) =
     False
   rule862 ((alhsIgraph)) =
     alhsIgraph

// Priority ----------------------------------------------------
// wrapper
moduleEnv_Inh_Priority :: Inh_Priority -> (ModuleEnv)
moduleEnv_Inh_Priority (Inh_Priority _ _ _ _ x) = x
mergeId_Inh_Priority :: Inh_Priority -> (Int)
mergeId_Inh_Priority (Inh_Priority _ _ _ x _) = x
graph_Inh_Priority :: Inh_Priority -> (GinGraph)
graph_Inh_Priority (Inh_Priority _ _ x _ _) = x
currTaskName_Inh_Priority :: Inh_Priority -> (String)
currTaskName_Inh_Priority (Inh_Priority _ x _ _ _) = x
caseExpr_Inh_Priority :: Inh_Priority -> (Maybe Expression)
caseExpr_Inh_Priority (Inh_Priority x _ _ _ _) = x
graph_Syn_Priority :: Syn_Priority -> (GinGraph)
graph_Syn_Priority (Syn_Priority _ x) = x
copy_Syn_Priority :: Syn_Priority -> (Priority)
copy_Syn_Priority (Syn_Priority x _) = x
wrap_Priority :: T_Priority  Inh_Priority  -> (Syn_Priority )
wrap_Priority (T_Priority act) (Inh_Priority alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Priority_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Priority_s53 sem arg) >>= \ (T_Priority_vOut52 alhsOcopy alhsOgraph) ->
     lift (Syn_Priority alhsOcopy alhsOgraph)
   )

// cata
sem_Priority :: Priority  -> T_Priority 
sem_Priority ( Prio assoc_ prio_ ) = sem_Priority_Prio assoc_ prio_
sem_Priority ( NoPrio  ) = sem_Priority_NoPrio 

// semantic domain
:: T_Priority  = T_Priority (Identity (T_Priority_s53 ))
attach_T_Priority (T_Priority t_Priority) = t_Priority
inv_Priority_s53 (C_Priority_s53 x) = x
sem_Priority_Prio  :: (Assoc) (Int) -> T_Priority 
sem_Priority_Prio arg_assoc_ arg_prio_ = T_Priority (lift st53) where
   st53 =
         let
             v52 (T_Priority_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           lcopy = rule863 arg_assoc_ arg_prio_
                           alhsOcopy = rule864 lcopy
                           alhsOgraph = rule865 alhsIgraph
                           ag__result_ = T_Priority_vOut52 alhsOcopy alhsOgraph
                       in ag__result_
         in C_Priority_s53 v52
   rule863 assoc_ prio_ =
     Prio assoc_ prio_
   rule864 lcopy =
     lcopy
   rule865 ((alhsIgraph)) =
     alhsIgraph
sem_Priority_NoPrio  ::   T_Priority 
sem_Priority_NoPrio  = T_Priority (lift st53) where
   st53 =
         let
             v52 (T_Priority_vIn52 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           lcopy = rule866  Void
                           alhsOcopy = rule867 lcopy
                           alhsOgraph = rule868 alhsIgraph
                           ag__result_ = T_Priority_vOut52 alhsOcopy alhsOgraph
                       in ag__result_
         in C_Priority_s53 v52
   rule866  (_) =
     NoPrio
   rule867 lcopy =
     lcopy
   rule868 ((alhsIgraph)) =
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
     lift (T_Selection_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Selection_s56 sem arg) >>= \ (T_Selection_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Selection alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Selection :: Selection  -> T_Selection 
sem_Selection ( RecordSelection gds_ n_ ) = sem_Selection_RecordSelection ( sem_GlobalDefinedSymbol gds_ ) n_
sem_Selection ( ArraySelection gds_ eiptr_ expr_ ) = sem_Selection_ArraySelection ( sem_GlobalDefinedSymbol gds_ ) eiptr_ ( sem_Expression expr_ )
sem_Selection ( DictionarySelection bv_ sels_ eiptr_ expr_ ) = sem_Selection_DictionarySelection ( sem_BoundVar bv_ ) ( sem_Selections sels_ ) eiptr_ ( sem_Expression expr_ )

// semantic domain
:: T_Selection  = T_Selection (Identity (T_Selection_s56 ))
attach_T_Selection (T_Selection t_Selection) = t_Selection
inv_Selection_s56 (C_Selection_s56 x) = x
sem_Selection_RecordSelection  :: (T_GlobalDefinedSymbol ) (Int) -> T_Selection 
sem_Selection_RecordSelection arg_gds_ arg_n_ = T_Selection (lift st56) where
   st56 =
         let
             v55 (T_Selection_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsX44 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           (T_GlobalDefinedSymbol_vOut43 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s44 st_gdsX44 (T_GlobalDefinedSymbol_vIn43 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           alhsOppDebug = rule869 agdsIppDebug
                           alhsOppAg = rule870 agdsIppAg
                           alhsOhasRecs = rule871 agdsIhasRecs
                           alhsOmEntryId = rule872 agdsImEntryId
                           alhsOmExitId = rule873 agdsImExitId
                           alhsOppAgs = rule874 agdsIppAgs
                           alhsOppDebugs = rule875 agdsIppDebugs
                           alhsOrecNode = rule876 agdsIrecNode
                           lcopy = rule877 agdsIcopy arg_n_
                           alhsOcopy = rule878 lcopy
                           alhsOgraph = rule879 agdsIgraph
                           agdsOcaseExpr = rule880 alhsIcaseExpr
                           agdsOcurrTaskName = rule881 alhsIcurrTaskName
                           agdsOgraph = rule882 alhsIgraph
                           agdsOmergeId = rule883 alhsImergeId
                           agdsOmoduleEnv = rule884 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s56 v55
   /*# LINE 120 "./frontend/Tonic/Pretty.ag" #*/
   rule869 ((agdsIppDebug)) =
                                        /*# LINE 120 "./frontend/Tonic/Pretty.ag" #*/
                                        agdsIppDebug
                                        /*# LINE 4910 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 121 "./frontend/Tonic/Pretty.ag" #*/
   rule870 ((agdsIppAg)) =
                                        /*# LINE 121 "./frontend/Tonic/Pretty.ag" #*/
                                        agdsIppAg
                                        /*# LINE 4915 "frontend/Tonic/Tonic.icl"#*/
   rule871 ((agdsIhasRecs)) =
     agdsIhasRecs
   rule872 ((agdsImEntryId)) =
     agdsImEntryId
   rule873 ((agdsImExitId)) =
     agdsImExitId
   rule874 ((agdsIppAgs)) =
     agdsIppAgs
   rule875 ((agdsIppDebugs)) =
     agdsIppDebugs
   rule876 ((agdsIrecNode)) =
     agdsIrecNode
   rule877 ((agdsIcopy)) n_ =
     RecordSelection agdsIcopy n_
   rule878 lcopy =
     lcopy
   rule879 ((agdsIgraph)) =
     agdsIgraph
   rule880 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule881 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule882 ((alhsIgraph)) =
     alhsIgraph
   rule883 ((alhsImergeId)) =
     alhsImergeId
   rule884 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selection_ArraySelection  :: (T_GlobalDefinedSymbol ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_ArraySelection arg_gds_ arg_eiptr_ arg_expr_ = T_Selection (lift st56) where
   st56 =
         let
             v55 (T_Selection_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_gdsX44 = 'Control.Monad.Identity'.runIdentity (attach_T_GlobalDefinedSymbol (arg_gds_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_GlobalDefinedSymbol_vOut43 agdsIcopy agdsIgraph agdsIhasRecs agdsImEntryId agdsImExitId agdsIppAg agdsIppAgs agdsIppDebug agdsIppDebugs agdsIrecNode) = inv_GlobalDefinedSymbol_s44 st_gdsX44 (T_GlobalDefinedSymbol_vIn43 agdsOcaseExpr agdsOcurrTaskName agdsOgraph agdsOmergeId agdsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule885  Void
                           alhsOppAg = rule886  Void
                           alhsOhasRecs = rule887 aexprIhasRecs agdsIhasRecs
                           alhsOmEntryId = rule888 aexprImEntryId agdsImEntryId
                           alhsOmExitId = rule889 aexprImExitId agdsImExitId
                           alhsOppAgs = rule890 aexprIppAgs agdsIppAgs
                           alhsOppDebugs = rule891 aexprIppDebugs agdsIppDebugs
                           alhsOrecNode = rule892 aexprIrecNode agdsIrecNode
                           lcopy = rule893 aexprIcopy agdsIcopy arg_eiptr_
                           alhsOcopy = rule894 lcopy
                           alhsOgraph = rule895 aexprIgraph
                           agdsOcaseExpr = rule896 alhsIcaseExpr
                           agdsOcurrTaskName = rule897 alhsIcurrTaskName
                           agdsOgraph = rule898 alhsIgraph
                           agdsOmergeId = rule899 alhsImergeId
                           agdsOmoduleEnv = rule900 alhsImoduleEnv
                           aexprOcaseExpr = rule901 alhsIcaseExpr
                           aexprOcurrTaskName = rule902 alhsIcurrTaskName
                           aexprOgraph = rule903 agdsIgraph
                           aexprOmergeId = rule904 alhsImergeId
                           aexprOmoduleEnv = rule905 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s56 v55
   /*# LINE 122 "./frontend/Tonic/Pretty.ag" #*/
   rule885  (_) =
                                        /*# LINE 122 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 4982 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 123 "./frontend/Tonic/Pretty.ag" #*/
   rule886  (_) =
                                        /*# LINE 123 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: ArraySelection"
                                        /*# LINE 4987 "frontend/Tonic/Tonic.icl"#*/
   rule887 ((aexprIhasRecs)) ((agdsIhasRecs)) =
     agdsIhasRecs || aexprIhasRecs
   rule888 ((aexprImEntryId)) ((agdsImEntryId)) =
     agdsImEntryId <> aexprImEntryId
   rule889 ((aexprImExitId)) ((agdsImExitId)) =
     agdsImExitId <> aexprImExitId
   rule890 ((aexprIppAgs)) ((agdsIppAgs)) =
     agdsIppAgs ++ aexprIppAgs
   rule891 ((aexprIppDebugs)) ((agdsIppDebugs)) =
     agdsIppDebugs ++ aexprIppDebugs
   rule892 ((aexprIrecNode)) ((agdsIrecNode)) =
     agdsIrecNode || aexprIrecNode
   rule893 ((aexprIcopy)) ((agdsIcopy)) eiptr_ =
     ArraySelection agdsIcopy eiptr_ aexprIcopy
   rule894 lcopy =
     lcopy
   rule895 ((aexprIgraph)) =
     aexprIgraph
   rule896 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule897 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule898 ((alhsIgraph)) =
     alhsIgraph
   rule899 ((alhsImergeId)) =
     alhsImergeId
   rule900 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule901 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule902 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule903 ((agdsIgraph)) =
     agdsIgraph
   rule904 ((alhsImergeId)) =
     alhsImergeId
   rule905 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selection_DictionarySelection  :: (T_BoundVar ) (T_Selections ) (ExprInfoPtr) (T_Expression ) -> T_Selection 
sem_Selection_DictionarySelection arg_bv_ arg_sels_ arg_eiptr_ arg_expr_ = T_Selection (lift st56) where
   st56 =
         let
             v55 (T_Selection_vIn55 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_bvX8 = 'Control.Monad.Identity'.runIdentity (attach_T_BoundVar (arg_bv_))
                           st_selsX59 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_sels_))
                           st_exprX14 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                           (T_BoundVar_vOut7 abvIcopy abvIgraph abvIhasRecs abvImEntryId abvImExitId abvIppAg abvIppAgs abvIppDebug abvIppDebugs abvIrecNode) = inv_BoundVar_s8 st_bvX8 (T_BoundVar_vIn7 abvOcaseExpr abvOcurrTaskName abvOgraph abvOmergeId abvOmoduleEnv)
                           (T_Selections_vOut58 aselsIcopy aselsIgraph aselsIhasRecs aselsImEntryId aselsImExitId aselsIppAg aselsIppAgs aselsIppDebug aselsIppDebugs aselsIrecNode) = inv_Selections_s59 st_selsX59 (T_Selections_vIn58 aselsOcaseExpr aselsOcurrTaskName aselsOgraph aselsOmergeId aselsOmoduleEnv)
                           (T_Expression_vOut13 aexprIcopy aexprIgraph aexprIhasRecs aexprImEntryId aexprImExitId aexprIppAg aexprIppAgs aexprIppDebug aexprIppDebugs aexprIrecNode) = inv_Expression_s14 st_exprX14 (T_Expression_vIn13 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                           alhsOppDebug = rule906  Void
                           alhsOppAg = rule907  Void
                           alhsOhasRecs = rule908 abvIhasRecs aexprIhasRecs aselsIhasRecs
                           alhsOmEntryId = rule909 abvImEntryId aexprImEntryId aselsImEntryId
                           alhsOmExitId = rule910 abvImExitId aexprImExitId aselsImExitId
                           alhsOppAgs = rule911 abvIppAgs aexprIppAgs aselsIppAgs
                           alhsOppDebugs = rule912 abvIppDebugs aexprIppDebugs aselsIppDebugs
                           alhsOrecNode = rule913 abvIrecNode aexprIrecNode aselsIrecNode
                           lcopy = rule914 abvIcopy aexprIcopy aselsIcopy arg_eiptr_
                           alhsOcopy = rule915 lcopy
                           alhsOgraph = rule916 aexprIgraph
                           abvOcaseExpr = rule917 alhsIcaseExpr
                           abvOcurrTaskName = rule918 alhsIcurrTaskName
                           abvOgraph = rule919 alhsIgraph
                           abvOmergeId = rule920 alhsImergeId
                           abvOmoduleEnv = rule921 alhsImoduleEnv
                           aselsOcaseExpr = rule922 alhsIcaseExpr
                           aselsOcurrTaskName = rule923 alhsIcurrTaskName
                           aselsOgraph = rule924 abvIgraph
                           aselsOmergeId = rule925 alhsImergeId
                           aselsOmoduleEnv = rule926 alhsImoduleEnv
                           aexprOcaseExpr = rule927 alhsIcaseExpr
                           aexprOcurrTaskName = rule928 alhsIcurrTaskName
                           aexprOgraph = rule929 aselsIgraph
                           aexprOmergeId = rule930 alhsImergeId
                           aexprOmoduleEnv = rule931 alhsImoduleEnv
                           ag__result_ = T_Selection_vOut55 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selection_s56 v55
   /*# LINE 124 "./frontend/Tonic/Pretty.ag" #*/
   rule906  (_) =
                                        /*# LINE 124 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 5071 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 125 "./frontend/Tonic/Pretty.ag" #*/
   rule907  (_) =
                                        /*# LINE 125 "./frontend/Tonic/Pretty.ag" #*/
                                        text "TODO: DictionarySelection"
                                        /*# LINE 5076 "frontend/Tonic/Tonic.icl"#*/
   rule908 ((abvIhasRecs)) ((aexprIhasRecs)) ((aselsIhasRecs)) =
     abvIhasRecs || aselsIhasRecs || aexprIhasRecs
   rule909 ((abvImEntryId)) ((aexprImEntryId)) ((aselsImEntryId)) =
     abvImEntryId <> aselsImEntryId <> aexprImEntryId
   rule910 ((abvImExitId)) ((aexprImExitId)) ((aselsImExitId)) =
     abvImExitId <> aselsImExitId <> aexprImExitId
   rule911 ((abvIppAgs)) ((aexprIppAgs)) ((aselsIppAgs)) =
     abvIppAgs ++ aselsIppAgs ++ aexprIppAgs
   rule912 ((abvIppDebugs)) ((aexprIppDebugs)) ((aselsIppDebugs)) =
     abvIppDebugs ++ aselsIppDebugs ++ aexprIppDebugs
   rule913 ((abvIrecNode)) ((aexprIrecNode)) ((aselsIrecNode)) =
     abvIrecNode || aselsIrecNode || aexprIrecNode
   rule914 ((abvIcopy)) ((aexprIcopy)) ((aselsIcopy)) eiptr_ =
     DictionarySelection abvIcopy aselsIcopy eiptr_ aexprIcopy
   rule915 lcopy =
     lcopy
   rule916 ((aexprIgraph)) =
     aexprIgraph
   rule917 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule918 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule919 ((alhsIgraph)) =
     alhsIgraph
   rule920 ((alhsImergeId)) =
     alhsImergeId
   rule921 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule922 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule923 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule924 ((abvIgraph)) =
     abvIgraph
   rule925 ((alhsImergeId)) =
     alhsImergeId
   rule926 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule927 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule928 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule929 ((aselsIgraph)) =
     aselsIgraph
   rule930 ((alhsImergeId)) =
     alhsImergeId
   rule931 ((alhsImoduleEnv)) =
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
     lift (T_Selections_vIn58 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Selections_s59 sem arg) >>= \ (T_Selections_vOut58 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_Selections alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_Selections :: Selections  -> T_Selections 
sem_Selections list = foldr sem_Selections_Cons sem_Selections_Nil (map sem_Selection list)

// semantic domain
:: T_Selections  = T_Selections (Identity (T_Selections_s59 ))
attach_T_Selections (T_Selections t_Selections) = t_Selections
inv_Selections_s59 (C_Selections_s59 x) = x
sem_Selections_Cons  :: (T_Selection ) (T_Selections ) -> T_Selections 
sem_Selections_Cons arg_hd_ arg_tl_ = T_Selections (lift st59) where
   st59 =
         let
             v58 (T_Selections_vIn58 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_hdX56 = 'Control.Monad.Identity'.runIdentity (attach_T_Selection (arg_hd_))
                           st_tlX59 = 'Control.Monad.Identity'.runIdentity (attach_T_Selections (arg_tl_))
                           (T_Selection_vOut55 ahdIcopy ahdIgraph ahdIhasRecs ahdImEntryId ahdImExitId ahdIppAg ahdIppAgs ahdIppDebug ahdIppDebugs ahdIrecNode) = inv_Selection_s56 st_hdX56 (T_Selection_vIn55 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                           (T_Selections_vOut58 atlIcopy atlIgraph atlIhasRecs atlImEntryId atlImExitId atlIppAg atlIppAgs atlIppDebug atlIppDebugs atlIrecNode) = inv_Selections_s59 st_tlX59 (T_Selections_vIn58 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                           alhsOhasRecs = rule932 ahdIhasRecs atlIhasRecs
                           alhsOmEntryId = rule933 ahdImEntryId atlImEntryId
                           alhsOmExitId = rule934 ahdImExitId atlImExitId
                           alhsOppAg = rule935 ahdIppAg atlIppAg
                           alhsOppAgs = rule936 ahdIppAgs atlIppAgs
                           alhsOppDebug = rule937 ahdIppDebug atlIppDebug
                           alhsOppDebugs = rule938 ahdIppDebugs atlIppDebugs
                           alhsOrecNode = rule939 ahdIrecNode atlIrecNode
                           lcopy = rule940 ahdIcopy atlIcopy
                           alhsOcopy = rule941 lcopy
                           alhsOgraph = rule942 atlIgraph
                           ahdOcaseExpr = rule943 alhsIcaseExpr
                           ahdOcurrTaskName = rule944 alhsIcurrTaskName
                           ahdOgraph = rule945 alhsIgraph
                           ahdOmergeId = rule946 alhsImergeId
                           ahdOmoduleEnv = rule947 alhsImoduleEnv
                           atlOcaseExpr = rule948 alhsIcaseExpr
                           atlOcurrTaskName = rule949 alhsIcurrTaskName
                           atlOgraph = rule950 ahdIgraph
                           atlOmergeId = rule951 alhsImergeId
                           atlOmoduleEnv = rule952 alhsImoduleEnv
                           ag__result_ = T_Selections_vOut58 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selections_s59 v58
   rule932 ((ahdIhasRecs)) ((atlIhasRecs)) =
     ahdIhasRecs || atlIhasRecs
   rule933 ((ahdImEntryId)) ((atlImEntryId)) =
     ahdImEntryId <> atlImEntryId
   rule934 ((ahdImExitId)) ((atlImExitId)) =
     ahdImExitId <> atlImExitId
   rule935 ((ahdIppAg)) ((atlIppAg)) =
     ahdIppAg <$$> atlIppAg
   rule936 ((ahdIppAgs)) ((atlIppAgs)) =
     ahdIppAgs ++ atlIppAgs
   rule937 ((ahdIppDebug)) ((atlIppDebug)) =
     ahdIppDebug <$$> atlIppDebug
   rule938 ((ahdIppDebugs)) ((atlIppDebugs)) =
     ahdIppDebugs ++ atlIppDebugs
   rule939 ((ahdIrecNode)) ((atlIrecNode)) =
     ahdIrecNode || atlIrecNode
   rule940 ((ahdIcopy)) ((atlIcopy)) =
     (\x xs -> [x:xs]) ahdIcopy atlIcopy
   rule941 lcopy =
     lcopy
   rule942 ((atlIgraph)) =
     atlIgraph
   rule943 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule944 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule945 ((alhsIgraph)) =
     alhsIgraph
   rule946 ((alhsImergeId)) =
     alhsImergeId
   rule947 ((alhsImoduleEnv)) =
     alhsImoduleEnv
   rule948 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule949 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule950 ((ahdIgraph)) =
     ahdIgraph
   rule951 ((alhsImergeId)) =
     alhsImergeId
   rule952 ((alhsImoduleEnv)) =
     alhsImoduleEnv
sem_Selections_Nil  ::   T_Selections 
sem_Selections_Nil  = T_Selections (lift st59) where
   st59 =
         let
             v58 (T_Selections_vIn58 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule953  Void
                           alhsOmEntryId = rule954  Void
                           alhsOmExitId = rule955  Void
                           alhsOppAg = rule956  Void
                           alhsOppAgs = rule957  Void
                           alhsOppDebug = rule958  Void
                           alhsOppDebugs = rule959  Void
                           alhsOrecNode = rule960  Void
                           lcopy = rule961  Void
                           alhsOcopy = rule962 lcopy
                           alhsOgraph = rule963 alhsIgraph
                           ag__result_ = T_Selections_vOut58 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_Selections_s59 v58
   rule953  (_) =
     False
   rule954  (_) =
     Nothing
   rule955  (_) =
     Nothing
   rule956  (_) =
     empty
   rule957  (_) =
     []
   rule958  (_) =
     empty
   rule959  (_) =
     []
   rule960  (_) =
     False
   rule961  (_) =
     []
   rule962 lcopy =
     lcopy
   rule963 ((alhsIgraph)) =
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
recNode_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ _ x) = x
ppDebugs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppDebugs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ _ x _) = x
ppDebug_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppDebug_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ _ x _ _) = x
ppAgs_Syn_SymbIdent :: Syn_SymbIdent -> ([Doc])
ppAgs_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ _ x _ _ _) = x
ppAg_Syn_SymbIdent :: Syn_SymbIdent -> (Doc)
ppAg_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ _ x _ _ _ _) = x
mExitId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mExitId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ _ x _ _ _ _ _) = x
mEntryId_Syn_SymbIdent :: Syn_SymbIdent -> (Maybe Int)
mEntryId_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ _ x _ _ _ _ _ _) = x
isCurrTask_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
isCurrTask_Syn_SymbIdent (Syn_SymbIdent _ _ _ _ x _ _ _ _ _ _ _) = x
ident_Syn_SymbIdent :: Syn_SymbIdent -> (String)
ident_Syn_SymbIdent (Syn_SymbIdent _ _ _ x _ _ _ _ _ _ _ _) = x
hasRecs_Syn_SymbIdent :: Syn_SymbIdent -> (Bool)
hasRecs_Syn_SymbIdent (Syn_SymbIdent _ _ x _ _ _ _ _ _ _ _ _) = x
graph_Syn_SymbIdent :: Syn_SymbIdent -> (GinGraph)
graph_Syn_SymbIdent (Syn_SymbIdent _ x _ _ _ _ _ _ _ _ _ _) = x
copy_Syn_SymbIdent :: Syn_SymbIdent -> (SymbIdent)
copy_Syn_SymbIdent (Syn_SymbIdent x _ _ _ _ _ _ _ _ _ _ _) = x
wrap_SymbIdent :: T_SymbIdent  Inh_SymbIdent  -> (Syn_SymbIdent )
wrap_SymbIdent (T_SymbIdent act) (Inh_SymbIdent alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_SymbIdent_vIn61 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbIdent_s62 sem arg) >>= \ (T_SymbIdent_vOut61 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_SymbIdent alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_SymbIdent :: SymbIdent  -> T_SymbIdent 
sem_SymbIdent { SymbIdent | symb_ident = symb_ident_,symb_kind = symb_kind_ } = sem_SymbIdent_SymbIdent ( sem_Ident symb_ident_ ) symb_kind_

// semantic domain
:: T_SymbIdent  = T_SymbIdent (Identity (T_SymbIdent_s62 ))
attach_T_SymbIdent (T_SymbIdent t_SymbIdent) = t_SymbIdent
inv_SymbIdent_s62 (C_SymbIdent_s62 x) = x
sem_SymbIdent_SymbIdent  :: (T_Ident ) (SymbKind) -> T_SymbIdent 
sem_SymbIdent_SymbIdent arg_symb_ident_ arg_symb_kind_ = T_SymbIdent (lift st62) where
   st62 =
         let
             v61 (T_SymbIdent_vIn61 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           st_symb_identX47 = 'Control.Monad.Identity'.runIdentity (attach_T_Ident (arg_symb_ident_))
                           (T_Ident_vOut46 asymb_identIcopy asymb_identIgraph asymb_identIhasRecs asymb_identIident asymb_identIisCurrTask asymb_identImEntryId asymb_identImExitId asymb_identIppAg asymb_identIppAgs asymb_identIppDebug asymb_identIppDebugs asymb_identIrecNode) = inv_Ident_s47 st_symb_identX47 (T_Ident_vIn46 asymb_identOcaseExpr asymb_identOcurrTaskName asymb_identOgraph asymb_identOmergeId asymb_identOmoduleEnv)
                           alhsOident = rule964 asymb_identIident
                           alhsOisCurrTask = rule965 asymb_identIisCurrTask
                           alhsOppDebug = rule966 asymb_identIppDebug
                           alhsOppAg = rule967 asymb_identIppAg
                           alhsOhasRecs = rule968 asymb_identIhasRecs
                           alhsOmEntryId = rule969 asymb_identImEntryId
                           alhsOmExitId = rule970 asymb_identImExitId
                           alhsOppAgs = rule971 asymb_identIppAgs
                           alhsOppDebugs = rule972 asymb_identIppDebugs
                           alhsOrecNode = rule973 asymb_identIrecNode
                           lcopy = rule974 asymb_identIcopy arg_symb_kind_
                           alhsOcopy = rule975 lcopy
                           alhsOgraph = rule976 asymb_identIgraph
                           asymb_identOcaseExpr = rule977 alhsIcaseExpr
                           asymb_identOcurrTaskName = rule978 alhsIcurrTaskName
                           asymb_identOgraph = rule979 alhsIgraph
                           asymb_identOmergeId = rule980 alhsImergeId
                           asymb_identOmoduleEnv = rule981 alhsImoduleEnv
                           ag__result_ = T_SymbIdent_vOut61 alhsOcopy alhsOgraph alhsOhasRecs alhsOident alhsOisCurrTask alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_SymbIdent_s62 v61
   /*# LINE 109 "./frontend/Tonic/MkGraph.ag" #*/
   rule964 ((asymb_identIident)) =
                               /*# LINE 109 "./frontend/Tonic/MkGraph.ag" #*/
                               trace_n "SymbIdent.ident" $           asymb_identIident
                               /*# LINE 5380 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
   rule965 ((asymb_identIisCurrTask)) =
                               /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
                               trace_n "SymbIdent.isCurrTask" $      asymb_identIisCurrTask
                               /*# LINE 5385 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 98 "./frontend/Tonic/Pretty.ag" #*/
   rule966 ((asymb_identIppDebug)) =
                              /*# LINE 98 "./frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppDebug
                              /*# LINE 5390 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 99 "./frontend/Tonic/Pretty.ag" #*/
   rule967 ((asymb_identIppAg)) =
                              /*# LINE 99 "./frontend/Tonic/Pretty.ag" #*/
                              asymb_identIppAg
                              /*# LINE 5395 "frontend/Tonic/Tonic.icl"#*/
   rule968 ((asymb_identIhasRecs)) =
     asymb_identIhasRecs
   rule969 ((asymb_identImEntryId)) =
     asymb_identImEntryId
   rule970 ((asymb_identImExitId)) =
     asymb_identImExitId
   rule971 ((asymb_identIppAgs)) =
     asymb_identIppAgs
   rule972 ((asymb_identIppDebugs)) =
     asymb_identIppDebugs
   rule973 ((asymb_identIrecNode)) =
     asymb_identIrecNode
   rule974 ((asymb_identIcopy)) symb_kind_ =
     {SymbIdent|symb_ident = asymb_identIcopy , symb_kind = symb_kind_}
   rule975 lcopy =
     lcopy
   rule976 ((asymb_identIgraph)) =
     asymb_identIgraph
   rule977 ((alhsIcaseExpr)) =
     alhsIcaseExpr
   rule978 ((alhsIcurrTaskName)) =
     alhsIcurrTaskName
   rule979 ((alhsIgraph)) =
     alhsIgraph
   rule980 ((alhsImergeId)) =
     alhsImergeId
   rule981 ((alhsImoduleEnv)) =
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
     lift (T_SymbolType_vIn64 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_SymbolType_s65 sem arg) >>= \ (T_SymbolType_vOut64 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode) ->
     lift (Syn_SymbolType alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode)
   )

// cata
sem_SymbolType :: SymbolType  -> T_SymbolType 
sem_SymbolType { SymbolType | st_vars = st_vars_,st_args = st_args_,st_args_strictness = st_args_strictness_,st_arity = st_arity_,st_result = st_result_,st_context = st_context_,st_attr_vars = st_attr_vars_,st_attr_env = st_attr_env_ } = sem_SymbolType_SymbolType st_vars_ st_args_ st_args_strictness_ st_arity_ st_result_ st_context_ st_attr_vars_ st_attr_env_

// semantic domain
:: T_SymbolType  = T_SymbolType (Identity (T_SymbolType_s65 ))
attach_T_SymbolType (T_SymbolType t_SymbolType) = t_SymbolType
inv_SymbolType_s65 (C_SymbolType_s65 x) = x
sem_SymbolType_SymbolType  :: ([TypeVar]) ([AType]) (StrictnessList) (Int) (AType) ([TypeContext]) ([AttributeVar]) ([AttrInequality]) -> T_SymbolType 
sem_SymbolType_SymbolType arg_st_vars_ arg_st_args_ arg_st_args_strictness_ arg_st_arity_ arg_st_result_ arg_st_context_ arg_st_attr_vars_ arg_st_attr_env_ = T_SymbolType (lift st65) where
   st65 =
         let
             v64 (T_SymbolType_vIn64 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
                       let
                           alhsOhasRecs = rule982  Void
                           alhsOmEntryId = rule983  Void
                           alhsOmExitId = rule984  Void
                           alhsOppAg = rule985  Void
                           alhsOppAgs = rule986  Void
                           alhsOppDebug = rule987  Void
                           alhsOppDebugs = rule988  Void
                           alhsOrecNode = rule989  Void
                           lcopy = rule990 arg_st_args_ arg_st_args_strictness_ arg_st_arity_ arg_st_attr_env_ arg_st_attr_vars_ arg_st_context_ arg_st_result_ arg_st_vars_
                           alhsOcopy = rule991 lcopy
                           alhsOgraph = rule992 alhsIgraph
                           ag__result_ = T_SymbolType_vOut64 alhsOcopy alhsOgraph alhsOhasRecs alhsOmEntryId alhsOmExitId alhsOppAg alhsOppAgs alhsOppDebug alhsOppDebugs alhsOrecNode
                       in ag__result_
         in C_SymbolType_s65 v64
   rule982  (_) =
     False
   rule983  (_) =
     Nothing
   rule984  (_) =
     Nothing
   rule985  (_) =
     empty
   rule986  (_) =
     []
   rule987  (_) =
     empty
   rule988  (_) =
     []
   rule989  (_) =
     False
   rule990 st_args_ st_args_strictness_ st_arity_ st_attr_env_ st_attr_vars_ st_context_ st_result_ st_vars_ =
     {SymbolType|st_vars = st_vars_ , st_args = st_args_ , st_args_strictness = st_args_strictness_ , st_arity = st_arity_ , st_result = st_result_ , st_context = st_context_ , st_attr_vars = st_attr_vars_ , st_attr_env = st_attr_env_}
   rule991 lcopy =
     lcopy
   rule992 ((alhsIgraph)) =
     alhsIgraph
