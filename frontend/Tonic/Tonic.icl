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
from syntax import :: Optional (..)
// 25 "frontend/Tonic/Tonic.icl"

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
// 46 "frontend/Tonic/Tonic.icl"

// 2 "./frontend/Tonic/ExprSyn.ag"

from syntax import
  :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let {..}, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..},
  :: SymbIdent {..}, :: SymbKind, :: Priority, :: VarInfoPtr, :: DynamicExpr,
  :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index, :: Bind,
  :: Position, :: AType, :: Env, :: Ident {..}, :: SymbolPtr,
  :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..),
  :: FieldSymbol, :: IclModule, :: DclModule, :: FunDef, :: Optional,
  :: SymbolType, :: LetBind

import Tonic.AbsSyn
// 62 "frontend/Tonic/Tonic.icl"
from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// 125 "./frontend/Tonic/MkGraph.ag"


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
nodeErr menv mn expr = mkPretty menv expr +++ "\n" +++
  maybe "for which its ID is unknown" (\n -> "with node ID " +++ toString n) mn

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
/*funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph*/
/*funToGraph {fun_ident=fun_ident, fun_body = TransformedBody tb} fun_defs icl_module dcl_modules*/
  /*= Yes $ GGraph mkBody*/
  /*where*/
  /*mkBody*/
    /*# (mergeId, g)  = addNode GMerge emptyGraph*/
    /*# inh           = mkInhExpr (mkModuleEnv fun_defs icl_module dcl_modules) g mergeId fun_ident.id_name Nothing*/
    /*# syn           = exprCata (mkGraphAlg inh) tb.tb_rhs*/
    /*# g             = syn.syn_graph*/
    /*# (initId, g)   = addNode GInit g*/
    /*# g             = if syn.syn_has_recs*/
                        /*(mkRec syn.syn_nid initId mergeId g)*/
                        /*(mkNonrec syn.syn_nid initId mergeId g)*/
    /*= addStopEdges g*/

  /*addStopEdges g*/
    /*# leafs        = leafNodes g*/
    /*# (stopId, g)  = addNode GStop g*/
    /*= foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs*/

  /*mkRec mfirstId initId mergeId g*/
    /*# g = addEmptyEdge (initId, mergeId) g*/
    /*= maybe g (\firstId -> addEmptyEdge (mergeId, firstId) g) mfirstId*/

  /*mkNonrec mfirstId initId mergeId g*/
    /*# g = removeNode mergeId g*/
    /*= maybe g (\firstId -> addEmptyEdge (initId, firstId) g) mfirstId*/

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
// 164 "frontend/Tonic/Tonic.icl"

// 83 "./frontend/Tonic/Pretty.ag"

mkPretty :: ModuleEnv -> (a -> String) | PPAG a
mkPretty menv = ppCompact o (ppAg menv)

ppCompact :: (Doc -> String)
ppCompact = display o renderCompact

ppExpression :: ModuleEnv Expression -> Doc
ppExpression menv expr = ppAg_Syn_Expression (wrap_Expression (sem_Expression expr) (mkPPInh menv))

ppDebugExpression :: ModuleEnv Expression -> Doc
ppDebugExpression menv expr = ppDebug_Syn_Expression (wrap_Expression (sem_Expression expr) (mkPPInh menv))

mkPPInh :: ModuleEnv -> Inh_Expression
mkPPInh me = Inh_Expression Nothing "" emptyGraph 0 me

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
    (GLet glt)            -> whiteNode [shape "box", label (intercalateString "\n" $ map (mkPretty menv) glt)] // TODO: Rounded corners
    GParallelSplit        -> whiteNode [shape "circle", label "Run in\nparallel"]
    (GParallelJoin jt)    -> whiteNode [shape "circle", label (mkJoinLbl jt)]
    (GTaskApp tid exprs)  -> whiteNode [shape "box", label tid] // TODO: complex contents with extra bar
    (GReturn expr)        -> whiteNode [shape "oval", label (mkPretty menv expr)]
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

class PPAG a where
  ppAg :: ModuleEnv a -> Doc

instance PPAG Expression where
  ppAg menv expr = ppExpression menv expr
  /*ppAg menv expr = ppDebugExpression menv expr*/

instance PPAG Ident where
  ppAg _ i = text i.id_name

instance PPAG BoundVar where
  ppAg menv bv = ppAg menv bv.var_ident

instance PPAG FreeVar where
  ppAg menv fv = ppAg menv fv.fv_ident

instance PPAG SymbIdent where
  ppAg menv si = ppAg menv si.symb_ident

instance PPAG BasicValue where
  ppAg _ (BVI str)  = text str
  ppAg _ (BVInt i)  = int i
  ppAg _ (BVC str)  = text str
  ppAg _ (BVB b)    = bool b
  ppAg _ (BVR str)  = text str
  ppAg _ (BVS str)  = text str

instance PPAG DefinedSymbol where
  ppAg menv ds = ppAg menv ds.ds_ident

instance PPAG Selection where
  ppAg menv (RecordSelection gds _)     = ppAg menv gds.glob_object
  ppAg _ (ArraySelection _ _ _)         = text "TODO: ArraySelection"
  ppAg _ (DictionarySelection _ _ _ _)  = text "TODO: DictionarySelection"

instance PPAG GExpression where
  ppAg _ GUndefinedExpression      = text "undef"
  ppAg _ (GGraphExpression graph)  = text "TODO: render a subgraph (and don't PP one)"
  ppAg _ (GListExpression ges)     = text "TODO: render a list expression (and don't PP one)"
  //ppAg _ (GListComprehensionExpression glc)  = text "TODO: render a list comprehension expression (and don't PP one)"
  ppAg _ (GCleanExpression ce)     = text ce

instance PPAG GLet where
  ppAg menv gl = vcat (map (ppAg menv) gl.glet_binds)

instance PPAG GLetBind where
  ppAg menv lb = text lb.glb_dst <+> equals <+> ppAg menv lb.glb_src

// 295 "frontend/Tonic/Tonic.icl"
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
recNode_Syn_Expression (Syn_Expression _ _ _ _ _ x) = x
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppDebug_Syn_Expression (Syn_Expression _ _ _ _ x _) = x
ppAg_Syn_Expression :: Syn_Expression -> (Doc)
ppAg_Syn_Expression (Syn_Expression _ _ _ x _ _) = x
mNodeId_Syn_Expression :: Syn_Expression -> (Maybe Int)
mNodeId_Syn_Expression (Syn_Expression _ _ x _ _ _) = x
hasRecs_Syn_Expression :: Syn_Expression -> (Bool)
hasRecs_Syn_Expression (Syn_Expression _ x _ _ _ _) = x
graph_Syn_Expression :: Syn_Expression -> (GinGraph)
graph_Syn_Expression (Syn_Expression x _ _ _ _ _) = x
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expression_s2 sem arg) >>= \ (T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode) ->
     lift (Syn_Expression alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode)
   )

// cata
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Var bv_ ) = sem_Expression_Var bv_
sem_Expression ( App app_ ) = sem_Expression_App app_
sem_Expression ( At expr_ exprs_ ) = sem_Expression_At ( sem_Expression expr_ ) ( sem_Expressions exprs_ )
sem_Expression ( Let let__  ) = sem_Expression_Let let__ 
sem_Expression ( Case case__ ) = sem_Expression_Case case__
sem_Expression ( Selection skind_ expr_ sels_ ) = sem_Expression_Selection skind_ ( sem_Expression expr_ ) sels_
sem_Expression ( Update exprl_ sels_ exprr_ ) = sem_Expression_Update ( sem_Expression exprl_ ) sels_ ( sem_Expression exprr_ )
sem_Expression ( RecordUpdate gdsym_ expr_ binds_ ) = sem_Expression_RecordUpdate gdsym_ ( sem_Expression expr_ ) binds_
sem_Expression ( TupleSelect dsym_ n_ expr_ ) = sem_Expression_TupleSelect dsym_ n_ ( sem_Expression expr_ )
sem_Expression ( BasicExpr bv_ ) = sem_Expression_BasicExpr bv_
sem_Expression ( Conditional cond_ ) = sem_Expression_Conditional cond_
sem_Expression ( AnyCodeExpr cbbv_ cbfv_ ss_ ) = sem_Expression_AnyCodeExpr cbbv_ cbfv_ ss_
sem_Expression ( ABCCodeExpr ss_ bl_ ) = sem_Expression_ABCCodeExpr ss_ bl_
sem_Expression ( MatchExpr gdfs_ expr_ ) = sem_Expression_MatchExpr gdfs_ ( sem_Expression expr_ )
sem_Expression ( IsConstructor expr_ gdfs_ arity_ gidx_ ident_ pos_ ) = sem_Expression_IsConstructor ( sem_Expression expr_ ) gdfs_ arity_ gidx_ ident_ pos_
sem_Expression ( FreeVar fv_ ) = sem_Expression_FreeVar fv_
sem_Expression ( DictionariesFunction fvat_ expr_ aty_ ) = sem_Expression_DictionariesFunction fvat_ ( sem_Expression expr_ ) aty_
sem_Expression ( Constant symid_ n_ prio_ ) = sem_Expression_Constant symid_ n_ prio_
sem_Expression ( ClassVariable varinfptr_ ) = sem_Expression_ClassVariable varinfptr_
sem_Expression ( DynamicExpr dynexpr_ ) = sem_Expression_DynamicExpr dynexpr_
sem_Expression ( TypeCodeExpression tycodeexpr_ ) = sem_Expression_TypeCodeExpression tycodeexpr_
sem_Expression ( TypeSignature sigfun_ expr_ ) = sem_Expression_TypeSignature sigfun_ ( sem_Expression expr_ )
sem_Expression ( EE  ) = sem_Expression_EE 
sem_Expression ( NoBind exprinfoptr_ ) = sem_Expression_NoBind exprinfoptr_
sem_Expression ( FailExpr ident_ ) = sem_Expression_FailExpr ident_

// semantic domain
attach_T_Expression (T_Expression t_Expression) = t_Expression
inv_Expression_s2 (C_Expression_s2 x) = x
sem_Expression_Var  :: (BoundVar) -> T_Expression 
sem_Expression_Var arg_bv_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule0 alhsImoduleEnv arg_bv_
                          alhsOppAg :: Doc
                          alhsOppAg = rule1 alhsImoduleEnv arg_bv_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule2  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule3  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule4  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule5 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 44 "./frontend/Tonic/Pretty.ag" #*/
   rule0 = \ ((alhsImoduleEnv)) bv_ ->
                      /*# LINE 44 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Var>" <+> ppAg alhsImoduleEnv bv_
                      /*# LINE 386 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 45 "./frontend/Tonic/Pretty.ag" #*/
   rule1 = \ ((alhsImoduleEnv)) bv_ ->
                      /*# LINE 45 "./frontend/Tonic/Pretty.ag" #*/
                      ppAg alhsImoduleEnv bv_
                      /*# LINE 391 "frontend/Tonic/Tonic.icl"#*/
   rule2 = \  (_) ->
     False
   rule3 = \  (_) ->
     Nothing
   rule4 = \  (_) ->
     False
   rule5 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_App  :: (App) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule6 alhsIgraph alhsImoduleEnv arg_app_ ltaskGraph
                          ltaskGraph = rule7 arg_app_ lassignGraph lbinAppGraph lbindGraph lparBinAppGraph lparListAppGraph lreturnGraph lstepGraph ltaskAppGraph
                          lnodictargs = rule8 alhsImoduleEnv arg_app_
                          (lbindLhsExpr,lbindRhsApp) = rule9 alhsImoduleEnv lnodictargs
                          lbindGraph = rule10  Void
                          lreturnGraph = rule11  Void
                          lbinAppGraph = rule12  Void
                          lassignGraph = rule13  Void
                          lstepGraph = rule14  Void
                          lparBinAppGraph = rule15  Void
                          lparListAppGraph = rule16  Void
                          ltaskAppGraph = rule17 alhsIgraph alhsImoduleEnv arg_app_ lisCurrTask
                          lisCurrTask = rule18 alhsIcurrTaskName arg_app_
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule19 alhsImoduleEnv arg_app_
                          alhsOppAg :: Doc
                          alhsOppAg = rule20 alhsImoduleEnv arg_app_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule21  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule22  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule23  Void
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 35 "./frontend/Tonic/MkGraph.ag" #*/
   rule6 = \ ((alhsIgraph)) ((alhsImoduleEnv)) app_ ltaskGraph ->
                    /*# LINE 35 "./frontend/Tonic/MkGraph.ag" #*/
                    if (identIsTask alhsImoduleEnv app_.app_symb.symb_ident)
                      ltaskGraph
                      alhsIgraph
                    /*# LINE 440 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 39 "./frontend/Tonic/MkGraph.ag" #*/
   rule7 = \ app_ lassignGraph lbinAppGraph lbindGraph lparBinAppGraph lparListAppGraph lreturnGraph lstepGraph ltaskAppGraph ->
                        /*# LINE 39 "./frontend/Tonic/MkGraph.ag" #*/
                        case appFunName app_ of
                          ">>="       -> lbindGraph
                          "return"    -> lreturnGraph
                          ">>|"       -> lbinAppGraph     Nothing
                          "@:"        -> lassignGraph
                          ">>*"       -> lstepGraph
                          "-||-"      -> lparBinAppGraph     DisFirstBin
                          "||-"       -> lparBinAppGraph     DisRight
                          "-||"       -> lparBinAppGraph     DisLeft
                          "-&&-"      -> lparBinAppGraph     ConPair
                          "anyTask"   -> lparListAppGraph     DisFirstList
                          "allTasks"  -> lparListAppGraph     ConAll
                          _           -> ltaskAppGraph
                        /*# LINE 457 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 53 "./frontend/Tonic/MkGraph.ag" #*/
   rule8 = \ ((alhsImoduleEnv)) app_ ->
                         /*# LINE 53 "./frontend/Tonic/MkGraph.ag" #*/
                         dropAppContexts app_ alhsImoduleEnv
                         /*# LINE 462 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 56 "./frontend/Tonic/MkGraph.ag" #*/
   rule9 = \ ((alhsImoduleEnv)) lnodictargs ->
                              /*# LINE 56 "./frontend/Tonic/MkGraph.ag" #*/
                              case lnodictargs     of
                                [e:App rhsApp:_]  -> (e, rhsApp)
                                _                 -> abort ("Invalid bind: " +++ (intercalateString " " $ map (\x -> "'" +++ mkPretty alhsImoduleEnv x +++ "'") lnodictargs    ))
                              /*# LINE 469 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 61 "./frontend/Tonic/MkGraph.ag" #*/
   rule10 = \  (_) ->
                        /*# LINE 61 "./frontend/Tonic/MkGraph.ag" #*/
                        undef
                        /*# LINE 474 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
   rule11 = \  (_) ->
                          /*# LINE 81 "./frontend/Tonic/MkGraph.ag" #*/
                          undef
                          /*# LINE 479 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
   rule12 = \  (_) ->
                          /*# LINE 83 "./frontend/Tonic/MkGraph.ag" #*/
                          \mPat -> undef
                          /*# LINE 484 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 85 "./frontend/Tonic/MkGraph.ag" #*/
   rule13 = \  (_) ->
                          /*# LINE 85 "./frontend/Tonic/MkGraph.ag" #*/
                          undef
                          /*# LINE 489 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 87 "./frontend/Tonic/MkGraph.ag" #*/
   rule14 = \  (_) ->
                        /*# LINE 87 "./frontend/Tonic/MkGraph.ag" #*/
                        abort "Step not implemented yet"
                        /*# LINE 494 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 89 "./frontend/Tonic/MkGraph.ag" #*/
   rule15 = \  (_) ->
                             /*# LINE 89 "./frontend/Tonic/MkGraph.ag" #*/
                             \join -> undef
                             /*# LINE 499 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 91 "./frontend/Tonic/MkGraph.ag" #*/
   rule16 = \  (_) ->
                              /*# LINE 91 "./frontend/Tonic/MkGraph.ag" #*/
                              \join -> undef
                              /*# LINE 504 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 93 "./frontend/Tonic/MkGraph.ag" #*/
   rule17 = \ ((alhsIgraph)) ((alhsImoduleEnv)) app_ lisCurrTask ->
                           /*# LINE 93 "./frontend/Tonic/MkGraph.ag" #*/
                           if lisCurrTask
                             alhsIgraph
                             (let appArgs  = map (GCleanExpression o (mkPretty alhsImoduleEnv)) app_.app_args
                                  (an, g)  = addNode (GTaskApp (appFunName app_) appArgs) g
                              in  g)
                           /*# LINE 513 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 99 "./frontend/Tonic/MkGraph.ag" #*/
   rule18 = \ ((alhsIcurrTaskName)) app_ ->
                         /*# LINE 99 "./frontend/Tonic/MkGraph.ag" #*/
                         appFunName app_ == alhsIcurrTaskName
                         /*# LINE 518 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 48 "./frontend/Tonic/Pretty.ag" #*/
   rule19 = \ ((alhsImoduleEnv)) app_ ->
                      /*# LINE 48 "./frontend/Tonic/Pretty.ag" #*/
                      let args    = app_.app_args
                          argsPP  = hcat $ intersperse (text ", ") $ map (ppDebugExpression alhsImoduleEnv) args
                      in  text "<App>" <+> ppAg alhsImoduleEnv app_.app_symb <+> brackets argsPP
                      /*# LINE 525 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 52 "./frontend/Tonic/Pretty.ag" #*/
   rule20 = \ ((alhsImoduleEnv)) app_ ->
                      /*# LINE 52 "./frontend/Tonic/Pretty.ag" #*/
                      let args       = app_.app_args
                          ppargs xs  = hcat $ intersperse (text " ") $ map (ppAg alhsImoduleEnv) xs
                      in  case args of
                            []     -> ppAg alhsImoduleEnv app_.app_symb
                            [x:xs] -> if (isInfix alhsImoduleEnv app_.app_symb)
                                        (ppAg alhsImoduleEnv x <+> ppAg alhsImoduleEnv app_.app_symb <+> ppargs xs)
                                        (ppAg alhsImoduleEnv app_.app_symb <+> ppargs args)
                      /*# LINE 536 "frontend/Tonic/Tonic.icl"#*/
   rule21 = \  (_) ->
     False
   rule22 = \  (_) ->
     Nothing
   rule23 = \  (_) ->
     False
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_At arg_expr_ arg_exprs_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          st_exprsX5 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_exprs_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          (T_Expressions_vOut4 aexprsIgraph aexprsIhasRecs aexprsImNodeId aexprsIppAg aexprsIppDebug aexprsIrecNode) = inv_Expressions_s5 st_exprsX5 (T_Expressions_vIn4 aexprsOcaseExpr aexprsOcurrTaskName aexprsOgraph aexprsOmergeId aexprsOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule24 aexprIhasRecs aexprsIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule25 aexprImNodeId aexprsImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule26 aexprIppAg aexprsIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule27 aexprIppDebug aexprsIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule28 aexprIrecNode aexprsIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule29 aexprsIgraph
                          aexprOcaseExpr = rule30 alhsIcaseExpr
                          aexprOcurrTaskName = rule31 alhsIcurrTaskName
                          aexprOgraph = rule32 alhsIgraph
                          aexprOmergeId = rule33 alhsImergeId
                          aexprOmoduleEnv = rule34 alhsImoduleEnv
                          aexprsOcaseExpr = rule35 alhsIcaseExpr
                          aexprsOcurrTaskName = rule36 alhsIcurrTaskName
                          aexprsOgraph = rule37 aexprIgraph
                          aexprsOmergeId = rule38 alhsImergeId
                          aexprsOmoduleEnv = rule39 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule24 = \ ((aexprIhasRecs)) ((aexprsIhasRecs)) ->
     aexprIhasRecs || aexprsIhasRecs
   rule25 = \ ((aexprImNodeId)) ((aexprsImNodeId)) ->
     aexprImNodeId <> aexprsImNodeId
   rule26 = \ ((aexprIppAg)) ((aexprsIppAg)) ->
     aexprIppAg <$$> aexprsIppAg
   rule27 = \ ((aexprIppDebug)) ((aexprsIppDebug)) ->
     aexprIppDebug <$$> aexprsIppDebug
   rule28 = \ ((aexprIrecNode)) ((aexprsIrecNode)) ->
     aexprIrecNode || aexprsIrecNode
   rule29 = \ ((aexprsIgraph)) ->
     aexprsIgraph
   rule30 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule31 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule32 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule33 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule34 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule35 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule36 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule37 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule38 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule39 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Let  :: (Let)  -> T_Expression 
sem_Expression_Let arg_let__  = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_letExprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression ((sem_Expression letExpr_val_)))
                          (T_Expression_vOut1 aletExprIgraph aletExprIhasRecs aletExprImNodeId aletExprIppAg aletExprIppDebug aletExprIrecNode) = inv_Expression_s2 st_letExprX2 (T_Expression_vIn1 aletExprOcaseExpr aletExprOcurrTaskName aletExprOgraph aletExprOmergeId aletExprOmoduleEnv)
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule40 aletExprIgraph lconnId lglet lmexpr
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule41  Void
                          lconnId = rule42 aletExprImNodeId aletExprIrecNode alhsImergeId
                          aletExprOcaseExpr = rule43 lmexpr
                          lmexpr = rule44 lglet
                          lglet = rule45 alhsImoduleEnv arg_let__
                          letExpr_val_ = rule46 arg_let__
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule47 aletExprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule48 aletExprImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule49 aletExprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule50 aletExprIppDebug
                          aletExprOcurrTaskName = rule51 alhsIcurrTaskName
                          aletExprOgraph = rule52 alhsIgraph
                          aletExprOmergeId = rule53 alhsImergeId
                          aletExprOmoduleEnv = rule54 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 102 "./frontend/Tonic/MkGraph.ag" #*/
   rule40 = \ ((aletExprIgraph)) lconnId lglet lmexpr ->
                    /*# LINE 102 "./frontend/Tonic/MkGraph.ag" #*/
                    case lmexpr     of
                      Just e  -> aletExprIgraph
                      _       -> let glet      = lglet
                                     (lid, g)  = addNode (GLet glet.glet_binds) aletExprIgraph
                                     err       = abort "Failed to add let edge; no synthesized ID from let body"
                                 in maybe err (\n -> addEmptyEdge (lid, n) g) lconnId
                    /*# LINE 653 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
   rule41 = \  (_) ->
                      /*# LINE 110 "./frontend/Tonic/MkGraph.ag" #*/
                      False
                      /*# LINE 658 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 112 "./frontend/Tonic/MkGraph.ag" #*/
   rule42 = \ ((aletExprImNodeId)) ((aletExprIrecNode)) ((alhsImergeId)) ->
                     /*# LINE 112 "./frontend/Tonic/MkGraph.ag" #*/
                     if aletExprIrecNode (Just alhsImergeId) aletExprImNodeId
                     /*# LINE 663 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 114 "./frontend/Tonic/MkGraph.ag" #*/
   rule43 = \ lmexpr ->
                            /*# LINE 114 "./frontend/Tonic/MkGraph.ag" #*/
                            lmexpr
                            /*# LINE 668 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 116 "./frontend/Tonic/MkGraph.ag" #*/
   rule44 = \ lglet ->
                    /*# LINE 116 "./frontend/Tonic/MkGraph.ag" #*/
                    let glet = lglet
                    in  listToMaybe  [  bnd.glb_src \\ bnd <- glet.glet_binds
                                     |  bnd.glb_dst == "_case_var"]
                    /*# LINE 675 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
   rule45 = \ ((alhsImoduleEnv)) let__ ->
                   /*# LINE 120 "./frontend/Tonic/MkGraph.ag" #*/
                   mkGLet alhsImoduleEnv let__
                   /*# LINE 680 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 123 "./frontend/Tonic/MkGraph.ag" #*/
   rule46 = \ let__ ->
                       /*# LINE 123 "./frontend/Tonic/MkGraph.ag" #*/
                       let__.let_expr
                       /*# LINE 685 "frontend/Tonic/Tonic.icl"#*/
   rule47 = \ ((aletExprIhasRecs)) ->
     aletExprIhasRecs
   rule48 = \ ((aletExprImNodeId)) ->
     aletExprImNodeId
   rule49 = \ ((aletExprIppAg)) ->
     aletExprIppAg
   rule50 = \ ((aletExprIppDebug)) ->
     aletExprIppDebug
   rule51 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule52 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule53 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule54 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Case _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule55  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule56  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule57  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule58  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule59  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule60 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule55 = \  (_) ->
     False
   rule56 = \  (_) ->
     Nothing
   rule57 = \  (_) ->
     empty
   rule58 = \  (_) ->
     empty
   rule59 = \  (_) ->
     False
   rule60 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) ([Selection]) -> T_Expression 
sem_Expression_Selection _ arg_expr_ arg_sels_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule61 aexprIppDebug alhsImoduleEnv arg_sels_
                          alhsOppAg :: Doc
                          alhsOppAg = rule62 aexprIppAg alhsImoduleEnv arg_sels_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule63 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule64 aexprImNodeId
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule65 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule66 aexprIgraph
                          aexprOcaseExpr = rule67 alhsIcaseExpr
                          aexprOcurrTaskName = rule68 alhsIcurrTaskName
                          aexprOgraph = rule69 alhsIgraph
                          aexprOmergeId = rule70 alhsImergeId
                          aexprOmoduleEnv = rule71 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 61 "./frontend/Tonic/Pretty.ag" #*/
   rule61 = \ ((aexprIppDebug)) ((alhsImoduleEnv)) sels_ ->
                      /*# LINE 61 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Selection>" <+> aexprIppDebug <-> char '.' <->
                      hcat (intersperse (char '.') $ map (ppAg alhsImoduleEnv) sels_)
                      /*# LINE 770 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 64 "./frontend/Tonic/Pretty.ag" #*/
   rule62 = \ ((aexprIppAg)) ((alhsImoduleEnv)) sels_ ->
                      /*# LINE 64 "./frontend/Tonic/Pretty.ag" #*/
                      aexprIppAg <-> char '.' <->
                      hcat (intersperse (char '.') $ map (ppAg alhsImoduleEnv) sels_)
                      /*# LINE 776 "frontend/Tonic/Tonic.icl"#*/
   rule63 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule64 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule65 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule66 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule67 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule68 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule69 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule70 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule71 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Update  :: (T_Expression ) ([Selection]) (T_Expression ) -> T_Expression 
sem_Expression_Update arg_exprl_ _ arg_exprr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprlX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprl_))
                          st_exprrX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_exprr_))
                          (T_Expression_vOut1 aexprlIgraph aexprlIhasRecs aexprlImNodeId aexprlIppAg aexprlIppDebug aexprlIrecNode) = inv_Expression_s2 st_exprlX2 (T_Expression_vIn1 aexprlOcaseExpr aexprlOcurrTaskName aexprlOgraph aexprlOmergeId aexprlOmoduleEnv)
                          (T_Expression_vOut1 aexprrIgraph aexprrIhasRecs aexprrImNodeId aexprrIppAg aexprrIppDebug aexprrIrecNode) = inv_Expression_s2 st_exprrX2 (T_Expression_vIn1 aexprrOcaseExpr aexprrOcurrTaskName aexprrOgraph aexprrOmergeId aexprrOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule72  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule73  Void
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule74 aexprlIhasRecs aexprrIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule75 aexprlImNodeId aexprrImNodeId
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule76 aexprlIrecNode aexprrIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule77 aexprrIgraph
                          aexprlOcaseExpr = rule78 alhsIcaseExpr
                          aexprlOcurrTaskName = rule79 alhsIcurrTaskName
                          aexprlOgraph = rule80 alhsIgraph
                          aexprlOmergeId = rule81 alhsImergeId
                          aexprlOmoduleEnv = rule82 alhsImoduleEnv
                          aexprrOcaseExpr = rule83 alhsIcaseExpr
                          aexprrOcurrTaskName = rule84 alhsIcurrTaskName
                          aexprrOgraph = rule85 aexprlIgraph
                          aexprrOmergeId = rule86 alhsImergeId
                          aexprrOmoduleEnv = rule87 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 68 "./frontend/Tonic/Pretty.ag" #*/
   rule72 = \  (_) ->
                      /*# LINE 68 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 835 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 69 "./frontend/Tonic/Pretty.ag" #*/
   rule73 = \  (_) ->
                      /*# LINE 69 "./frontend/Tonic/Pretty.ag" #*/
                      text "<Update>"
                      /*# LINE 840 "frontend/Tonic/Tonic.icl"#*/
   rule74 = \ ((aexprlIhasRecs)) ((aexprrIhasRecs)) ->
     aexprlIhasRecs || aexprrIhasRecs
   rule75 = \ ((aexprlImNodeId)) ((aexprrImNodeId)) ->
     aexprlImNodeId <> aexprrImNodeId
   rule76 = \ ((aexprlIrecNode)) ((aexprrIrecNode)) ->
     aexprlIrecNode || aexprrIrecNode
   rule77 = \ ((aexprrIgraph)) ->
     aexprrIgraph
   rule78 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule79 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule80 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule81 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule82 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule83 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule84 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule85 = \ ((aexprlIgraph)) ->
     aexprlIgraph
   rule86 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule87 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_RecordUpdate  :: (Global DefinedSymbol) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule88  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule89  Void
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule90 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule91 aexprImNodeId
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule92 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule93 aexprIgraph
                          aexprOcaseExpr = rule94 alhsIcaseExpr
                          aexprOcurrTaskName = rule95 alhsIcurrTaskName
                          aexprOgraph = rule96 alhsIgraph
                          aexprOmergeId = rule97 alhsImergeId
                          aexprOmoduleEnv = rule98 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 72 "./frontend/Tonic/Pretty.ag" #*/
   rule88 = \  (_) ->
                      /*# LINE 72 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 902 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 73 "./frontend/Tonic/Pretty.ag" #*/
   rule89 = \  (_) ->
                      /*# LINE 73 "./frontend/Tonic/Pretty.ag" #*/
                      text "<RecordUpdate>"
                      /*# LINE 907 "frontend/Tonic/Tonic.icl"#*/
   rule90 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule91 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule92 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule93 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule94 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule95 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule96 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule97 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule98 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_TupleSelect  :: (DefinedSymbol) (Int) (T_Expression ) -> T_Expression 
sem_Expression_TupleSelect _ _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule99  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule100  Void
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule101 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule102 aexprImNodeId
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule103 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule104 aexprIgraph
                          aexprOcaseExpr = rule105 alhsIcaseExpr
                          aexprOcurrTaskName = rule106 alhsIcurrTaskName
                          aexprOgraph = rule107 alhsIgraph
                          aexprOmergeId = rule108 alhsImergeId
                          aexprOmoduleEnv = rule109 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 76 "./frontend/Tonic/Pretty.ag" #*/
   rule99 = \  (_) ->
                      /*# LINE 76 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 959 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 77 "./frontend/Tonic/Pretty.ag" #*/
   rule100 = \  (_) ->
                      /*# LINE 77 "./frontend/Tonic/Pretty.ag" #*/
                      text "<TupleSelect>"
                      /*# LINE 964 "frontend/Tonic/Tonic.icl"#*/
   rule101 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule102 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule103 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule104 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule105 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule106 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule107 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule108 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule109 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_BasicExpr  :: (BasicValue) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule110 alhsImoduleEnv arg_bv_
                          alhsOppAg :: Doc
                          alhsOppAg = rule111 alhsImoduleEnv arg_bv_
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule112  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule113  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule114  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule115 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 80 "./frontend/Tonic/Pretty.ag" #*/
   rule110 = \ ((alhsImoduleEnv)) bv_ ->
                      /*# LINE 80 "./frontend/Tonic/Pretty.ag" #*/
                      text "<BasicValue>" <+> ppAg alhsImoduleEnv bv_
                      /*# LINE 1009 "frontend/Tonic/Tonic.icl"#*/
   /*# LINE 81 "./frontend/Tonic/Pretty.ag" #*/
   rule111 = \ ((alhsImoduleEnv)) bv_ ->
                      /*# LINE 81 "./frontend/Tonic/Pretty.ag" #*/
                      ppAg alhsImoduleEnv bv_
                      /*# LINE 1014 "frontend/Tonic/Tonic.icl"#*/
   rule112 = \  (_) ->
     False
   rule113 = \  (_) ->
     Nothing
   rule114 = \  (_) ->
     False
   rule115 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_Conditional _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule116  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule117  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule118  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule119  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule120  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule121 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule116 = \  (_) ->
     False
   rule117 = \  (_) ->
     Nothing
   rule118 = \  (_) ->
     empty
   rule119 = \  (_) ->
     empty
   rule120 = \  (_) ->
     False
   rule121 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule122  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule123  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule124  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule125  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule126  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule127 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule122 = \  (_) ->
     False
   rule123 = \  (_) ->
     Nothing
   rule124 = \  (_) ->
     empty
   rule125 = \  (_) ->
     empty
   rule126 = \  (_) ->
     False
   rule127 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule128  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule129  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule130  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule131  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule132  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule133 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule128 = \  (_) ->
     False
   rule129 = \  (_) ->
     Nothing
   rule130 = \  (_) ->
     empty
   rule131 = \  (_) ->
     empty
   rule132 = \  (_) ->
     False
   rule133 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule134 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule135 aexprImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule136 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule137 aexprIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule138 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule139 aexprIgraph
                          aexprOcaseExpr = rule140 alhsIcaseExpr
                          aexprOcurrTaskName = rule141 alhsIcurrTaskName
                          aexprOgraph = rule142 alhsIgraph
                          aexprOmergeId = rule143 alhsImergeId
                          aexprOmoduleEnv = rule144 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule134 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule135 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule136 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule137 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule138 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule139 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule140 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule141 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule142 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule143 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule144 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_IsConstructor  :: (T_Expression ) (Global DefinedSymbol) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ _ _ _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule145 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule146 aexprImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule147 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule148 aexprIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule149 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule150 aexprIgraph
                          aexprOcaseExpr = rule151 alhsIcaseExpr
                          aexprOcurrTaskName = rule152 alhsIcurrTaskName
                          aexprOgraph = rule153 alhsIgraph
                          aexprOmergeId = rule154 alhsImergeId
                          aexprOmoduleEnv = rule155 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule145 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule146 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule147 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule148 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule149 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule150 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule151 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule152 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule153 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule154 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule155 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_FreeVar  :: (FreeVar) -> T_Expression 
sem_Expression_FreeVar _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule156  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule157  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule158  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule159  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule160  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule161 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule156 = \  (_) ->
     False
   rule157 = \  (_) ->
     Nothing
   rule158 = \  (_) ->
     empty
   rule159 = \  (_) ->
     empty
   rule160 = \  (_) ->
     False
   rule161 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule162 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule163 aexprImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule164 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule165 aexprIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule166 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule167 aexprIgraph
                          aexprOcaseExpr = rule168 alhsIcaseExpr
                          aexprOcurrTaskName = rule169 alhsIcurrTaskName
                          aexprOgraph = rule170 alhsIgraph
                          aexprOmergeId = rule171 alhsImergeId
                          aexprOmoduleEnv = rule172 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule162 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule163 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule164 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule165 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule166 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule167 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule168 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule169 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule170 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule171 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule172 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Constant  :: (SymbIdent) (Int) (Priority) -> T_Expression 
sem_Expression_Constant _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule173  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule174  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule175  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule176  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule177  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule178 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule173 = \  (_) ->
     False
   rule174 = \  (_) ->
     Nothing
   rule175 = \  (_) ->
     empty
   rule176 = \  (_) ->
     empty
   rule177 = \  (_) ->
     False
   rule178 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule179  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule180  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule181  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule182  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule183  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule184 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule179 = \  (_) ->
     False
   rule180 = \  (_) ->
     Nothing
   rule181 = \  (_) ->
     empty
   rule182 = \  (_) ->
     empty
   rule183 = \  (_) ->
     False
   rule184 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule185  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule186  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule187  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule188  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule189  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule190 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule185 = \  (_) ->
     False
   rule186 = \  (_) ->
     Nothing
   rule187 = \  (_) ->
     empty
   rule188 = \  (_) ->
     empty
   rule189 = \  (_) ->
     False
   rule190 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule191  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule192  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule193  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule194  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule195  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule196 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule191 = \  (_) ->
     False
   rule192 = \  (_) ->
     Nothing
   rule193 = \  (_) ->
     empty
   rule194 = \  (_) ->
     empty
   rule195 = \  (_) ->
     False
   rule196 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIgraph aexprIhasRecs aexprImNodeId aexprIppAg aexprIppDebug aexprIrecNode) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule197 aexprIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule198 aexprImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule199 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule200 aexprIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule201 aexprIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule202 aexprIgraph
                          aexprOcaseExpr = rule203 alhsIcaseExpr
                          aexprOcurrTaskName = rule204 alhsIcurrTaskName
                          aexprOgraph = rule205 alhsIgraph
                          aexprOmergeId = rule206 alhsImergeId
                          aexprOmoduleEnv = rule207 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule197 = \ ((aexprIhasRecs)) ->
     aexprIhasRecs
   rule198 = \ ((aexprImNodeId)) ->
     aexprImNodeId
   rule199 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule200 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule201 = \ ((aexprIrecNode)) ->
     aexprIrecNode
   rule202 = \ ((aexprIgraph)) ->
     aexprIgraph
   rule203 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule204 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule205 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule206 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule207 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_EE  ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule208  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule209  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule210  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule211  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule212  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule213 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule208 = \  (_) ->
     False
   rule209 = \  (_) ->
     Nothing
   rule210 = \  (_) ->
     empty
   rule211 = \  (_) ->
     empty
   rule212 = \  (_) ->
     False
   rule213 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule214  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule215  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule216  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule217  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule218  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule219 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule214 = \  (_) ->
     False
   rule215 = \  (_) ->
     Nothing
   rule216 = \  (_) ->
     empty
   rule217 = \  (_) ->
     empty
   rule218 = \  (_) ->
     False
   rule219 = \ ((alhsIgraph)) ->
     alhsIgraph
sem_Expression_FailExpr  :: (Ident) -> T_Expression 
sem_Expression_FailExpr _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule220  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule221  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule222  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule223  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule224  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule225 alhsIgraph
                          ag__result_ = T_Expression_vOut1 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expression_s2 v1
   rule220 = \  (_) ->
     False
   rule221 = \  (_) ->
     Nothing
   rule222 = \  (_) ->
     empty
   rule223 = \  (_) ->
     empty
   rule224 = \  (_) ->
     False
   rule225 = \ ((alhsIgraph)) ->
     alhsIgraph

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
recNode_Syn_Expressions (Syn_Expressions _ _ _ _ _ x) = x
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebug_Syn_Expressions (Syn_Expressions _ _ _ _ x _) = x
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAg_Syn_Expressions (Syn_Expressions _ _ _ x _ _) = x
mNodeId_Syn_Expressions :: Syn_Expressions -> (Maybe Int)
mNodeId_Syn_Expressions (Syn_Expressions _ _ x _ _ _) = x
hasRecs_Syn_Expressions :: Syn_Expressions -> (Bool)
hasRecs_Syn_Expressions (Syn_Expressions _ x _ _ _ _) = x
graph_Syn_Expressions :: Syn_Expressions -> (GinGraph)
graph_Syn_Expressions (Syn_Expressions x _ _ _ _ _) = x
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expressions_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expressions_s5 sem arg) >>= \ (T_Expressions_vOut4 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode) ->
     lift (Syn_Expressions alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode)
   )

// cata
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = foldr sem_Expressions_Cons sem_Expressions_Nil (map sem_Expression list)

// semantic domain
attach_T_Expressions (T_Expressions t_Expressions) = t_Expressions
inv_Expressions_s5 (C_Expressions_s5 x) = x
sem_Expressions_Cons  :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (lift st5) where
   st5 =
        let
            v4 :: T_Expressions_v4 
            v4 = \ (T_Expressions_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_hdX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_hd_))
                          st_tlX5 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_tl_))
                          (T_Expression_vOut1 ahdIgraph ahdIhasRecs ahdImNodeId ahdIppAg ahdIppDebug ahdIrecNode) = inv_Expression_s2 st_hdX2 (T_Expression_vIn1 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                          (T_Expressions_vOut4 atlIgraph atlIhasRecs atlImNodeId atlIppAg atlIppDebug atlIrecNode) = inv_Expressions_s5 st_tlX5 (T_Expressions_vIn4 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule226 ahdIhasRecs atlIhasRecs
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule227 ahdImNodeId atlImNodeId
                          alhsOppAg :: Doc
                          alhsOppAg = rule228 ahdIppAg atlIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule229 ahdIppDebug atlIppDebug
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule230 ahdIrecNode atlIrecNode
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule231 atlIgraph
                          ahdOcaseExpr = rule232 alhsIcaseExpr
                          ahdOcurrTaskName = rule233 alhsIcurrTaskName
                          ahdOgraph = rule234 alhsIgraph
                          ahdOmergeId = rule235 alhsImergeId
                          ahdOmoduleEnv = rule236 alhsImoduleEnv
                          atlOcaseExpr = rule237 alhsIcaseExpr
                          atlOcurrTaskName = rule238 alhsIcurrTaskName
                          atlOgraph = rule239 ahdIgraph
                          atlOmergeId = rule240 alhsImergeId
                          atlOmoduleEnv = rule241 alhsImoduleEnv
                          ag__result_ = T_Expressions_vOut4 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expressions_s5 v4
   rule226 = \ ((ahdIhasRecs)) ((atlIhasRecs)) ->
     ahdIhasRecs || atlIhasRecs
   rule227 = \ ((ahdImNodeId)) ((atlImNodeId)) ->
     ahdImNodeId <> atlImNodeId
   rule228 = \ ((ahdIppAg)) ((atlIppAg)) ->
     ahdIppAg <$$> atlIppAg
   rule229 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug <$$> atlIppDebug
   rule230 = \ ((ahdIrecNode)) ((atlIrecNode)) ->
     ahdIrecNode || atlIrecNode
   rule231 = \ ((atlIgraph)) ->
     atlIgraph
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
   rule237 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule238 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule239 = \ ((ahdIgraph)) ->
     ahdIgraph
   rule240 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule241 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expressions_Nil  ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st5) where
   st5 =
        let
            v4 :: T_Expressions_v4 
            v4 = \ (T_Expressions_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOhasRecs :: Bool
                          alhsOhasRecs = rule242  Void
                          alhsOmNodeId :: Maybe Int
                          alhsOmNodeId = rule243  Void
                          alhsOppAg :: Doc
                          alhsOppAg = rule244  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule245  Void
                          alhsOrecNode :: Bool
                          alhsOrecNode = rule246  Void
                          alhsOgraph :: GinGraph
                          alhsOgraph = rule247 alhsIgraph
                          ag__result_ = T_Expressions_vOut4 alhsOgraph alhsOhasRecs alhsOmNodeId alhsOppAg alhsOppDebug alhsOrecNode
                      in ag__result_ )
        in C_Expressions_s5 v4
   rule242 = \  (_) ->
     False
   rule243 = \  (_) ->
     Nothing
   rule244 = \  (_) ->
     empty
   rule245 = \  (_) ->
     empty
   rule246 = \  (_) ->
     False
   rule247 = \ ((alhsIgraph)) ->
     alhsIgraph
