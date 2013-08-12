implementation module Tonic.Pretty

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
import Tonic.Pretty

from syntax import :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..}, :: SymbIdent {..}, :: SymbKind, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index,
  :: Bind, :: Position, :: AType, :: Env, :: Ident {..}, :: SymbolPtr, :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..), :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind

:: Expressions :== [Expression]

from Control.Monad.Identity import :: Identity
import qualified Control.Monad.Identity as Control.Monad.Identity
import Control.Monad.Identity
from Control.Applicative import lift
from Control.Monad import class Monad (..)
// 160 "./frontend/Tonic/Pretty.ag"

mkPretty :: ModuleEnv -> (a -> String) | PPAG a
mkPretty menv = ppCompact o (ppAg menv)

ppCompact :: (Doc -> String)
ppCompact = display o renderCompact

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
  mkJoinLbl DisFirstBin   = "Firstly\nfinished\ntask"
  mkJoinLbl DisFirstList  = "Firstly\nfinished\ntask"
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
  //ppAg menv expr = ppExpression menv expr
  ppAg menv expr = ppDebugExpression menv expr

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
  ppAg menv (RecordSelection gds _)     = text "TODO RecordSelection" // ppAg menv gds
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

// 163 "frontend/Tonic/Pretty.icl"
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
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppDebug_Syn_Expression (Syn_Expression _ x) = x
ppAg_Syn_Expression :: Syn_Expression -> (Doc)
ppAg_Syn_Expression (Syn_Expression x _) = x
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expression_s2 sem arg) >>= \ (T_Expression_vOut1 alhsOppAg alhsOppDebug) ->
     lift (Syn_Expression alhsOppAg alhsOppDebug)
   )

// cata
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Var bv_ ) = sem_Expression_Var bv_
sem_Expression ( App app_ ) = sem_Expression_App app_
sem_Expression ( At expr_ exprs_ ) = sem_Expression_At ( sem_Expression expr_ ) ( sem_Expressions exprs_ )
sem_Expression ( Let let_ ) = sem_Expression_Let let_
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
                          alhsOppAg = rule1  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 152 "./frontend/Tonic/Pretty.ag" #*/
   rule0 = \ ((alhsImoduleEnv)) bv_ ->
                              /*# LINE 152 "./frontend/Tonic/Pretty.ag" #*/
                              text "<Var>" <+> ppAg alhsImoduleEnv bv_
                              /*# LINE 238 "frontend/Tonic/Pretty.icl"#*/
   rule1 = \  (_) ->
     empty
sem_Expression_App  :: (App) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule2 alhsImoduleEnv arg_app_
                          alhsOppAg :: Doc
                          alhsOppAg = rule3  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 153 "./frontend/Tonic/Pretty.ag" #*/
   rule2 = \ ((alhsImoduleEnv)) app_ ->
                              /*# LINE 153 "./frontend/Tonic/Pretty.ag" #*/
                              let args    = dropAppContexts app_ alhsImoduleEnv
                                  argsPP  = hcat $ intersperse (text ", ") $ map (ppDebugExpression alhsImoduleEnv) args
                              in  text "<App>" <+> ppAg alhsImoduleEnv app_.app_symb <+> brackets argsPP
                              /*# LINE 261 "frontend/Tonic/Pretty.icl"#*/
   rule3 = \  (_) ->
     empty
sem_Expression_At  :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_At arg_expr_ arg_exprs_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          st_exprsX5 = 'Control.Monad.Identity'.runIdentity (attach_T_Expressions (arg_exprs_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          (T_Expressions_vOut4 aexprsIppAg aexprsIppDebug) = inv_Expressions_s5 st_exprsX5 (T_Expressions_vIn4 aexprsOcaseExpr aexprsOcurrTaskName aexprsOgraph aexprsOmergeId aexprsOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule4 aexprIppAg aexprsIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule5 aexprIppDebug aexprsIppDebug
                          aexprOcaseExpr = rule6 alhsIcaseExpr
                          aexprOcurrTaskName = rule7 alhsIcurrTaskName
                          aexprOgraph = rule8 alhsIgraph
                          aexprOmergeId = rule9 alhsImergeId
                          aexprOmoduleEnv = rule10 alhsImoduleEnv
                          aexprsOcaseExpr = rule11 alhsIcaseExpr
                          aexprsOcurrTaskName = rule12 alhsIcurrTaskName
                          aexprsOgraph = rule13 alhsIgraph
                          aexprsOmergeId = rule14 alhsImergeId
                          aexprsOmoduleEnv = rule15 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule4 = \ ((aexprIppAg)) ((aexprsIppAg)) ->
     aexprIppAg <$$> aexprsIppAg
   rule5 = \ ((aexprIppDebug)) ((aexprsIppDebug)) ->
     aexprIppDebug <$$> aexprsIppDebug
   rule6 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule7 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule8 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule9 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule10 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule11 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule12 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule13 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule14 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule15 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Let  :: (Let) -> T_Expression 
sem_Expression_Let _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule16  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule17  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule16 = \  (_) ->
     empty
   rule17 = \  (_) ->
     empty
sem_Expression_Case  :: (Case) -> T_Expression 
sem_Expression_Case _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule18  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule19  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule18 = \  (_) ->
     empty
   rule19 = \  (_) ->
     empty
sem_Expression_Selection  :: (SelectorKind) (T_Expression ) ([Selection]) -> T_Expression 
sem_Expression_Selection _ arg_expr_ arg_sels_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule20 aexprIppDebug alhsImoduleEnv arg_sels_
                          alhsOppAg :: Doc
                          alhsOppAg = rule21 aexprIppAg
                          aexprOcaseExpr = rule22 alhsIcaseExpr
                          aexprOcurrTaskName = rule23 alhsIcurrTaskName
                          aexprOgraph = rule24 alhsIgraph
                          aexprOmergeId = rule25 alhsImergeId
                          aexprOmoduleEnv = rule26 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 156 "./frontend/Tonic/Pretty.ag" #*/
   rule20 = \ ((aexprIppDebug)) ((alhsImoduleEnv)) sels_ ->
                              /*# LINE 156 "./frontend/Tonic/Pretty.ag" #*/
                              text "<Selection>" <+> aexprIppDebug <-> char '.' <->
                              hcat (intersperse (char '.') $ map (ppAg alhsImoduleEnv) sels_)
                              /*# LINE 378 "frontend/Tonic/Pretty.icl"#*/
   rule21 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule22 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule23 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule24 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule25 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule26 = \ ((alhsImoduleEnv)) ->
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
                          (T_Expression_vOut1 aexprlIppAg aexprlIppDebug) = inv_Expression_s2 st_exprlX2 (T_Expression_vIn1 aexprlOcaseExpr aexprlOcurrTaskName aexprlOgraph aexprlOmergeId aexprlOmoduleEnv)
                          (T_Expression_vOut1 aexprrIppAg aexprrIppDebug) = inv_Expression_s2 st_exprrX2 (T_Expression_vIn1 aexprrOcaseExpr aexprrOcurrTaskName aexprrOgraph aexprrOmergeId aexprrOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule27 aexprlIppAg aexprrIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule28 aexprlIppDebug aexprrIppDebug
                          aexprlOcaseExpr = rule29 alhsIcaseExpr
                          aexprlOcurrTaskName = rule30 alhsIcurrTaskName
                          aexprlOgraph = rule31 alhsIgraph
                          aexprlOmergeId = rule32 alhsImergeId
                          aexprlOmoduleEnv = rule33 alhsImoduleEnv
                          aexprrOcaseExpr = rule34 alhsIcaseExpr
                          aexprrOcurrTaskName = rule35 alhsIcurrTaskName
                          aexprrOgraph = rule36 alhsIgraph
                          aexprrOmergeId = rule37 alhsImergeId
                          aexprrOmoduleEnv = rule38 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule27 = \ ((aexprlIppAg)) ((aexprrIppAg)) ->
     aexprlIppAg <$$> aexprrIppAg
   rule28 = \ ((aexprlIppDebug)) ((aexprrIppDebug)) ->
     aexprlIppDebug <$$> aexprrIppDebug
   rule29 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule30 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule31 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule32 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule33 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule34 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule35 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule36 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule37 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule38 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_RecordUpdate  :: (Global DefinedSymbol) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule39 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule40 aexprIppDebug
                          aexprOcaseExpr = rule41 alhsIcaseExpr
                          aexprOcurrTaskName = rule42 alhsIcurrTaskName
                          aexprOgraph = rule43 alhsIgraph
                          aexprOmergeId = rule44 alhsImergeId
                          aexprOmoduleEnv = rule45 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule39 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule40 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule41 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule42 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule43 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule44 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule45 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_TupleSelect  :: (DefinedSymbol) (Int) (T_Expression ) -> T_Expression 
sem_Expression_TupleSelect _ _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule46 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule47 aexprIppDebug
                          aexprOcaseExpr = rule48 alhsIcaseExpr
                          aexprOcurrTaskName = rule49 alhsIcurrTaskName
                          aexprOgraph = rule50 alhsIgraph
                          aexprOmergeId = rule51 alhsImergeId
                          aexprOmoduleEnv = rule52 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule46 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule47 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule48 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule49 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule50 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule51 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule52 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_BasicExpr  :: (BasicValue) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule53 alhsImoduleEnv arg_bv_
                          alhsOppAg :: Doc
                          alhsOppAg = rule54  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   /*# LINE 158 "./frontend/Tonic/Pretty.ag" #*/
   rule53 = \ ((alhsImoduleEnv)) bv_ ->
                              /*# LINE 158 "./frontend/Tonic/Pretty.ag" #*/
                              text "<BasicValue>" <+> ppAg alhsImoduleEnv bv_
                              /*# LINE 531 "frontend/Tonic/Pretty.icl"#*/
   rule54 = \  (_) ->
     empty
sem_Expression_Conditional  :: (Conditional) -> T_Expression 
sem_Expression_Conditional _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule55  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule56  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule55 = \  (_) ->
     empty
   rule56 = \  (_) ->
     empty
sem_Expression_AnyCodeExpr  :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule57  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule58  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule57 = \  (_) ->
     empty
   rule58 = \  (_) ->
     empty
sem_Expression_ABCCodeExpr  :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule59  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule60  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule59 = \  (_) ->
     empty
   rule60 = \  (_) ->
     empty
sem_Expression_MatchExpr  :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule61 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule62 aexprIppDebug
                          aexprOcaseExpr = rule63 alhsIcaseExpr
                          aexprOcurrTaskName = rule64 alhsIcurrTaskName
                          aexprOgraph = rule65 alhsIgraph
                          aexprOmergeId = rule66 alhsImergeId
                          aexprOmoduleEnv = rule67 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule61 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule62 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule63 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule64 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule65 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule66 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule67 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_IsConstructor  :: (T_Expression ) (Global DefinedSymbol) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ _ _ _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule68 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule69 aexprIppDebug
                          aexprOcaseExpr = rule70 alhsIcaseExpr
                          aexprOcurrTaskName = rule71 alhsIcurrTaskName
                          aexprOgraph = rule72 alhsIgraph
                          aexprOmergeId = rule73 alhsImergeId
                          aexprOmoduleEnv = rule74 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule68 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule69 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule70 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule71 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule72 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule73 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule74 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_FreeVar  :: (FreeVar) -> T_Expression 
sem_Expression_FreeVar _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule75  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule76  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule75 = \  (_) ->
     empty
   rule76 = \  (_) ->
     empty
sem_Expression_DictionariesFunction  :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule77 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule78 aexprIppDebug
                          aexprOcaseExpr = rule79 alhsIcaseExpr
                          aexprOcurrTaskName = rule80 alhsIcurrTaskName
                          aexprOgraph = rule81 alhsIgraph
                          aexprOmergeId = rule82 alhsImergeId
                          aexprOmoduleEnv = rule83 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule77 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule78 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule79 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule80 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule81 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule82 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule83 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Constant  :: (SymbIdent) (Int) (Priority) -> T_Expression 
sem_Expression_Constant _ _ _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule84  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule85  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule84 = \  (_) ->
     empty
   rule85 = \  (_) ->
     empty
sem_Expression_ClassVariable  :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule86  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule87  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule86 = \  (_) ->
     empty
   rule87 = \  (_) ->
     empty
sem_Expression_DynamicExpr  :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule88  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule89  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule88 = \  (_) ->
     empty
   rule89 = \  (_) ->
     empty
sem_Expression_TypeCodeExpression  :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule90  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule91  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule90 = \  (_) ->
     empty
   rule91 = \  (_) ->
     empty
sem_Expression_TypeSignature  :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          st_exprX2 = 'Control.Monad.Identity'.runIdentity (attach_T_Expression (arg_expr_))
                          (T_Expression_vOut1 aexprIppAg aexprIppDebug) = inv_Expression_s2 st_exprX2 (T_Expression_vIn1 aexprOcaseExpr aexprOcurrTaskName aexprOgraph aexprOmergeId aexprOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule92 aexprIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule93 aexprIppDebug
                          aexprOcaseExpr = rule94 alhsIcaseExpr
                          aexprOcurrTaskName = rule95 alhsIcurrTaskName
                          aexprOgraph = rule96 alhsIgraph
                          aexprOmergeId = rule97 alhsImergeId
                          aexprOmoduleEnv = rule98 alhsImoduleEnv
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule92 = \ ((aexprIppAg)) ->
     aexprIppAg
   rule93 = \ ((aexprIppDebug)) ->
     aexprIppDebug
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
sem_Expression_EE  ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule99  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule100  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule99 = \  (_) ->
     empty
   rule100 = \  (_) ->
     empty
sem_Expression_NoBind  :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule101  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule102  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule101 = \  (_) ->
     empty
   rule102 = \  (_) ->
     empty
sem_Expression_FailExpr  :: (Ident) -> T_Expression 
sem_Expression_FailExpr _ = T_Expression (lift st2) where
   st2 =
        let
            v1 :: T_Expression_v1 
            v1 = \ (T_Expression_vIn1 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule103  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule104  Void
                          ag__result_ = T_Expression_vOut1 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expression_s2 v1
   rule103 = \  (_) ->
     empty
   rule104 = \  (_) ->
     empty

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
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebug_Syn_Expressions (Syn_Expressions _ x) = x
ppAg_Syn_Expressions :: Syn_Expressions -> (Doc)
ppAg_Syn_Expressions (Syn_Expressions x _) = x
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expressions_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expressions_s5 sem arg) >>= \ (T_Expressions_vOut4 alhsOppAg alhsOppDebug) ->
     lift (Syn_Expressions alhsOppAg alhsOppDebug)
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
                          (T_Expression_vOut1 ahdIppAg ahdIppDebug) = inv_Expression_s2 st_hdX2 (T_Expression_vIn1 ahdOcaseExpr ahdOcurrTaskName ahdOgraph ahdOmergeId ahdOmoduleEnv)
                          (T_Expressions_vOut4 atlIppAg atlIppDebug) = inv_Expressions_s5 st_tlX5 (T_Expressions_vIn4 atlOcaseExpr atlOcurrTaskName atlOgraph atlOmergeId atlOmoduleEnv)
                          alhsOppAg :: Doc
                          alhsOppAg = rule105 ahdIppAg atlIppAg
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule106 ahdIppDebug atlIppDebug
                          ahdOcaseExpr = rule107 alhsIcaseExpr
                          ahdOcurrTaskName = rule108 alhsIcurrTaskName
                          ahdOgraph = rule109 alhsIgraph
                          ahdOmergeId = rule110 alhsImergeId
                          ahdOmoduleEnv = rule111 alhsImoduleEnv
                          atlOcaseExpr = rule112 alhsIcaseExpr
                          atlOcurrTaskName = rule113 alhsIcurrTaskName
                          atlOgraph = rule114 alhsIgraph
                          atlOmergeId = rule115 alhsImergeId
                          atlOmoduleEnv = rule116 alhsImoduleEnv
                          ag__result_ = T_Expressions_vOut4 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expressions_s5 v4
   rule105 = \ ((ahdIppAg)) ((atlIppAg)) ->
     ahdIppAg <$$> atlIppAg
   rule106 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug <$$> atlIppDebug
   rule107 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule108 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule109 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule110 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule111 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule112 = \ ((alhsIcaseExpr)) ->
     alhsIcaseExpr
   rule113 = \ ((alhsIcurrTaskName)) ->
     alhsIcurrTaskName
   rule114 = \ ((alhsIgraph)) ->
     alhsIgraph
   rule115 = \ ((alhsImergeId)) ->
     alhsImergeId
   rule116 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expressions_Nil  ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st5) where
   st5 =
        let
            v4 :: T_Expressions_v4 
            v4 = \ (T_Expressions_vIn4 alhsIcaseExpr alhsIcurrTaskName alhsIgraph alhsImergeId alhsImoduleEnv) -> (
                      let
                          alhsOppAg :: Doc
                          alhsOppAg = rule117  Void
                          alhsOppDebug :: Doc
                          alhsOppDebug = rule118  Void
                          ag__result_ = T_Expressions_vOut4 alhsOppAg alhsOppDebug
                      in ag__result_ )
        in C_Expressions_s5 v4
   rule117 = \  (_) ->
     empty
   rule118 = \  (_) ->
     empty
