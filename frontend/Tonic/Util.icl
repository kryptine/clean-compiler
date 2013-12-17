implementation module Tonic.Util

import StdEnv
import Data.Func
import Data.Functor
import Data.List
import Data.Maybe
import Data.Map
import syntax
import Tonic.AbsSyn
import Tonic.Pretty
import Text
import iTasks.Framework.Tonic.AbsSyn

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a
foldrArr f b arr = foldrArr` 0 f b arr
  where
  arrSz = size arr
  foldrArr` n f b arr
    | n < arrSz  = f (select arr n) (foldrArr` (n + 1) f b arr)
    | otherwise  = b

findInArr :: (e -> Bool) (a e) -> Maybe (Int, e) | Array a e
findInArr p arr = findInArr` 0 p arr
  where
  arrSz = size arr
  findInArr` n p arr
    | n < arrSz
      #  elem = select arr n
      =  if (p elem) (Just (n, elem)) (findInArr` (n + 1) p arr)
    | otherwise  = Nothing

concatStrings :: [String] -> .String
concatStrings l = updateS 0 l (createArray (sum [size s \\ s <- l]) ' ')
  where
    updateS :: !Int [{#Char}] *{#Char} -> *{#Char}
    updateS i [] s
      =  s
    updateS i [h : t] s
      =  updateS (i + size h) t {s & [pos] = c \\ c <-: h & pos <- [i..]}

intercalateString :: String [String] -> String
intercalateString xs xss = concatStrings (intersperse xs xss)

//import StdDebug

dropAppContexts :: App *ModuleEnv -> *(([Expression], [Expression]), *ModuleEnv)
dropAppContexts app menv
  # (mcd, menv) = reifyConsDef ident menv
  = case mcd of
      Just cd = (dropContexts cd.cons_type app.app_args, menv)
      Nothing
        # (mst, menv) = reifySymbolType ident menv
        # funTy       = fromMaybe (abort err) mst
        =
          //trace_n (ident +++ " has arity " +++ toString funTy.st_arity) $
           (dropContexts funTy app.app_args, menv)
  where
  ident  = app.app_symb.symb_ident.id_name
  err    = "dropAppContexts : failed to find symbol type for " +++ ident

extractFunDefs :: !*{#FunDef} -> *(!{#FunDef}, !*{#FunDef})
extractFunDefs fun_defs
  # defs = {d \\ d <-: fun_defs}
  = (defs, {d \\ d <-: defs})

reifyConsDef :: String *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)
reifyConsDef ident menv
  # (common, iclmod) = (menv.me_icl_module)!icl_common
  # dcls             = menv.me_dcl_modules
  # menv             = {menv & me_icl_module=iclmod}
  = case searchConsDefs ident common.com_cons_defs of
      Just cd = (Just cd, menv)
      _
        # cds = [cd \\ Just cd <- [searchConsDefs ident common.com_cons_defs \\ common <- [dclmod.dcl_common \\ dclmod <-: dcls]]]
        = (listToMaybe cds, menv)

  where
    searchConsDefs :: String .{# ConsDef} -> Maybe ConsDef
    searchConsDefs ident defs = listToMaybe [cd \\ cd <-: defs | cd.cons_ident.id_name == ident]

reifyFunType :: String *ModuleEnv -> *(Maybe FunType, *ModuleEnv)
reifyFunType ident menv=:{me_dcl_modules}
  = (safeHead  [  ft \\ dcl <-: me_dcl_modules, ft <-: dcl.dcl_functions
               |  ft.ft_ident.id_name == ident
               ]
    , menv)

// Maybe return the index of the fundef in the unique FunDef array
reifyFunDef :: String *ModuleEnv -> *(Maybe (Int, FunDef), *ModuleEnv)
reifyFunDef ident menv=:{me_fun_defs}
  # (fds, fun_defs) = extractFunDefs me_fun_defs
  # mfd = findInArr (\fd -> fd.fun_ident.id_name == ident) fds
  = (mfd, { menv & me_fun_defs = fun_defs })

reifySymbolType :: String *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifySymbolType ident menv
  # (mfd, menv) = reifyFunDef ident menv
  = case mfd of
      Just (_, fd)  -> case fd.fun_type of
                         Yes t -> (Just t, menv)
                         _     -> findInDcls menv
      _             -> findInDcls menv
  where
  findInDcls menv
    # (mft, menv) = reifyFunType ident menv
    = (maybe Nothing (\ft -> Just ft.ft_type) mft, menv)

fdArrToMap :: .{#FunDef} -> Map String FunDef
fdArrToMap fds = fromList [(d.fun_ident.id_name, d) \\ d <-: fds]

isCons :: String -> Bool
isCons str = str == "_Cons"

isNil :: String -> Bool
isNil str = str == "_Nil"

appIsList :: App -> Bool
appIsList app = isCons ident || isNil ident
  where ident = app.app_symb.symb_ident.id_name

exprIsListConstr :: Expression -> Bool
exprIsListConstr (App app) = appIsList app
exprIsListConstr _         = False

exprIsListCompr :: Expression -> Bool
exprIsListCompr (App app)  = appIsListComp app
exprIsListCompr _          = False

appIsListComp :: App -> Bool
appIsListComp app = isListCompr app.app_symb.symb_ident.id_name

isListCompr :: String -> Bool
isListCompr str = startsWith "c;" str // TODO: Verify

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead [x:_] = Just x

fromOptional :: a (Optional a) -> a
fromOptional x  No       = x
fromOptional _  (Yes x)  = x

optional :: b (a -> b) (Optional a) -> b
optional b  _  No       = b
optional _  f  (Yes x)  = f x

appFunName :: App -> String
appFunName app = app.app_symb.symb_ident.id_name

freeVarName :: FreeVar -> String
freeVarName fv = fv.fv_ident.id_name

dropContexts :: SymbolType [a] -> ([a], [a])
dropContexts st xs
  # args    = keep st.st_arity xs
  # numargs = length args
  = splitAt (length xs - numargs) xs

numContexts :: SymbolType -> Int
numContexts st = length st.st_context

funIsTask :: FunDef -> Bool
funIsTask fd =
  case (fd.fun_type, fd.fun_kind) of
    (Yes st, FK_Function _)  -> symTyIsTask st
    _                        -> False

identIsLambda :: Ident -> Bool
identIsLambda ident
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = ident.id_name

exprIsLambda :: Expression -> Bool
exprIsLambda (Var bv)  = identIsLambda bv.var_ident
exprIsLambda (App app) = identIsLambda app.app_symb.symb_ident
exprIsLambda _         = False

symTyIsTask :: SymbolType -> Bool
symTyIsTask st =
  case st.st_result.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

identIsTask :: String *ModuleEnv -> *(Bool, *ModuleEnv)
identIsTask ident menv
  # (mst, menv) = reifySymbolType ident menv
  = (maybe False symTyIsTask mst, menv)

symbIdentIsTask :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)
symbIdentIsTask sid menv = identIsTask sid.symb_ident.id_name menv

// TODO Look ident up in CommonDefs (for type constructors)
isInfix :: String *ModuleEnv -> *(Bool, *ModuleEnv)
isInfix ident menv
  # (mfd, menv) = reifyFunDef ident menv
  = case mfd of
      Just (_, fd) = (prioIsInfix fd.fun_priority, menv)
      Nothing
        # (mft, menv) = reifyFunType ident menv
        = case mft of
            Just ft  = (prioIsInfix ft.ft_priority, menv)
            _
              # (mcd, menv) = reifyConsDef ident menv
              = case mcd of
                  Just cd -> (prioIsInfix cd.cons_priority, menv)
                  Nothing -> abort ("Failed to determine fixity for " +++ ident)

prioIsInfix :: Priority -> Bool
prioIsInfix prio =
  case prio of
    Prio _ _  -> True
    _         -> False

getFunName :: FunDef -> String
getFunName fd = fd.fun_ident.id_name

getFunArgs :: FunDef -> [FreeVar]
getFunArgs {fun_body = TransformedBody tb} = tb.tb_args
getFunArgs _                               = abort "getFunArgs: need a TransformedBody"

getFunRhs :: FunDef -> Expression
getFunRhs {fun_body = TransformedBody tb} = tb.tb_rhs
getFunRhs _                               = abort "getFunRhs: need a TransformedBody"

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx (Just e) menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}
updateWithAnnot _ _ menv = menv

updateFunRhs :: Int !*{#FunDef} Expression -> !*{#FunDef}
updateFunRhs n fun_defs e
  # (fd, fun_defs) = fun_defs![n]
  # tb = case fd.fun_body of
           TransformedBody fb -> { fb & tb_rhs = e }
           _                  -> abort "updateFunRhs: need a TransformedBody"
  # fd = { fd & fun_body = TransformedBody tb }
  = { fun_defs & [n] = fd}

emptyEdge :: GEdge
emptyEdge = {GEdge | edge_pattern = Nothing }

mkEdge :: String -> GEdge
mkEdge str = {GEdge | edge_pattern = Just str }

getLetBinds :: Let -> [LetBind]
getLetBinds lt = lt.let_strict_binds ++ lt.let_lazy_binds

mkGLetBinds :: Let *ModuleEnv -> *([(String, String)], *ModuleEnv)
mkGLetBinds lt menv
  = foldrSt f (getLetBinds lt) ([], menv)
  where f bnd (xs, menv)
          # (pprhs, menv) = ppExpression bnd.lb_src menv
          = ([(bnd.lb_dst.fv_ident.id_name, ppCompact pprhs):xs], menv)

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st
foldrSt op l st = foldr_st l
  where
    foldr_st []     = st
    foldr_st [a:as] = op a (foldr_st as)


