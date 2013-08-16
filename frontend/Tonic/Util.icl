implementation module Tonic.Util

import StdEnv
import Data.Func
import Data.Functor
import Data.List
import Data.Maybe
import syntax
import Tonic.AbsSyn
import Text

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a
foldrArr f b arr = foldrArr` 0 f b arr
  where
  arrSz = size arr
  foldrArr` n f b arr
    | n < arrSz  = f (select arr n) (foldrArr` (n + 1) f b arr)
    | otherwise  = b

findInArr :: (e -> Bool) (a e) -> Maybe e | Array a e
findInArr p arr = findInArr` 0 p arr
  where
  arrSz = size arr
  findInArr` n p arr
    | n < arrSz
      #  elem = select arr n
      =  if (p elem) (Just elem) (findInArr` (n + 1) p arr)
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

dropAppContexts :: App ModuleEnv -> [Expression]
dropAppContexts app menv
  | appIsList app = app.app_args
  | otherwise
    # funTy  = fromMaybe (abort err)
             $ reifySymbolType menv ident
    = dropContexts funTy app.app_args
  where
  ident  = app.app_symb.symb_ident
  err    = "dropAppContexts : failed to find symbol type for " +++ ident.id_name

reifyFunType :: ModuleEnv Ident -> Maybe FunType
reifyFunType menv ident =
  safeHead  [  ft \\ dcl <-: menv.me_dcl_modules, ft <-: dcl.dcl_functions
            |  ft.ft_ident.id_name == ident.id_name
            ]

reifyFunDef :: ModuleEnv Ident -> Maybe GFunDef
reifyFunDef menv ident =
  case findInFunDefs menv.me_fun_defs of
    Just fd  -> Just $ mkGFunDef fd
    _        -> fmap mkGFunDef $ findInFunDefs menv.me_icl_module.icl_functions
  where
  identName = ident.id_name
  findInFunDefs fds = findInArr (\fd -> fd.fun_ident.id_name == identName) fds

reifySymbolType :: ModuleEnv Ident -> Maybe SymbolType
reifySymbolType menv ident =
  case findInArr (\fd -> fd.fun_ident.id_name == ident.id_name) menv.me_fun_defs of
    Just fd  -> optional findInDcls Just fd.fun_type
    _        -> findInDcls
  where
  findInDcls = maybe Nothing (\ft -> Just ft.ft_type) (reifyFunType menv ident)

persistHasRec :: [SynExpression] SynExpression -> SynExpression
persistHasRec ss syn = { syn & syn_has_recs = has }
 where has = foldr (\s b -> s.syn_has_recs || b) False ss

appIsCons :: App -> Bool
appIsCons app = app.app_symb.symb_ident.id_name == "_Cons"

appIsNil :: App -> Bool
appIsNil app = app.app_symb.symb_ident.id_name == "_Nil"

appIsList :: App -> Bool
appIsList app = appIsCons app || appIsNil app

exprIsListConstr :: Expression -> Bool
exprIsListConstr (App app) = appIsList app
exprIsListConstr _         = False

exprIsListCompr :: Expression -> Bool
exprIsListCompr (App app)  = appIsListComp app
exprIsListCompr _          = False

appIsListComp :: App -> Bool
appIsListComp app = startsWith "c;" app.app_symb.symb_ident.id_name // TODO: Verify

withHead :: (a -> b) b [a] -> b
withHead _  b  []       = b
withHead f  _  [x : _]  = f x

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead [x:_] = Just x

withTwo :: (a a -> b) b [a] -> b
withTwo f  _  [x : y : _]  = f x y
withTwo _  b  _            = b

fromOptional :: a (Optional a) -> a
fromOptional x  No       = x
fromOptional _  (Yes x)  = x

optional :: b (a -> b) (Optional a) -> b
optional b  _  No       = b
optional _  f  (Yes x)  = f x

freeVarName :: FreeVar -> String
freeVarName fv = fv.fv_ident.id_name

dropContexts :: SymbolType [a] -> [a]
dropContexts st xs
  # lst = numContexts st
  | lst > length xs = xs
  = drop lst xs

numContexts :: SymbolType -> Int
numContexts st = length st.st_context

numFunArgs :: GFunDef -> Int
numFunArgs fd = length fd.gfd_args

funIsTask :: FunDef -> Bool
funIsTask fd =
  case (fd.fun_type, fd.fun_kind) of
    (Yes st, FK_Function _)  -> symTyIsTask st
    _                        -> False

symbIdentIsLam :: SymbIdent -> Bool
symbIdentIsLam si = identIsLam si.symb_ident

identIsLam :: Ident -> Bool
identIsLam ident
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = ident.id_name

exprIsLam :: Expression -> Bool
exprIsLam (Var bv)  = identIsLam bv.var_ident
exprIsLam _         = False

symTyIsTask :: SymbolType -> Bool
symTyIsTask st =
  case st.st_result.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

identIsTask :: ModuleEnv Ident -> Bool
identIsTask menv ident = maybe False symTyIsTask $ reifySymbolType menv ident

symbIdentIsTask :: ModuleEnv SymbIdent -> Bool
symbIdentIsTask menv sid = identIsTask menv sid.symb_ident


//isInfix :: ModuleEnv SymbIdent -> Bool
//isInfix menv si
  //# mfd  = reifyFunDef menv si.symb_ident
  //# mft  = reifyFunType menv si.symb_ident
  //= case mfd of
      //Just fd  -> isInfix` fd.gfd_priority
      //Nothing  ->
        //case mft of
          //Just ft  -> isInfix` ft.ft_priority
          //_        -> abort ("Failed to determine fixity for " +++ si.symb_ident.id_name)
  //where
  //isInfix` prio =
    //case prio of
      //Prio _ _  -> True
      //_         -> False
