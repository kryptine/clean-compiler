implementation module ctags

import syntax, checksupport, StdFile, StdOrdList, _SystemArray

from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
from filesystem import ensureDirectoryExists
import Data.Maybe

mkCtags :: String IclModule !*{# FunDef} !*Files -> *(!*{# FunDef}, !*Files)
mkCtags mod_dir icl_mod fun_defs files
  # csf_directory_path   = "Clean System Files"
  # tagsdir              = csf_directory_path +++ {DirectorySeparator} +++ icl_mod.icl_name.id_name +++ {DirectorySeparator}
  # (ok, files)          = ensureCleanSystemFilesExists csf_directory_path files
  # (ok, files)          = ensureDirectoryExists tagsdir files
  # (ok, tags, files)    = fopen (tagsdir +++ "tags") FWriteText files
  | not ok               = (fun_defs, files)
  # (fun_tags, fun_defs) = mkFunTags mod_dir fun_defs
  # cons_tags            = mkTypeTags mod_dir icl_mod
  # tags                 = fwrites (concatStrings (sort (fun_tags ++ cons_tags))) tags
  | not ok               = (fun_defs, files)
  # (ok, files)          = fclose tags files
  = (fun_defs, files)

mkFunTags :: String !*{# FunDef} -> *([String], !*{# FunDef})
mkFunTags mod_dir fun_defs = foldrArr mkTag [] fun_defs
  where
  mkTag fun_def tags
    | fun_def.fun_info.fi_def_level == 1  = funToTag fun_def tags
    | otherwise                           = tags
  funToTag fun_def tags
    # fun_id = fun_def.fun_ident.id_name
    = if (startsWith "TD;" fun_id)
        tags
        (prependTag fun_id mod_dir fun_def.fun_pos "v" tags)

mkTypeTags :: String .IclModule -> [String]
mkTypeTags mod_dir icl_mod = fst (foldrArr mkTypeTag [] icl_mod.icl_common.com_type_defs)
                          ++ fst (foldrArr mkConsTag [] icl_mod.icl_common.com_cons_defs)
  where
  mkTypeTag type_def tags = prependTag type_def.td_ident.id_name mod_dir type_def.td_pos "t" tags
  mkConsTag cons_def tags = prependTag cons_def.cons_ident.id_name mod_dir cons_def.cons_pos "d" tags

prependTag :: String String Position String [String] -> [String]
prependTag id_name mod_dir pos ex tags
  = case posToString pos of
      Just posStr
        = [id_name +++ "\t" +++ mod_dir +++ posStr +++ ";\"\t" +++ ex +++ "\n" : tags]
      _ = tags

posToString :: Position -> Maybe String
posToString (FunPos  filename lineNo _) = Just (filename +++ "\t" +++ toString lineNo)
posToString (LinePos filename lineNo)   = Just (filename +++ "\t" +++ toString lineNo)
posToString _                           = Nothing

startsWith :: !String !String -> Bool
startsWith needle haystack
  # s_needle = size needle
  = s_needle <= size haystack && needle == haystack % (0, s_needle - 1)

dropChars :: !Int !String -> String
dropChars n s = s % (n, size s - 1)

foldrArr f b arr = foldrArr` 0 f b arr
  where
  foldrArr` n f b arr
    | n < size arr
      # (elem, arr`) = arr ! [n]
      # (rec, arr`) = foldrArr` (n + 1) f b arr`
      = (f elem rec, arr`)
    | otherwise  = (b, arr)

concatStrings :: [String] -> .String
concatStrings l = updateS 0 l (createArray (sum [size s \\ s <- l]) ' ')
  where
    updateS :: !Int [{#Char}] *{#Char} -> *{#Char}
    updateS i [] s
      =  s
    updateS i [h : t] s
      =  updateS (i + size h) t {s & [pos] = c \\ c <-: h & pos <- [i..]}
