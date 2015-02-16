implementation module ctags

import syntax, checksupport, StdFile, StdOrdList, _SystemArray

from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
from filesystem import ensureDirectoryExists

mkCtags :: String IclModule !*{# FunDef} !*Files -> *(!*{# FunDef}, !*Files)
mkCtags mod_dir icl_mod fun_defs files
  # csf_directory_path = "Clean System Files"
  # tagsdir            = csf_directory_path +++ {DirectorySeparator} +++ icl_mod.icl_name.id_name +++ {DirectorySeparator}
  # (ok, files)        = ensureCleanSystemFilesExists csf_directory_path files
  # (ok, files)        = ensureDirectoryExists tagsdir files
  # (ok, tags, files)  = fopen (tagsdir +++ "tags") FWriteText files
  | not ok             = (fun_defs, files)
  # (tlst, fun_defs)   = mkTags` mod_dir fun_defs
  # tags               = fwrites (concatStrings (sort tlst)) tags
  | not ok             = (fun_defs, files)
  # (ok, files)        = fclose tags files
  = (fun_defs, files)

// TODO Extract constructor definitions
mkTags` :: String !*{# FunDef} -> *([String], !*{# FunDef})
mkTags` mod_dir fun_defs = foldrArr mkTag [] fun_defs
  where
  mkTag fun_def tags
    | fun_def.fun_info.fi_def_level == 1  = funToTag fun_def fun_def.fun_ident.id_name fun_def.fun_pos tags
    | otherwise                           = tags
  funToTag fun_def fun_id (FunPos filenm lnr _) tags = tagToStr fun_def fun_id filenm (toString lnr) tags
  funToTag fun_def fun_id (LinePos filenm lnr)  tags = tagToStr fun_def fun_id filenm (toString lnr) tags
  funToTag _   _      _                     tags = tags
  tagToStr fun_def fun_id filenm lnr tags
    # isTypeDef = startsWith "TD;" fun_id
    # funtag    = if isTypeDef
                    (dropChars 3 fun_id)
                    fun_id
    = let mkEntry ex = [funtag +++ "\t" +++ mod_dir +++ filenm +++ "\t" +++ toString lnr +++ ";\"\t" +++ ex +++ "\n" : tags]
      in  if isTypeDef
            (mkEntry "t")
            (mkEntry "v")

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
