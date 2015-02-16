definition module ctags

import syntax, checksupport

mkCtags :: String IclModule !*{# FunDef} !*Files -> *(!*{# FunDef}, !*Files)
