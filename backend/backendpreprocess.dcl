definition module backendpreprocess

import checksupport

// assign sequence numbers to all variables in the syntax tree

// MW was:backendPreprocess :: ![Index] !IclModule !*VarHeap -> *VarHeap
backendPreprocess :: !Ident ![Index] !IclModule !*VarHeap -> *VarHeap
