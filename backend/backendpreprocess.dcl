definition module backendpreprocess

import checksupport

// assign sequence numbers to all variables in the syntax tree

backendPreprocess :: !Ident ![Index] !IclModule !*VarHeap -> *VarHeap
