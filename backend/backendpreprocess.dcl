definition module backendpreprocess

import checksupport

// assign sequence numbers to all variables in the syntax tree

backendPreprocess :: ![Index] !IclModule !*VarHeap -> *VarHeap
