definition module Heaprepr

// See syntaxstr for contents description

from StdFile import <<<
from StdOverloaded import toString
from Heap import HeapN,PtrN

from Heap import   Ptr
instance toString (Ptr a)
instance <<<      (Ptr a)
