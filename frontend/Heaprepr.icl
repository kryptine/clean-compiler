implementation module Heaprepr

import Heap
import StdFile
import StdOverloaded

instance toString (Ptr a)
where toString p = "<"+++toString (ptrToInt p)+++">"

instance <<< (Ptr a)
where (<<<) file p = file <<< toString p
