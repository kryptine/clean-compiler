implementation module dnc

// $Id$

import graph
import basic
import StdEnv

// dnc is like varcontents, but can give a more reasonable error message
// when the contents is used when undefined.
dnc :: (var->.String) !.(Graph sym var) var -> (.Bool,Node sym var) | == var
dnc makemessage graph var
| fst vc = vc
         = (False,(wrong "symbol",wrong "arguments"))
  where vc = varcontents graph var
        wrong element = abort ("getting "+++element+++" of free variable: "+++makemessage var)
