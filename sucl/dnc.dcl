definition module dnc

// $Id$

from graph import Graph,Node
from StdString import String
from StdOverloaded import ==

// dnc is like varcontents, but can give a more reasonable error message
// when the contents is used when undefined.
dnc :: (var->.String) !.(Graph sym var) var -> (.Bool,Node sym var) | == var
