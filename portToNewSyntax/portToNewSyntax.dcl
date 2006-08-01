definition module portToNewSyntax

from StdMisc import abort

from StdFile import :: Files
from scanner import :: SearchPaths

import checksupport

switch_port_to_new_syntax port dont_port :== port

cTabWidth :== 4

writeExplImportsToFile :: !String ![([Declaration],a)] !{#u:DclModule} !*CheckState 
		-> (!{#u:DclModule},!.CheckState)

createPortedFiles :: !String !SearchPaths !*Files -> (!Bool, !*Files)
