definition module portToNewSyntax
// see the file readme.txt in the portToNewSyntax folder about
// this module

from StdMisc import abort
//1.3
from StdFile import Files
from StdString import String
from scanner import SearchPaths
//3.1
/*2.0
from StdFile import :: Files
from scanner import :: SearchPaths
0.2*/
import checksupport

switch_port_to_new_syntax port dont_port :== dont_port

cTabWidth :== 4

writeExplImportsToFile :: !String ![([Declaration],a)] !{#u:DclModule} !*CheckState 
		-> (!{#u:DclModule},!.CheckState)

createPortedFiles :: !String !SearchPaths !*Files -> (!Bool, !*Files)
