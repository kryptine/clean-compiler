This file explains how to build a valid cocl that reads
Clean 1.3 sources and as a sideeffect produces sources
in which the explicit import statements have been
ported to 2.0 syntax ("coclPort" application)

The module portToNewSyntax appears twice: in the "compiler"
folder and in the "portToNewSyntax" folder. Iff you want
to build coclPort then set the paths in such a way that
the portToNewSyntax.dcl/icl files from the portToNewSyntax
folder are preferred over the same files in the compiler
folder.

Further set the "switch_import_syntax" macro in module
syntax to "one_point_three"

The "switch_port_to_new_syntax" macro in module 
portToNewSyntax is used to ed/disable the porting
facilities:
portToNewSyntax/portToNewSyntax.dcl: port
compiler/portToNewSyntax.dcl: dont_port
