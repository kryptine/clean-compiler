definition module pretty

from StdFile import <<<
from StdString import String

/*  Pretty printing
    ===============

    We don't want to have to concatenate strings all the time.

    Here's a puny data structure for pretty printing.
    It's relatively easy to generate, fits most needs.

    The idea is to generate this once, and then run along it once
    as the constituent strings are written to an output file.

*/

:: Layout
   = Line String            // A single line
   | Indent String [Layout] // A sequence of lines, the first of which is indented by a string (and the rest by an equivalent number of spaces)

class Pretty t
where pretty :: t -> Layout

// We can pretty-print strings (and via it everything that can be written as a string).
instance Pretty {#Char}

// Layout structures can be written to a file.
instance <<< Layout
