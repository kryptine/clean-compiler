definition module cli

// $Id$

from coreclean import SuclSymbol,SuclVariable,SuclTypeSymbol,SuclTypeVariable
from rule import Rule

:: Cli

typerule :: Cli SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
