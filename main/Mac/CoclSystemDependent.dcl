// this is for the PowerMac
definition module CoclSystemDependent

from StdFile import Files

PathSeparator
	:==	','
DirectorySeparator
	:==	':'

script_handler :: !{#Char} *Files -> (!Int,!*Files);

clean2_compile :: !Int -> Int;

clean2_compile_c_entry :: !Int -> Int;
