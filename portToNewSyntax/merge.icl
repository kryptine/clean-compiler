implementation module merge

import StdEnv, RWSDebug, StdArrayExtensions

from syntax import Optional, Yes, No
import utilities, portToNewSyntax

mergeFiles ::  !*File !*File !*File -> (!.File,!.File,!.File)
mergeFiles old inferred new
	# (lines_within_comment, old)
			= lines_in_comment old
	= merge_files lines_within_comment 0 old inferred new

merge_files ::  ![Int] !Int !*File !*File !*File -> (!.File,!.File,!.File)
merge_files lines_within_comment line_nr old inferred new
	# (end, old) = fend old
	| end
		# (inferred, new)
				= copy_rest inferred new
		= (old, inferred, new)
	# (line, old) = my_freadline old
	  line_l = [ ch \\ ch<-:line ]
	| not (begins_with_from line_l) || isMember line_nr lines_within_comment
		= merge_files lines_within_comment (line_nr+1) old inferred (fwrites line new)
	# new = fwrites ("//1.3\n"+++(complete_line line)) new
	  (new_line_nr, module_names, old, new)
	  		= copy_original_from_statements line_nr line_l [] old new
  // insert inferred part
  	  new = fwrites ("//3.1\n/*2.0\n") new
	  (inferred, new)
	  		= foldSt insert_inferred_from_stmnt module_names (inferred, new)
	= merge_files lines_within_comment new_line_nr old inferred (fwrites "0.2*/\n" new)

copy_original_from_statements line_nr line_l mod_names_accu old new
	# (left_space, module_name) = get_ls_and_mn line_l
	  (line_nr, opt_next_from_statement, old, new) = layout_skip line_nr left_space old new
	= case opt_next_from_statement of
		No
			-> (line_nr, reverse [module_name:mod_names_accu], old, new)
		Yes line_l`
			-> copy_original_from_statements line_nr line_l` [module_name:mod_names_accu]
					old new

insert_inferred_from_stmnt module_name (inferred, new)
	# (first_line_of_import, inferred) = my_freadline inferred
	  new = foldSt fwrites ["from ", module_name, " ", first_line_of_import] new
  	= copy_rest_of_import inferred new
	
begins_with_from line_l
	# without_spaces = dropWhile isSpace line_l
	= case without_spaces of
		['from'] -> True
		['from',ch:_] -> not (isAlphanum ch || isMember ch ['`_']) 
		_ -> False

get_ls_and_mn line_l
	# (spaces, rest1) = span isSpace line_l
	  without_from = drop 4 rest1
	  (_, rest2) = span isSpace without_from
	  module_name = takeWhile (not o isSpace) rest2
	= (space_count spaces 0, toString module_name)

space_count [] _
	= 0
space_count [' ':spaces] modTabWidth
	= 1+(space_count spaces ((modTabWidth+1) mod modTabWidth))
space_count ['\t':spaces] modTabWidth
	= (cTabWidth-modTabWidth)+(space_count spaces 0)
space_count ['\n':_] _
	= 0

layout_skip :: !Int !Int !*File !*File -> (!Int, !Optional [Char], !.File, !.File)
layout_skip line_nr left_space old new
	# (end, old) = fend old
	| end
		= (line_nr, No, old, new)
	# (cur_pos, old) = fposition old
	  (line, old) = my_freadline old
	  line_l = [ ch \\ ch<-:line ]
	  spaces = takeWhile isSpace line_l
	| space_count spaces 0<=left_space
		| begins_with_from line_l
			= (line_nr+1, Yes line_l, old, fwrites (complete_line line) new) 
		= (line_nr+1, No, snd (fseek old cur_pos FSeekSet), new)
	= layout_skip (line_nr+1) left_space old (fwrites (complete_line line) new)

copy_rest_of_import :: !*File !*File -> (!.File, !.File)
copy_rest_of_import inferred new
	# (end, inferred) = fend inferred
	| end
		= (inferred ,new)
	# (cur_pos, inferred) = fposition inferred
	  (line, inferred) = my_freadline inferred
	| line % (0,5)=="import"
		= (snd (fseek inferred cur_pos FSeekSet), new)
	= copy_rest_of_import inferred (fwrites line new)

complete_line line
	| line.[size line-1]<>'\n'
		= line+++"\n"
	= line	

copy_rest inferred new
	# (end, inferred) = fend inferred
	| end
		= (inferred, new)
	# (line, inferred)
			= my_freadline inferred
	= copy_rest inferred (fwrites line new)

lines_in_comment file
	# (cur_pos, file)
			= fposition file
	  (rev_lines_within_comment, file)
	  		= get_lic 0 [] file
	= (reverse rev_lines_within_comment, snd (fseek file cur_pos FSeekSet))
  where
	get_lic :: !Int ![Int] !*File -> (![Int], !*File)
	get_lic line_nr line_nr_accu file
		# (end, file)
				= fend file
		| end
			= (line_nr_accu, file)
		# (line, file)
				= my_freadline file
		  line_l
		  		= [ch \\ ch<-:line]
		# (bwc, rest)
				= begins_with_comment line_l
		| bwc
			= consider_comment 1 rest line_nr line_nr_accu file
		= get_lic (line_nr+1) line_nr_accu file

	begins_with_comment ['//1.3':rest]
		= (True, rest)
	begins_with_comment line_l
	  	 # without_spaces
	  	  		= dropWhile isSpace line_l
		= case without_spaces of
			['/*':rest]
				-> (True, rest)
			_
				-> (False, [])

	consider_comment nesting_level ['*/':rest] line_nr line_nr_accu file
		| nesting_level==1
			= get_lic line_nr line_nr_accu file
		= consider_comment (nesting_level-1) rest line_nr line_nr_accu file
	consider_comment nesting_level ['/*':rest] line_nr line_nr_accu file
		= consider_comment (nesting_level+1) rest line_nr line_nr_accu file
	consider_comment nesting_level [_:rest] line_nr line_nr_accu file
		= consider_comment nesting_level rest line_nr line_nr_accu file
	consider_comment nesting_level [] line_nr line_nr_accu file
		# (end, file)
				= fend file
		| end
			= ([], file)
		# (line, file)
				= my_freadline file
		  line_l
		  		= [ch \\ ch<-:line]
		= case line_l of
			['//3.1':rest]
				| nesting_level==1
					-> get_lic (line_nr+1) [line_nr+1:line_nr_accu] file
				-> consider_comment (nesting_level-1) rest (line_nr+1) [line_nr+1:line_nr_accu] file
			_
				-> consider_comment nesting_level line_l (line_nr+1) [line_nr+1:line_nr_accu] file

my_freadline :: !*File -> (!String, !*File)
my_freadline file
	#! (line, file) = freadline file
	   last_char_ix = size line - 1
	   last_printable_char_ix = findrArrElt isntNewlineOnAnyPlatform line last_char_ix
	| last_printable_char_ix==(-1)
		= ("\n", file)
	| last_printable_char_ix==last_char_ix
		= (line, file)
	| last_printable_char_ix==last_char_ix-1 && line.[last_char_ix]=='\n'
		= (line, file)
	= ({line & [last_printable_char_ix+1] = '\n' } %(0, last_printable_char_ix+1), file)

isntNewlineOnAnyPlatform '\xA' = False
isntNewlineOnAnyPlatform '\xD' = False
isntNewlineOnAnyPlatform _ = True

