module rmPreprop

import StdEnv, Directory, StdLib, StdDebug

one_three =: "1.3"
two_zero =: "2.0"

intro_text current_dir_string =
	[ "This program can be used to remove the preprocessor statements\n"
	, "from your Clean sources. Consult the documentation about\n"
	, "differences between Clean 1.3 and Clean 2.0 to get more information\n"
	, "about the Clean preprocessor.\n"
	, "\n"
	, "This program will perform it's task on all .icl and .dcl files\n"
	, "in the current folder only. To process several folders you can move\n"
	, "this executable.\n"
	, "\n"
	, "This program will not alter the files in the current folder, but will\n"
	, "rather create two subfolders with the resulting 1.3 and 2.0 sources.\n"
	, "The subfolders are called \"", one_three, "\" and \"", two_zero, "\".\n"
	, "\n"
	, "Current directory:", current_dir_string, "\n"
	, "\n"
	, "Should I start? (y/n):"
	]
	

appStdio f w
	#! (io, w)
			= stdio w
	   (x, io, w)
	   		= f io w
	   (_, w)
	   		= fclose io w 
	= (x, w)
	   		
appStdio1 f w
	#! (_, w)
			= appStdio (\io w -> let io2 = f io in (0, io2, w)) w
	= w

intro io w
	#! (current_dir_path, w)
	   		= getCurrentDirectory w
	   (current_dir_string, w)
	   		= pathToPD_String current_dir_path w
	   io
	   		= foldlSt fwrites (intro_text current_dir_string) io
	   (answer, io)
	   		= freadline io
	   io
	   		= fwrites "\n" io
	= (size answer>0 && (answer.[0]=='y' || answer.[0]=='Y'), io, w)

perform w
	#! (filenames, w)
			= getFilenames w
	| isEmpty filenames
		= (False, w)
	#! (ok, w)
	   		= makeSubfolders w
	| not ok
		= (ok, w)
	= loop filenames w
  where
	getFilenames w
		#! ((err, dir_entries), w)
				= getDirectoryContents (RelativePath []) w
		| err<>NoDirError
			#! w
					= appStdio1 (fwrites "Error:can't retrieve contents of current directory\n\n") w
			= ([], w)
		= ([fileName \\ {fileName}<-dir_entries | endsWith fileName ".dcl" || endsWith fileName ".icl"], w)
	endsWith s suffix
		#! size_s = size s
		= s % (size_s-size suffix, size_s-1)==suffix
	makeSubfolders w
		#! (ok1, w)
				= makeSubfolder one_three w
		   (ok2, w)
				= makeSubfolder two_zero w
		= (ok1 && ok2, w)
	makeSubfolder name w
		#! (err, w)
				= createDirectory (RelativePath [PathDown name]) w
		= (err==NoDirError || err==AlreadyExists, w)
	loop [] w
		= (True, w)
	loop [filename:filenames] w
		#! (ok, w)
				= performOnFile filename w
		| not ok
			= (ok, w)
		= loop filenames w
	performOnFile filename w
		#! (ok, input, w)
				= fopen filename FReadData w
		| not ok
			= (ok, w)
		#! (ok1, out13, w)
				= openOutputfile one_three filename w
		   (ok2, out20, w)
				= openOutputfile two_zero filename w
		| not ok1 || not ok2
			= (False, w)
		#! (input, out13, out20)
				= fileLoop input out13 out20
		   (_, w)
		   		= fclose input w
		   (_, w)
		   		= fclose out13 w
		   (_, w)
		   		= fclose out20 w
		= (True, w)
	  where
		fileLoop :: !*File !*File !*File -> (!*File, !*File, !*File)
		fileLoop input out13 out20
			#! (isEof, input)
					= fend input
			| isEof
				= (input, out13, out20)
			#! (line, input)
					= freadline input
			| beginsWith "//1.3" line
				= oneThree input out13 out20
			| beginsWith "/*2.0" line
				= twoZero input out13 out20
			#! out13
					= fwrites line out13
			   out20
					= fwrites line out20
			= fileLoop input out13 out20
		oneThree :: !*File !*File !*File -> (!*File, !*File, !*File)
		oneThree input out13 out20
			#! (isEof, input)
					= fend input
			| isEof
				= (input, out13, out20)
			#! (line, input)
					= freadline input
			| beginsWith "//3.1" line
				= fileLoop input out13 out20
			#! out13
					= fwrites line out13
			= oneThree input out13 out20
		twoZero :: !*File !*File !*File -> (!*File, !*File, !*File)
		twoZero input out13 out20
			#! (isEof, input)
					= fend input
			| isEof
				= (input, out13, out20)
			#! (line, input)
					= freadline input
			| beginsWith "0.2*/" line
				= fileLoop input out13 out20
			#! out20
					= fwrites line out20
			= twoZero input out13 out20
		beginsWith praefix line
			= line % (0, size praefix-1) == praefix
	openOutputfile subdir_name filename w
		#! (pd_path, w)
				= pathToPD_String (RelativePath [PathDown subdir_name, PathDown filename]) w
		   (ok, file, w)
		   		= fopen pd_path FWriteData w
		| not ok
			#! w
					= appStdio1 (fwrites ("Error:can't open "+++pd_path+++".\n\n")) w
			= (ok, file, w)
		= (ok, file, w)

byebye ok io
	#! io
			= fwrites (if ok "Work done.\n\n" "Couldn't finish work.\n\n") io
	   io
	   		= fwrites "Push enter to quit" io
	   (_, io)
	   		= freadline io
	= io

Start w
	#! (do_it, w)
			= appStdio intro w
	| not do_it
		= w
	#! (ok, w)
			= perform w
	   w
	   		= appStdio1 (byebye ok) w
	= w