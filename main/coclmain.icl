/*
	module owner: Ronny Wichers Schreur
*/
implementation module coclmain

import StdEnv
import StdDebug
import ArgEnv
import set_return_code

import compile

coclMain :: ![{#Char}] !*World -> *World
// currentVersion latestDefVersion latestImpVersion testArgs world
coclMain  testArgs world
	# world
		=	set_return_code 0 world
	# (commandArgs, world)
		=	getCommandArgs (tl [arg \\ arg <-: getCommandLine]) testArgs world 
	# (symbol_table,world)
		= init_identifiers newHeap world
	# (success, world)
		=	accFiles (compiler symbol_table) world
	=	set_return_code (if success 0(-1)) world
	where
		getCommandArgs :: [{#Char}] [{#Char}] *World -> ([{#Char}], *World)
		getCommandArgs [] testArgs world
			=	getArgs testArgs world
		getCommandArgs realArgs _ world
			=	getArgs realArgs world

		getArgs :: [{#Char}] *World -> ([{#Char}], *World)
		getArgs ["--dump-args" : commandArgs] world
			# (opened, file, world)
				=	fopen CoclArgsFile FWriteText world
			| not opened
				=	abort ("--dump-args " +++ CoclArgsFile +++ " could not be opened\n")
			# file
				=	foldSt (\s -> fwritec '\n' o fwrites s) commandArgs file
			# (closed, world)
				=	fclose file world
			| not closed
				=	abort ("--dump-args " +++ CoclArgsFile +++ " could not be closed\n")
			=	(commandArgs, world)
		getArgs ["--restore-args"] world
			# (opened, file, world)
				=	fopen CoclArgsFile FReadText world
			| not opened
				=	abort ("--restore-args " +++ CoclArgsFile +++ " could not be opened\n")
			# (commandArgs, file)
				=	readArgs [] file
			# (closed, world)
				=	fclose file world
			| not closed
				=	abort ("--restore-args " +++ CoclArgsFile +++ " could not be closed\n")
			=	(commandArgs, world)
			where
				readArgs :: [{#Char}] *File -> ([{#Char}], *File)
				readArgs reversedArgs file
					# (arg, file)
						=	freadline file
					| arg == ""
						=	(reverse reversedArgs, file)
					// otherwise
						=	readArgs [chopNewline arg : reversedArgs] file

				chopNewline :: {#Char} -> {#Char}
				chopNewline s
					| s.[n-1] == '\n'
						=	s % (0, n-2)
					// otherwise
						=	s
					where
						n
							=	size s
		getArgs commandArgs world
			=	(commandArgs, world)

CoclArgsFile :== "coclargs.txt"

/*
import thread_message;

import code from "thread_message.obj";
*/

// compiler driver

/* Windows
compiler symbol_table files
	# dcl_cache = empty_cache symbol_table
	| length commandArgs==2 && commandArgs!!0=="-ide"
		# wm_number=get_message_number;
		# thread_id=hex_to_int (commandArgs!!1);
		= (True,compile_files compile dcl_cache thread_id wm_number files)
		# (r,dcl_cache,files)=compile commandArgs dcl_cache files
		= (r,files)
	where
		commandArgs
			=	tl [arg \\ arg <-: getCommandLine]
*/
// Unix
compiler symbol_table files
	# dcl_cache = empty_cache symbol_table
	| length commandArgs==3 && commandArgs!!0=="--pipe"
		# commands_name= (commandArgs!!1);
		# results_name= (commandArgs!!2);
		= (True,compile_loop compile dcl_cache commands_name results_name files)
		# (r,dcl_cache,files)=compile commandArgs dcl_cache files
		= (r,files)
	where
		commandArgs
			=	tl [arg \\ arg <-: getCommandLine]
// ... Unix

hex_to_int :: {#Char} -> Int
hex_to_int s
	= hex_to_int 0 0;
	where
		l=size s;

		hex_to_int i n
			| i==l
				= n;
				# c=s.[i];
				# i=i+1;
				# n=n<<4;
				| c<='9'
					= hex_to_int i (n bitor (toInt c-toInt '0'));
					= hex_to_int i (n bitor (toInt c-(toInt 'A'-10)));

string_to_args string
	= string_to_args 0;
	where
		l=size string;
		
		string_to_args i
			# end_spaces_i=skip_spaces i;
			| end_spaces_i==l
				= []
			| string.[end_spaces_i]=='"'
				# next_double_quote_i=skip_to_double_quote (end_spaces_i+1)
				| next_double_quote_i>=l
					= [string % (end_spaces_i,l-1)]
					# arg=string % (end_spaces_i+1,next_double_quote_i-1);
					= [arg : string_to_args (next_double_quote_i+1)];
				# space_i=skip_to_space (end_spaces_i+1)
				| space_i>=l
					= [string % (end_spaces_i,l-1)]
					# arg=string % (end_spaces_i,space_i-1);
					= [arg : string_to_args (space_i+1)];

		skip_spaces i
			| i>=l
				= l;
			# c=string.[i];
			| c==' ' || c=='\t'
				= skip_spaces (i+1);
				= i;

		skip_to_space i
			| i>=l
				= l;
			# c=string.[i];
			| c==' ' || c=='\t'
				= i;
				= skip_to_space (i+1);

		skip_to_double_quote i
			| i>=l
				= l;
			# c=string.[i];
			| c=='"'
				= i;
				= skip_to_double_quote (i+1);

// Unix
import ipc
import code from "ipc.o"

compile_loop compile cache commands results files
	# r=open_pipes commands results;
	| r<>0
		= abort ("compile_loop\n");
	=	compile_files compile cache files
	

compile_files compile cache files
	# n = get_command_length;
	| n==(-1)
		= abort "compile_files 1";
	# string=createArray n '\0';
	# r=get_command string;
	| r<>0
		= abort ("compile_files 2 ");
	# args=string_to_args (string % (0,size string-2))
	= case args of
		["cocl":cocl_args]
			# (ok,cache,files)=compile cocl_args cache files
			# result=if ok 0(-1);
			# r=send_result result
			| r<>0
				-> abort "compile_files 3";
				-> compile_files compile cache files
		["quit"]
			-> trace_n "quiting" files;
		_
				-> abort "compile_files 4"
