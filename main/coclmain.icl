implementation module coclmain

CoclMainVersion :== 0

import StdEnv
import ArgEnv
import Version
import set_return_code

import compile

// coclMain :: ![{#Char}] !*World -> *World
// testArgs world
coclMain :== coclMainWithVersionCheck CoclMainVersionCurrent CoclMainVersionLatestDef CoclMainVersionLatestImp

CoclMainVersionCurrent
	:==	0x02000205
CoclMainVersionLatestDef
	:==	0x02000205
CoclMainVersionLatestImp
	:==	0x02000205

checkVersion :: VersionsCompatability *File -> (!Bool, !*File)
checkVersion VersionsAreCompatible errorFile
	=	(True, errorFile)
checkVersion VersionObservedIsTooNew errorFile
	#	errorFile
			=	fwrites "[Coclmain] the library is too new\n" errorFile
	=	(False, errorFile)
checkVersion VersionObservedIsTooOld errorFile
	#	errorFile
			=	fwrites "[Coclmain] the library is too old\n" errorFile
	=	(False, errorFile)

coclMainWithVersionCheck :: !Int !Int !Int ![{#Char}] !*World -> *World
// currentVersion latestDefVersion latestImpVersion testArgs world
coclMainWithVersionCheck  currentVersion latestDefVersion latestImpVersion testArgs world
	# observedVersion =
		{	versionCurrent
				=	CoclMainVersionCurrent
		,	versionOldestDefinition
				=	CoclMainVersionLatestDef
		,	versionOldestImplementation
				=	CoclMainVersionLatestImp
		}
	  expectedVersion =
		{	versionCurrent
				=	currentVersion
		,	versionOldestDefinition
				=	latestDefVersion
		,	versionOldestImplementation
				=	latestImpVersion
		}
	| not (fst (checkVersion (versionCompare expectedVersion observedVersion) stderr))
		=	set_return_code (-1) world
	# (success, world)
		=	accFiles (compiler commandArgs) world
	=	set_return_code (if success 0(-1)) world
	where
		commandArgs
			=	if (length realArgs == 0) testArgs realArgs
		realArgs
			=	tl [arg \\ arg <-: getCommandLine]

import thread_message;

import code from "thread_message.obj";

compiler :: ![{#Char}] *Files -> *(!Bool,!*Files);
compiler commandArgs files
	| length commandArgs==2 && commandArgs!!0=="-ide"
		# wm_number=get_message_number;
		# thread_id=hex_to_int (commandArgs!!1);
		= (True,compile_files (empty_cache newHeap) thread_id wm_number files)
		# (r,cache,files)=compile commandArgs (empty_cache newHeap) files
		= (r,files)

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

compile_files cache thread_id wm_number files
	# (r,a,s) =get_integers_from_message wm_number;
	| r==0
		= abort "compile_files 1";
	# string=createArray a '\0';
	# r=get_string_from_file_map_and_delete_map s string;
	| r==0
		= abort ("compile_files 2 ");
	# args=string_to_args (string % (0,size string-2))
	= case args of
		["cocl":cocl_args]
			# (ok,cache,files)=compile cocl_args cache files
			# result=if ok 0(-1);
			# r=send_integers_to_thread thread_id wm_number 0 result;
			| r==0
				-> abort "compile_files 3";
				-> compile_files cache thread_id wm_number files
		["exit"]
			-> files;
		_
				-> abort "compile_files 4"
