implementation module scanner

import	StdEnv, compare_constructor, StdCompare, general

from utilities import revCharListToString, isSpecialChar

/*
Known bug:
functions names starting with '->' require a ';' after the type. Solutions:
1) Make '->' an ordinary token. This implies that we have to write 'a-> .b' instead 
   of 'a->.b'.
2) re-scan token in new context. Requires substantial changes.
3) Determine offsides before token is generated. Tricky since we do not know the
   actual context of the new token or/and have to take care of generating the right
   amount of offsides. 
*/
::	SearchPaths	:== [String]

::	* ScanState =
	{	ss_input		::	ScanInput
	,	ss_offsides		::	! [(Int, Bool) ]	// (column, defines newDefinition)
	,	ss_useLayout	::	! Bool
	,	ss_tokenBuffer	::	! Buffer LongToken
	}

::	* ScanInput
	=	Input			Input
	|	PushedToken		LongToken ScanInput

::	* Input =
	{	inp_stream		::	! InputStream
	,	inp_filename	::	String
	,	inp_pos			::	! FilePosition
	,	inp_tabsize		::	! Int
	,	inp_charBuffer	::	! Buffer (Char,FilePosition)
	//,	inp_curToken	::	! [ Char ]
	}

::	* InputStream
	=	InFile			! * File
	|	InLOC			! [Char]
	|	OldChar			! Char ! FilePosition ! InputStream
	|	OldChars		! [Char] ! InputStream
	|	OldToken		! LongToken	! InputStream

::	FilePosition =
	{	fp_line			::	! Int
	,	fp_col			::	! Int
	}

::	LongToken =
	{	lt_position		::	! FilePosition	// Start position of this token
	,	lt_token		::	! Token			// The token itself
//	,	lt_chars		::	! [Char]		// The chars in this token
//	,	lt_context		::	! Context		// The context of the scanning of this token
	}

::	Buffer x
	=	Buffer0
	|	Buffer1 x
	|	Buffer2 x x
	|	Buffer3 x x x // buffer size is 3.

::	Token
	= 	IdentToken ! .String	//		an identifier
	|	IntToken !.String		//		an integer
	|	RealToken !.String		//		a real
	|	StringToken !.String	//		a string
	|	CharToken !.String		//		a character
	|	CharListToken !.String	//		a character list '{char}*'
	|	BoolToken !Bool			//		a boolean
	|	OpenToken				//		(
	|	CloseToken				//		)
	|	CurlyOpenToken			//		{
	|	CurlyCloseToken			//		}
	|	SquareOpenToken			//		[
	|	SquareCloseToken		//		]

	|	DotToken				//		.
	|	SemicolonToken			//		;
	|	ColonToken				//		:
	|	DoubleColonToken		//		::
	|	CommaToken				//		,
	|	ExclamationToken		//		!
	|	BarToken				//		|
	|	ArrowToken				//		->
	|	DoubleArrowToken		//		=>
	|	EqualToken				//		=
	|	DefinesColonToken		//		=:
	|	ColonDefinesToken		//		:==
	|	WildCardToken			//		_
	|	BackSlashToken			//		\
	|	DoubleBackSlashToken	//		\\
	|	LeftArrowToken			//		<-
	|	LeftArrowColonToken		//		<-:
	|	DotDotToken				//		..
	|	AndToken				//		&
	|	HashToken				//		#
	|	AsteriskToken			//		*
	|	LessThanOrEqualToken	//		<=

	|	ModuleToken				//		module
	|	ImpModuleToken			//		implementation
	|	DefModuleToken			//		definition
	|	SysModuleToken			//		system

	|	ImportToken				//		import
	|	FromToken				//		from
	|	SpecialToken			//		special

	|	IntTypeToken			//		Int
	|	CharTypeToken			//		Char
	|	RealTypeToken			//		Real
	|	BoolTypeToken			//		Bool
	|	StringTypeToken			//		String
	|	FileTypeToken			//		File
	|	WorldTypeToken			//		World
	|	VoidTypeToken			//		Void
	|	LeftAssocToken			//		left
	|	RightAssocToken			//		right
	|	ClassToken				//		class
	|	InstanceToken			//		instance
	|	OtherwiseToken			//		otherwise

	|	IfToken					//		if
	|	WhereToken				//		where
	|	WithToken				//		with
	|	CaseToken				//		case
	|	OfToken					//		of
	|	LetToken Bool			//		let!, let
	|	SeqLetToken Bool		//		#!, #
	|	InToken					//		in

	|	DynamicToken			//		dynamic
	|	DynamicTypeToken		//		Dynamic

	|	PriorityToken Priority	//		infixX N

	|	CodeToken				//		code
	|	InlineToken				//		inline
	|	CodeBlockToken [String]	//		{...}

	|	NewDefinitionToken		//		generated automatically, OffsideToken.
	|	EndGroupToken			//		generated automatically
	|	EndOfFileToken			//		end of file
	|	ErrorToken String		//		an error has occured

::	Context
	=	GeneralContext
	|	TypeContext
	|	FunctionContext
	|	CodeContext

instance == Context
where
	(==) co1 co2 = equal_constructor co1 co2

::	Assoc
	=	LeftAssoc
	|	RightAssoc
	|	NoAssoc

::	Priority
	=	Prio Assoc Int
	|	NoPrio

//
//	Macros for error messages
//
ScanErrIllegal	:== "illegal char in input"
ScanErrCharErr	:== "wrong character denotation"
ScanErrNLString	:== "new line in string denotation"
ScanErrWild		:== "ident should not start with _"

class getFilename state :: !*state -> (!String,!*state)

instance getFilename ScanInput
where
	getFilename (Input input)
		# (filename,input) = input!inp_filename
		= (filename,Input input)
	getFilename (PushedToken tok input)
		# (filename,input) = getFilename input
		= (filename,PushedToken tok input)

instance getFilename ScanState
where
	getFilename scanState=:{ss_input}
		# (filename,ss_input) = getFilename ss_input
		= (filename,{scanState & ss_input = ss_input })

class getPosition state :: !*state -> (!FilePosition,!*state)  // Position of current Token (or Char)

instance getPosition ScanState
where
	getPosition scanState=:{ss_tokenBuffer}
		| isEmptyBuffer ss_tokenBuffer
			= getCharPosition scanState
		# (ltok,_) = get ss_tokenBuffer
		= (ltok.lt_position, scanState)

instance getPosition Input
where
	getPosition input=:{inp_pos} = (inp_pos, input)

class getCharPosition state :: !*state -> (FilePosition,!*state)

instance getCharPosition ScanState
where
	getCharPosition scanState=:{ss_input=Input input}
		# (pos,input) = getPosition input
		= (pos,{ scanState & ss_input = Input input })
	getCharPosition scanState=:{ss_input=PushedToken longToken _}
		= (longToken.lt_position,scanState)

instance getCharPosition Input
where getCharPosition input=:{inp_pos} = (inp_pos, input)

class nextToken state :: !Context !*state -> (!Token, !*state)

instance nextToken ScanState
where
	nextToken newContext scanState=:{ss_input=input=:PushedToken token=:{lt_position,lt_token/*,lt_context*/} rest,ss_tokenBuffer}
//		| lt_context == newContext || ~ (contextDependent lt_token) || isGeneratedToken lt_token
//		| True
		=	(	lt_token
			,	{ scanState
				& ss_input			= rest
				, ss_tokenBuffer	= store token ss_tokenBuffer
				}
			)  //-->> ("nextToken: pushed token", lt_token)
/*		=	nextToken newContext { scanState & ss_input = pushTokensBack input}
	where
		pushTokensBack input=:(Input _) = input
		pushTokensBack (PushedToken token input)
			# (Input input=:{inp_stream}) = pushTokensBack input
			= Input
				{ input
				& inp_stream = OldToken token inp_stream
				}  //-->> ("pushTokensBack",token)
*/	nextToken context scanState=:{ss_input=Input inp,ss_tokenBuffer,ss_offsides,ss_useLayout}
		# (error, c, inp) 	= SkipWhites inp
		  (pos, inp)		= inp!inp_pos
		  scanState			= {scanState & ss_input = Input inp }
		= case error of
			Yes string	->	( ErrorToken string
							,	{	scanState
								&	ss_tokenBuffer	= store
												{	lt_position 	= pos
												,	lt_token		= ErrorToken string
											//	,	lt_chars		= []
											//	,	lt_context		= context
												}
												scanState.ss_tokenBuffer
								}
							) -->> ("Error token generated",string)
			no			->	determineToken c scanState
	where
		determineToken c scanState=:{ss_input=Input inp}
			#	(eof, inp)	= EndOfInput inp
				(pos, inp)	= inp!inp_pos
			|	eof && c == NewLineChar
				#	newToken	= EndOfFileToken
				=	checkOffside pos newToken
						{ scanState
						& ss_tokenBuffer	= store
												{	lt_position 	= pos
												,	lt_token		= newToken
											//	,	lt_chars		= []
											//	,	lt_context		= context
												}
												scanState.ss_tokenBuffer
						, ss_input = Input inp
						} // -->> (EndOfFileToken,pos)
			// otherwise // ~ (eof && c == NewLineChar)
				#	(token, inp)	= Scan c inp /* {inp & inp_curToken = [c]}*/ context
			//	#	(chars, inp)	= inp!inp_curToken
				= checkOffside pos token
					{ scanState
					& ss_input 			= Input inp
					, ss_tokenBuffer	= store
											{	lt_position 	= pos
											,	lt_token		= token
										//	,	lt_chars		= reverse chars
										//	,	lt_context		= context
											}
											ss_tokenBuffer
					}	 //-->> (token,pos)
	nextToken _ _ = abort "Scanner: Error in nextToken"

class tokenBack state :: !*state -> !*state

instance tokenBack ScanState
where
	tokenBack scanState=:{ss_tokenBuffer, ss_input}
		| isEmptyBuffer ss_tokenBuffer = abort "tokenBack with empty token buffer"
		# (tok, buf) = get ss_tokenBuffer
		=	{ scanState
			& ss_tokenBuffer	= buf
			, ss_input			= PushedToken tok ss_input
			
			} // -->> ("tokenBack", tok, buf)

class currentToken state :: !*state -> (!Token, !*state)

instance currentToken ScanState
where currentToken scanState=:{ss_tokenBuffer}
		| isEmptyBuffer ss_tokenBuffer
			= (ErrorToken "dummy", scanState)
			= ((head ss_tokenBuffer).lt_token, scanState)

class insertToken state :: !Token !Context !*state -> *state

instance insertToken ScanState
where
	insertToken t c scanState
/*		#	chars = if (isGeneratedToken t)
						[]
						(fromString (toString t))
*/		#	(pos, scanState=:{ss_input}) = getPosition scanState
		=	{ scanState
			& ss_input = PushedToken
							{ lt_position	= pos
							, lt_token		= t
						//	, lt_chars		= chars
						//	, lt_context	= c
							}
							ss_input
			}
/*
isGeneratedToken :: !Token -> Bool
isGeneratedToken NewDefinitionToken = True
isGeneratedToken EndGroupToken      = True
isGeneratedToken (CodeBlockToken _) = True
isGeneratedToken _					= False
*/

class replaceToken state :: !Token !*state -> *state

instance replaceToken ScanState
where
	replaceToken tok scanState=:{ss_tokenBuffer}
		# (longToken,buffer) = get ss_tokenBuffer
		= { scanState
		  & ss_tokenBuffer = store { longToken & lt_token = tok } buffer
		  }

SkipWhites :: !Input -> (!Optional String, !Char, !Input)
SkipWhites input
	# (eof, c, input)		= ReadChar input
	| eof					= (No, NewLineChar, input) // -->> "EOF in SkipWhites"
	| IsWhiteSpace c		= SkipWhites input
							= TryScanComment c input

TryScanComment :: !Char !Input -> (!Optional String, !Char, !Input)
TryScanComment c1=:'/' input
	# (eof,c2, input)		= ReadChar input
	| eof					= (No, c1, input)
	= case c2 of
		'/' -> SkipWhites (SkipToEndOfLine input)
		'*' -> case ScanComment input of
				(No,input)	-> SkipWhites input
				(er,input)	-> (er, c1, input)
		_   -> (No, c1, charBack input)
TryScanComment c input
	= (No, c, input)

ScanComment	:: !Input -> (!Optional String, !Input)
ScanComment input
	# (eof1, c1, input)	= ReadChar input
	| eof1				= (Yes "end of file encountered inside comment", input)
	| c1 == '/'
		# (eof2, c2, input)	= ReadChar input
		| eof2				= (Yes "end of file encountered inside comment", input)
							= case c2 of
								'/'	->	ScanComment (SkipToEndOfLine input)
								'*'	->	case ScanComment input of
											(No, input) -> ScanComment input
											error		-> error
								_	->	ScanComment input
	| c1 == '*'
		# (eof2, c2, input)	= ReadChar input
		| eof2				= (Yes "end of file encountered inside comment", input)
		| c2 == '/'			= (No, input)
							= ScanComment input
	| otherwise				= ScanComment input

SkipToEndOfLine	:: !Input -> !Input
SkipToEndOfLine input
	# (eof, c, input)	= ReadChar input
	| eof				= input
	| c==NewLineChar	= input
			= SkipToEndOfLine input
/*
SkipToChar :: ! Char ! Input -> Input
SkipToChar c input
	# (eof, c1, input)		= ReadChar input
	| eof || c1 == c		= input
							= SkipToChar c input
*/
Scan :: !Char !Input !Context -> (!Token, !Input)
Scan '(' input co			= (OpenToken, input)
Scan ')' input co			= (CloseToken, input)
Scan '{' input CodeContext	= ScanCodeBlock input
Scan '{' input co			= (CurlyOpenToken, input)
Scan '}' input co			= (CurlyCloseToken, input)
Scan '[' input co			= (SquareOpenToken, input)
Scan ']' input co			= (SquareCloseToken, input)
Scan c0=:'|' input co
	# (eof, c1, input)		= ReadChar input
	| eof					= (BarToken, input)
	| isSpecialChar c1		= ScanOperator 1 input [c1, c0] co
							= (BarToken, charBack input)
Scan ',' input co			= (CommaToken, input)
Scan ';' input co			= (SemicolonToken, input)
Scan '#' input TypeContext	= (HashToken, input)
Scan c0=:'#' input co
	# (strict, input)		= determineStrictness input
	| strict
		= (SeqLetToken strict, input)
	# (eof,c1, input)		= ReadChar input
	| eof
		= (SeqLetToken False, input)
	| isSpecialChar c1
		= ScanOperator 1 input [c1, c0] co
	// otherwise
		= (SeqLetToken strict, charBack input)
Scan '*' input TypeContext	= (AsteriskToken, input)
Scan c0=:'&' input co
	# (eof, c1, input)		= ReadChar input
	| eof					= (AndToken, input)
	| isSpecialChar c1		= ScanOperator 1 input [c1, c0] co
							= (AndToken, charBack input)
Scan c0=:'.' input co
	= case co of
		TypeContext

						-> (DotToken, input)
		_	# (eof, c1, input) = ReadChar input
			| eof		-> (DotToken, input)
			| c1 <> '.'	-> (DotToken, charBack input)
			# (eof, c2, input) = ReadChar input
			| eof		-> (DotDotToken, input)
			| isSpecialChar c2
						-> ScanOperator 2 input [c2, c1, c0] co
						-> (DotDotToken, charBack input)
Scan '!' input TypeContext	= (ExclamationToken, input)
Scan '\\' input co
	# (eof, c, input)		= ReadChar input
	| eof					= (BackSlashToken, input)
	| c == '\\'				= (DoubleBackSlashToken, input)
							= (BackSlashToken, charBack input)
Scan c0=:'_' input co
	# (eof, c1, input)		= ReadChar input
	| eof					= (WildCardToken, input)
	| IsIdentChar c1	co	= ScanIdent 1 input [c1, c0] co
//	| isSpecialChar c1		= ScanOperator 1 input [c1, c0] co
							= (WildCardToken, charBack input)
Scan c0=:'<' input TypeContext
	# (eof, c1, input)		= ReadChar input
	| eof					= (ErrorToken "< just before end of file in TypeContext", input)
	| c1 == '='				= (LessThanOrEqualToken, input)
							=  ScanOperator 0 (charBack input) [c0] TypeContext
Scan c0=:'<' input co
	# (eof, c1, input)		= ReadChar input
	| eof 					= (IdentToken "<", input)
	| c1 <> '-'				= ScanOperator 0 (charBack input) [c0] co
	# (eof, c2, input)		= ReadChar input
	| eof					= (LeftArrowToken, input)
	| c2 == ':'	
		# (eof, c3, input)		= ReadChar input
		| eof					= (LeftArrowColonToken, input)
		| isSpecialChar c3		= ScanOperator 3 input [c3, c2, c1, c0] co
								= (LeftArrowColonToken, charBack input)
	| isSpecialChar c2		= ScanOperator 2 input [c2, c1, c0] co
							= (LeftArrowToken, charBack input)
Scan c0=:'-' input co
	# (eof, c1, input)		= ReadChar input
	| eof					= (IdentToken "-", input)
	# new					= newExp input.inp_charBuffer
	| IsDigit c1 && new		= ScanNumeral 1 input [c1,c0]
	| c1 <> '>'				= ScanOperator 0 (charBack input) [c0] co
	| co == TypeContext		= (ArrowToken, input)	// -> is a reserved symbol in a type context
							// Can cause an error when token (like ->.) is read in wrong context
	# (eof, c2, input)		= ReadChar input		
	| eof					= (ArrowToken, input)
	| isSpecialChar c2		= ScanOperator 2 input [c2, c1, c0] co
							= (ArrowToken, charBack input)
Scan c0=:'+' input co
	# (eof, c1, input)		= ReadChar input
	| eof					= (IdentToken "+", input)
	# new					= newExp input.inp_charBuffer
	| IsDigit c1 && new		= ScanNumeral 1 input [c1,c0]
							= ScanOperator 0 (charBack input) [c0] co
Scan c0=:'=' input co
	# (eof, c, input)		= ReadChar input
	| eof					= (EqualToken, input)
	| c == ':'				= (DefinesColonToken, input)
	| c == '>'				= (DoubleArrowToken, input)
	| isSpecialChar c		= ScanOperator 1 input [c, c0] co
							= (EqualToken, charBack input)
Scan c0=:':' input co
	# (eof,c1, input)		= ReadChar input
	| eof					= (ColonToken, input)
	| c1 == ':'				= (DoubleColonToken, input)
	| c1 <> '='
		| isSpecialChar c1	= ScanOperator 1 input [c1, c0] co
							= (ColonToken, charBack input)
	# (eof, c2, input)		= ReadChar input
	| eof					= ScanOperator 1 input [c1, c0] co
	| c2 == '='				= (ColonDefinesToken, input)
							= ScanOperator 1 (charBack input) [c1, c0] co
Scan c0=:'\'' input co		= ScanChar input [c0]
Scan c0=:'\"' input co		= ScanString 0 input [c0]
Scan c    input co
	| IsDigit c				= ScanNumeral 0 input [c]
	| IsIdentChar c	co		= ScanIdent 0 input [c] co
	| isSpecialChar c		= ScanOperator 0 input [c] co
							= (ErrorToken ScanErrIllegal, input)

newExp :: !(Buffer (Char,FilePosition)) -> Bool
newExp buffer
	# (c, _)	= case buffer of
					Buffer3 _ _ cp	-> cp
					_				-> (' ',{fp_line=0,fp_col=0})
	= new_exp_char c
where
	new_exp_char ',' = True
	new_exp_char '[' = True
	new_exp_char '(' = True
	new_exp_char '/' = True // to handle end of comment symbol: */
	new_exp_char c	 = isSpace c

ScanIdent :: !Int !Input ![Char] !Context -> (!Token, !Input)
ScanIdent n input token co
	# (eof, c, input)		= ReadChar input
	| eof					= CheckReserved co (revCharListToString n token) input
	| IsIdentChar c co		= ScanIdent (n + 1) input [c:token] co
							= CheckReserved co (revCharListToString n token) (charBack input)


ScanOperator :: !Int !Input ![Char] !Context -> (!Token, !Input)
ScanOperator n input token co
	#  (eof, c, input)		= ReadChar input
	| eof					= (IdentToken (revCharListToString n token), input)
	| isSpecialChar c		= ScanOperator (n + 1) input [c:token] co
							= CheckReserved co (revCharListToString n token) (charBack input)

CheckReserved :: !Context !String !Input -> (!Token, !Input)
CheckReserved GeneralContext    s i = CheckGeneralContext s i
CheckReserved TypeContext       s i = CheckTypeContext s i
CheckReserved FunctionContext	s i = CheckFunctContext s i
CheckReserved CodeContext		s i = CheckCodeContext s i

CheckGeneralContext	:: !String !Input -> (!Token, !Input)
CheckGeneralContext s input
 = case s of
	"module"     		-> (ModuleToken		, input)
	"definition"  		-> (DefModuleToken	, input)
	"implementation"	-> (ImpModuleToken	, input)
	"system"			-> (SysModuleToken	, input)
	"import"     		-> (ImportToken		, input)
	"from" 				-> (FromToken		, input)
	"in"  	    		-> (InToken			, input)
	s					-> CheckEveryContext s input

CheckEveryContext :: !String !Input -> (!Token, !Input)
CheckEveryContext s input
 = case s of
	"where"		->	(WhereToken			, input)
	"with"		->	(WithToken			, input)
	"class" 	->	(ClassToken			, input)
	"instance"	->	(InstanceToken		, input)
	"otherwise"	->	(OtherwiseToken		, input)
	"!"			->	(ExclamationToken	, input)
//	"::"		->	(DoubleColonToken	, input)
	"*/"		->	(ErrorToken "Unexpected end of comment, */", input)
	"infixr"	#	(error, n, input) = GetPrio  input
				->	case error of
						Yes err -> (ErrorToken err						, input)  //-->> ("Error token generated: "+err)
						No		-> (PriorityToken (Prio RightAssoc n)	, input)
	"infixl"	#	(error, n, input) = GetPrio  input
				->	case error of
						Yes err -> (ErrorToken err						, input)  //-->> ("Error token generated: "+err)
						No		-> (PriorityToken (Prio LeftAssoc n)	, input)
	"infix"		#	(error, n, input) = GetPrio  input
				->	case error of
						Yes err -> (ErrorToken err						, input)  //-->> ("Error token generated: "+err)
						No		-> (PriorityToken (Prio NoAssoc n)		, input)
	s			->	(IdentToken s		, input)

CheckTypeContext :: !String !Input -> (!Token, !Input)
CheckTypeContext s input
 = case s of
 	"Int"		->	(IntTypeToken		, input)
	"Char"		->	(CharTypeToken		, input)
	"Real"		->	(RealTypeToken		, input)
	"Bool"		->	(BoolTypeToken		, input)
	"String"	->	(StringTypeToken	, input)
	"File"		->	(FileTypeToken		, input)
	"World"		->	(WorldTypeToken		, input)
	"Dynamic"	->	(DynamicTypeToken	, input)
	"special"	->	(SpecialToken		, input)
	"from" 		->	(FromToken			, input)
	s			->	CheckEveryContext s input

CheckFunctContext :: !String !Input -> (!Token, !Input)
CheckFunctContext s input
 = case s of
	"if"		->	(IfToken			, input)
	"True"		->	(BoolToken True		, input)
	"False"		->	(BoolToken False	, input)
	"case"		->	(CaseToken			, input)
	"of"		->	(OfToken			, input)
	"system"	->	(SysModuleToken		, input)
	"import"	->	(ImportToken		, input)
	"from"		->	(FromToken			, input)
	"let" 	    #	(strict, input) = determineStrictness input
				->	(LetToken strict, input)
//	"Let" 	    #	(strict, input) = determineStrictness input
//				->	(SeqLetToken strict	, input)
	"in"  	    ->	(InToken			, input)
	"dynamic"  	->	(DynamicToken		, input)
	"code"		->	(CodeToken			, input)
	s			->	CheckEveryContext s input

CheckCodeContext :: !String !Input -> (!Token, !Input)
CheckCodeContext s input
 = case s of
	"inline"	->	(InlineToken		, input)
	s			->	CheckEveryContext s input	

GetPrio :: !Input -> (!Optional String, !Int, !Input)
GetPrio input
	# (error, c, input) = SkipWhites input
	| IsDigit c
		= (error, digitToInt c, input)
		= (error, defaultPrio , charBack input)
where defaultPrio = 0

determineStrictness :: !Input -> (!Bool, !Input)
determineStrictness input
	# (eof, c, input)		= ReadChar input
	| eof					= (False, input)
	| c == '!'				= (True, input)
							= (False, charBack input)

ScanCodeBlock :: !Input -> (!Token, !Input)
ScanCodeBlock input
	= scan_code_block [] input
where
	scan_code_block :: ![String] !Input -> (!Token,!Input)
	scan_code_block acc input
		# (eof, c, input)	= ReadChar input
		| c == '}'
			= (CodeBlockToken (reverse acc), input)
		| isNewLine c
			| eof
				= (ErrorToken "eof in code block", input)
				= scan_code_block acc input
		| IsWhiteSpace c
				= scan_code_block acc input
		# (line, input)		= ReadLine input
		= scan_code_block [toString c+stripNewline line:acc] input

stripNewline :: !String -> String
stripNewline string
	# size = size string
	= case size of
		0 -> string
		1 | isNewLine string.[0]
			-> ""
			-> string
		_ | isNewLine string.[size-1]
			| isNewLine string.[size-2]
				-> string%(0,size-3)
				-> string%(0,size-2)
			-> string
		

ScanNumeral	:: !Int !Input [Char] -> (!Token, !Input)
ScanNumeral n input chars=:['0':r]
	| isEmpty r || r == ['+']
		# (eof, c, input)		= ReadChar input
		| eof					= (IntToken (revCharListToString n chars), input)
		| c == 'x'
			# (eof, c1, input)	= ReadChar input
			| eof				= (IntToken "0", charBack input)
			| isHexDigit c1		= ScanHexNumeral (hexDigitToInt c1) input
								= (IntToken "0", charBack (charBack input))
		| isOctDigit c			= ScanOctNumeral (digitToInt c) input
		| c == '.'				= TestFraction n input chars
								= (IntToken "0", charBack input)
	| r == ['-']
		# (eof, c, input)		= ReadChar input
		| eof					= (IntToken (revCharListToString n chars), input)
		| c == 'x'
			# (eof, c1, input)	= ReadChar input
			| eof				= (IntToken "0", charBack input)
			| isHexDigit c1		= ScanHexNumeral (~ (hexDigitToInt c1)) input
								= (IntToken "0", charBack (charBack input))
		| isOctDigit c			= ScanOctNumeral (~ (digitToInt c)) input
		| c == '.'				= TestFraction n input chars
								= (IntToken "0", charBack input)
ScanNumeral n input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (IntToken (revCharListToString n chars), input)
	| IsDigit c				= ScanNumeral (n + 1) input [c:chars]
	| c == 'E'				= ScanExponentSign (n + 1) input [c:chars]
	| c == '.'				= TestFraction n input chars
							= (IntToken (revCharListToString n chars), charBack input)

TestFraction :: !Int !Input ![Char] -> (!Token, !Input)
TestFraction n input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (ErrorToken ("Incorrect Real at end of file: "+(revCharListToString (n+1) ['.':chars])), input)
	| IsDigit c				= ScanFraction (n + 2) input [c,'.':chars]
			 				= (IntToken (revCharListToString n chars), charBack (charBack input))

ScanFraction :: !Int !Input ![Char] -> (!Token, !Input)
ScanFraction n input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (RealToken (revCharListToString n chars), input)
	| c == 'E'				= case chars of
								[c:_] | IsDigit c	-> ScanExponentSign (n + 1) input [c:chars]
								_					-> ScanExponentSign (n + 2) input [c,'0':chars]
	| IsDigit c				= ScanFraction (n + 1) input [c:chars]
							= case chars of
								[c:_] | IsDigit c	-> (RealToken (revCharListToString n chars), charBack input)
								_					-> (RealToken (revCharListToString (n+1) ['0':chars]), charBack input)

ScanExponentSign :: !Int !Input ![Char] -> (!Token, !Input)
ScanExponentSign n input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (RealToken (revCharListToString n chars), input)
	| c == '+'				= ScanExponent n input chars
	| c == '-' || IsDigit c	= ScanExponent (n+1) input [c:chars]
	| otherwise				= (ErrorToken ("Digit or sign expected after "+revCharListToString n chars), charBack input)

ScanExponent :: !Int !Input ![Char] -> (!Token, !Input)
ScanExponent n input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (RealToken (revCharListToString n chars), input)
	| IsDigit c				= ScanExponent (n + 1) input [c:chars]
							= case chars of
								[c:_] | IsDigit c	-> (RealToken (revCharListToString n chars), charBack input)
								_					-> (ErrorToken ("Digit expected after "+revCharListToString n chars), charBack input)

ScanHexNumeral	:: !Int !Input -> (!Token, !Input)
ScanHexNumeral n input
	# (eof, c, input)		= ReadChar input
	| eof					= (IntToken (toString n), input)
	| isHexDigit c			= ScanHexNumeral (n*16+hexDigitToInt c) input
							= (IntToken (toString n), charBack input)

ScanOctNumeral	:: !Int !Input -> (!Token, !Input)
ScanOctNumeral n input
	# (eof, c, input)		= ReadChar input
	| eof					= (IntToken (toString n), input)
	| isOctDigit c			= ScanOctNumeral (n*8+digitToInt c) input
							= (IntToken (toString n), charBack input)

ScanChar :: !Input ![Char] -> (!Token, !Input)
ScanChar input chars
	# (eof, c, input)		= ReadChar input
	| eof					= (ErrorToken "End of file inside Char denotation", input)
	| '\\' <> c				= ScanEndOfChar 1 [c: chars] input
	# (chars, n, input)		= ScanBSChar 0 chars input
	= ScanEndOfChar n chars input

ScanBSChar :: !Int ![Char] !Input -> (![Char], !Int, !Input)
ScanBSChar n chars input
	# (eof, c, input)		= ReadChar input
	| eof					= (chars, n, input)
	= case c of
		'n'		->	(['n','\\':chars], n + 2, input)
		'r'		->	(['r','\\':chars], n + 2, input)
		'f'		->	(['f','\\':chars], n + 2, input)
		'b'		->	(['b','\\':chars], n + 2, input)
		't'		->	(['t','\\':chars], n + 2, input)
		'v'		->	(['v','\\':chars], n + 2, input)
		'\\'	->	(['\\','\\':chars], n + 2, input)
		'"'		->	(['"' ,'\\':chars], n + 2, input)
		'\''	->	(['\'','\\':chars], n + 2, input)
		'x'		#	(cc,input) = ScanNumChar Hex isHexDigit 2 0 input // max 2 characters
				->	to_chars cc n input
		'd'		#	(cc,input) = ScanNumChar Dec isDigit 3 0 input // max 3 characters
				->	to_chars cc n input
		c | IsOct c
				#	(cc,input) = ScanNumChar Oct IsOct 2 (digitToInt c) input // max 3 characters, including current
				->	to_chars cc n input
				->	([c:chars], n + 1, input)
where
	ScanNumChar base valid 0 acc input
		= (acc, input)
	ScanNumChar base valid n acc input
		# (eof, c, input)		= ReadChar input
		| eof					= (acc, input)
		| valid c				= ScanNumChar base valid (n-1) (base*acc+digitToInt c) input
								= (acc, charBack input)	
	Hex = 16
	Oct = 8
	Dec = 10
	
	to_chars cc n input
	 = case toChar cc of
		'\n'	->	(['n','\\':chars], n + 2, input)
		'\r'	->	(['r','\\':chars], n + 2, input)
		'\f'	->	(['f','\\':chars], n + 2, input)
		'\b'	->	(['b','\\':chars], n + 2, input)
		'\t'	->	(['t','\\':chars], n + 2, input)
		'\v'	->	(['v','\\':chars], n + 2, input)
		'\\'	->	(['\\','\\':chars], n + 2, input)
//		'"'		->	(['"' ,'\\':chars], n + 2, input)
		'\''	->	(['\'','\\':chars], n + 2, input)
	 	c		->	([c:chars], n + 1, input)

ScanEndOfChar :: !Int ![Char] !Input -> (!Token, !Input)
ScanEndOfChar n chars input
	# (eof, c, input)		= ReadChar input
	| eof					= (ErrorToken "End of file inside char denotation", input)
	| '\'' == c				= (CharToken (revCharListToString (n + 1) [c:chars]), input)
							= ScanCharList (n+1) [c:chars] input
//							= (ErrorToken ScanErrCharErr, input)

ScanCharList :: !Int ![Char] !Input -> (!Token, !Input)
ScanCharList n chars input
	# (eof, c, input)		= ReadChar input
	| eof					= (ErrorToken "End of file inside char list denotation", input)
	= case c of
		'\''		#	charList	= revCharListToString n chars % (1,n) // without '\''
					->	(CharListToken charList, input)
		'\\'		#	(chars, n, input)	= ScanBSChar n chars input
					->	ScanCharList n chars input
		NewLineChar	->	(ErrorToken "newline in char list", input)
		_			->	ScanCharList (n+1) [c:chars] input

ScanString :: !Int !Input ![Char] -> (!Token, !Input)
ScanString n input chars
 # (eof, c, input)		= ReadChar input
 | eof					= (ErrorToken "End of file inside String denotation", input)
 = case c of 
	'\\' 		#  (chars, n, input) = ScanBSChar n chars input
		 		-> ScanString n input chars
	'\"' 		-> (StringToken (revCharListToString (n + 1) [c:chars]), input)
	NewLineChar -> (ErrorToken ScanErrNLString, input)
	_	 		-> ScanString (n + 1) input [c:chars]

/*
	some predicates on tokens
*/

isLhsStartToken :: ! Token -> Bool
isLhsStartToken OpenToken       = True
isLhsStartToken SquareOpenToken	= True
isLhsStartToken CurlyOpenToken	= True
isLhsStartToken (IdentToken id) = True
isLhsStartToken token           = False

isOffsideToken :: ! Token -> Bool
isOffsideToken NewDefinitionToken	= True
isOffsideToken EndGroupToken		= True
isOffsideToken EndOfFileToken		= True
isOffsideToken token				= False

isEndGroupToken :: ! Token -> Bool
isEndGroupToken EndGroupToken = True
isEndGroupToken CurlyCloseToken = True
isEndGroupToken token = False
/*
contextDependent :: !Token -> Bool
contextDependent HashToken 			= True
//contextDependent (SeqLetToken _)	= True // Do not do this XXXXXX
contextDependent _					= False
*/
/*
	character functions
*/

//IsWhiteSpace	:: Char	-> Bool
IsWhiteSpace c :== isSpace c

//IsDigit	:: Char	-> Bool
IsDigit c :== isDigit c

IsOct c :== '0' <= c && c <= '7'

//IsHex c :== isDigit c || ('A' <= c && c <= 'F') || ('a' <= c && c <= 'f') 
/*
isHexDigit :: !Char -> Bool // Defined in StdChar
isHexDigit c
	| isDigit c
		= True
	| c < 'g'
		= c >= 'a'
	| c < 'G'
		= c >= 'A'
		= False
*/
//IsIdentChar	:: !Char !Context -> Bool
//IsIdentChar c co
// :== isAlphanum c ||	c == '_' ||	c == '`' ||	(c == '^' && co == TypeContext)

hexDigitToInt :: !Char -> Int
hexDigitToInt 'a' = 10
hexDigitToInt 'A' = 10
hexDigitToInt 'b' = 11
hexDigitToInt 'B' = 11
hexDigitToInt 'c' = 12
hexDigitToInt 'C' = 12
hexDigitToInt 'd' = 13
hexDigitToInt 'D' = 13
hexDigitToInt 'e' = 14
hexDigitToInt 'E' = 14
hexDigitToInt 'f' = 15
hexDigitToInt 'F' = 15
hexDigitToInt c   = digitToInt c

IsIdentChar :: !Char !Context -> Bool
IsIdentChar  c	_ | isAlphanum c	= True
IsIdentChar '_'	_ 					= True
IsIdentChar '`'	_					= True
IsIdentChar '^'	TypeContext			= True
IsIdentChar  _	_					= False

/*
	Input functions
*/

EndOfInput :: !Input -> (!Bool, !Input)
EndOfInput input=:{inp_stream = InFile file}
	# (endoffile, file) = fend file
	= (endoffile, { input & inp_stream = InFile file })
EndOfInput f=:{inp_stream = InLOC []}	= (True, f)
EndOfInput input						= (False, input)

ReadChar :: !Input -> (!Bool, !Char, !Input) // Bool indicates end of file, we read always newlines in an empty file
ReadChar input=:{inp_stream = InFile file, inp_pos, inp_tabsize, inp_charBuffer /*, inp_curToken*/}
	#!	(s, file) = freadline file
		eof = s == ""
	| eof
		#	c	= NewLineChar
			pos	= NextPos c inp_pos inp_tabsize
		=	(	eof
			,	c
			,	{	input
				&	inp_stream		= InFile file
				,	inp_pos			= pos
				,	inp_charBuffer	= store (c,pos) inp_charBuffer
			//	,	inp_curToken	= [c:inp_curToken]
				}
			) // -->> ("EOF in " + input.inp_filename + " found in ReadChar")
	// otherwise // s <> ""
		# chars = fromString s
		= ReadChar { input & inp_stream = OldChars chars (InFile file) }
/*	#! (eof, file) = fend file								// old, too slow
	| eof
		#	c	= NewLineChar
			pos	= NextPos c inp_pos inp_tabsize
		=	(	eof
			,	c
			,	{	input
				&	inp_stream		= InFile file
				,	inp_pos			= pos
				,	inp_charBuffer	= store (c,pos) inp_charBuffer
			//	,	inp_curToken	= [c:inp_curToken]
				}
			) // -->> ("EOF in " + input.inp_filename + " found in ReadChar")
	#! (ok, c, file) = freadc file
	| ok
		#	pos			= NextPos c inp_pos inp_tabsize
			(c,input`)	= correctNewline c pos inp_tabsize (InFile file)
		=	(	False
			,	c
			,	{	input
				&	inp_stream		= input`
				,	inp_pos			= pos
				,	inp_charBuffer	= store (c,pos) inp_charBuffer
			//	,	inp_curToken	= [c:inp_curToken]
				}
			)
		= abort "ReadChar failure" */
ReadChar input =: {inp_stream = OldChar c pos oldfile, inp_charBuffer /*, inp_curToken*/}
	=	(	False
		,	c
		,	{	input
			&	inp_stream		= oldfile
			,	inp_pos			= pos
			,	inp_charBuffer	= store (c,pos) inp_charBuffer
		//	,	inp_curToken	= [c:inp_curToken]
			}
		)
ReadChar input =: {inp_stream = OldChars [c:rest] stream, inp_pos, inp_tabsize, inp_charBuffer /*, inp_curToken*/}
	#	pos			= NextPos c inp_pos inp_tabsize
		(c,input`)	= correctNewline c pos inp_tabsize (OldChars rest stream)
	=	(	False
		,	c
		,	{	input
			&	inp_stream		= input`
			,	inp_pos			= pos
			,	inp_charBuffer	= store (c,pos) inp_charBuffer
		//	,	inp_curToken	= [c:inp_curToken]
			}
		)
ReadChar input =: {inp_stream = OldChars [] stream, inp_pos}
		= ReadChar {input & inp_stream = stream}
ReadChar input =: {inp_stream = InLOC [c : r], inp_pos, inp_tabsize /*, inp_curToken*/, inp_charBuffer}
	# pos	= NextPos c inp_pos inp_tabsize
	=	(	False
		,	c
		,	{	input
			&	inp_stream		= InLOC r
			,	inp_pos			= pos
			,	inp_charBuffer	= store (c,pos) inp_charBuffer
		//	,	inp_curToken	= [c:inp_curToken]
			}
		)
ReadChar input =: {inp_stream = InLOC [], inp_pos, inp_tabsize /*, inp_curToken*/, inp_charBuffer}
	#	c	= NewLineChar
		pos	= NextPos c inp_pos inp_tabsize
	=	(	True
		,	c
		,	{	input
			&	inp_pos			= pos
			,	inp_charBuffer	= store (c,pos) inp_charBuffer
		//	,	inp_curToken	= [c:inp_curToken]
			}
		)
		//-->> ("EOF of InLOC found in ReadChar")
/*
ReadChar input =: {inp_stream = OldToken {lt_chars,lt_position} stream, inp_charBuffer}
	#	pos	= lt_position
		c	= hd lt_chars
	=	(	False
		,	c
		,	{	input
			&	inp_stream		= OldChars (tl lt_chars) stream
			,	inp_pos			= pos
			,	inp_charBuffer	= store (c,pos) inp_charBuffer
		//	,	inp_curToken	= [c]
			}
		)
*/
ReadLine :: !Input -> (!String, !Input)
ReadLine input=:{inp_stream = OldChars cs oldfile, inp_pos}
	# input			= {input & inp_stream = oldfile, inp_pos = NextPos CRChar inp_pos 0}
	| isEmpty cs	= ReadLine input
	| otherwise		= (toString cs, input)
ReadLine input=:{inp_stream = InFile infile,inp_pos}
	# (eof, file) 	= fend infile
	| eof			= ("", {input & inp_stream = InFile file})
	# (l, file )	= freadline file
	= (l,  {input & inp_stream = InFile file, inp_pos = NextPos CRChar inp_pos 0})
ReadLine input =: {inp_stream = InLOC [a : c], inp_pos, inp_tabsize}
	| a==NewLineChar= ("\n", {input & inp_stream = InLOC c, inp_pos = inp_pos})
	# (line, input)	= ReadLine {input & inp_stream = InLOC c, inp_pos = inp_pos}
	= (toString a + line, input)
ReadLine input=:{inp_stream = OldChar c p oldfile}
	# input			= {input & inp_stream = oldfile}
	| c==NewLineChar= ("\n", input)
	# (line, input)	= ReadLine input
	= (toString c + line, input)
ReadLine input		= ("", input)

NextPos :: !Char !FilePosition !Int -> FilePosition
NextPos c pos=:{fp_line, fp_col} t
	= case c of
		LFChar	-> NextPos CRChar pos t		//	-->> "LF in Nextpos"
		CRChar	-> {fp_line = fp_line + 1, fp_col = 0}	// -->> ("line " +toString (fp_line + 1))
		'\t'	-> {pos & fp_col = t * (fp_col / t + 1)}
		_		-> {pos & fp_col = fp_col + 1}

correctNewline :: !Char !FilePosition !Int !InputStream -> (!Char, !InputStream)
correctNewline c pos tab_size (InFile file) 	// Correct newline convention: Mac: CR, Unix: LF, DOS CR LF
	=	case c of
			LFChar	-> (NewLineChar,InFile file)	//-->> "UNIX newline"
			CRChar 
				# (ok,c2,file) =  freadc file
				| ok
					| c2 == LFChar -> (NewLineChar,InFile file) // -->> "DOS newline corrected"
					               -> (NewLineChar,OldChar c2 (NextPos c2 pos tab_size) (InFile file))
					-> (NewLineChar, InFile file)
			_		-> (c, InFile file)
correctNewline c pos tab_size (OldChars [] input)
	= correctNewline c pos tab_size input
correctNewline c pos tab_size (OldChars chars input)
	=	case c of
			LFChar	-> (NewLineChar,OldChars chars input)	//-->> "UNIX newline"
			CRChar
				# [c2:rest] = chars
				| c2 == LFChar -> (NewLineChar,OldChars rest input) // -->> "DOS newline corrected"
				               -> (NewLineChar,OldChars chars input)
			_		-> (c,OldChars chars input)
correctNewline c _ _ input = (c, input)

charBack :: !Input -> Input
charBack input=:{inp_stream,inp_charBuffer}
	|	isEmptyBuffer inp_charBuffer
		=	abort "charBack with empty character buffer"
	#	((c,p),rest) = get inp_charBuffer
	=	{	input
		&	inp_stream		= OldChar c p inp_stream
		,	inp_charBuffer	= rest
		}

qw s :== "\"" + s + "\""

instance <<< Token
where
	(<<<) f t = f <<< (toString t)

instance <<< LongToken
where
	(<<<) f lt = f <<< lt.lt_token <<< " from " <<< lt.lt_position

instance <<< FilePosition
where
	(<<<) f {fp_line,fp_col} = f <<< fp_line <<< ";" <<< fp_col

instance toString Token
where
	toString (IdentToken id)		= id // qw id
	toString (IntToken id)			= id
	toString (RealToken id)			= id
	toString (StringToken id)		= id
	toString (CharToken id)			= id
	toString (CharListToken id)		= "['"+id+"']"
	toString (BoolToken id)			= toString id
	toString OpenToken				= "("
	toString CloseToken				= ")"
	toString CurlyOpenToken			= "{"
	toString CurlyCloseToken		= "}"
	toString SquareOpenToken		= "["
	toString SquareCloseToken		= "]"
	toString DotToken				= "."
	toString SemicolonToken			= ";"
	toString ColonToken				= ": (ColonToken)"
	toString DoubleColonToken		= "::"
	toString CommaToken				= ","
	toString ExclamationToken		= "!"
	toString BarToken				= "|"
	toString ArrowToken				= "->"
	toString DoubleArrowToken		= "=>"
	toString EqualToken				= "="
	toString DefinesColonToken		= "=:"
	toString ColonDefinesToken		= ":=="
	toString WildCardToken			= "_"
	toString BackSlashToken			= "\\"
	toString DoubleBackSlashToken	= "\\\\"
	toString LeftArrowToken			= "<-"
	toString LeftArrowColonToken	= "<-:"
	toString DotDotToken			= ".."
	toString AndToken				= "&"
	toString HashToken				= "#"
	toString AsteriskToken			= "*"
	toString LessThanOrEqualToken	= "<="
	toString ModuleToken			= "module"
	toString ImpModuleToken			= "implementation"
	toString DefModuleToken			= "definition"
	toString SysModuleToken			= "system"	
	toString ImportToken			= "import"
	toString FromToken				= "from"
	toString SpecialToken			= "special"
	toString IntTypeToken			= "Int"
	toString CharTypeToken			= "Char"
	toString RealTypeToken			= "Real"
	toString BoolTypeToken			= "Bool"
	toString StringTypeToken		= "String"
	toString LeftAssocToken			= "left"
	toString RightAssocToken		= "right"
	toString ClassToken				= "class"
	toString InstanceToken			= "instance"
	toString OtherwiseToken			= "otherwise"
	toString IfToken				= "if"
	toString WhereToken				= "where"
	toString WithToken				= "with"
	toString CaseToken				= "case"
	toString OfToken				= "of"
	toString (LetToken strict)
		| strict	= "let!"
					= "let"
	toString (SeqLetToken strict)
		| strict	= "#!"
					= "#"
	toString InToken					= "in"

	toString DynamicToken				= "dynamic"
	toString DynamicTypeToken			= "Dynamic"

	toString (PriorityToken priority)	= toString priority
	toString NewDefinitionToken			= "offside token (new def)"
	toString EndGroupToken				= "offside token (end group)"
	toString EndOfFileToken				= "end of file"
	toString (ErrorToken id)			= "Scanner error: " + id
	toString CodeToken					= "code"
	toString InlineToken				= "inline"
	toString (CodeBlockToken the_code)	= "<code block>"
	toString token						= "toString (Token) does not know this token"

instance == Token
where
	(==) token1 token2
		= equal_constructor token1 token2 && equal_args_of_tokens token1 token2
	where
		equal_args_of_tokens :: !Token !Token -> Bool
		equal_args_of_tokens (IdentToken id1)		(IdentToken id2)		= id1 == id2
		equal_args_of_tokens (RealToken real1) 		(RealToken real2)		= real1 == real2
		equal_args_of_tokens (StringToken string1)	(StringToken string2)	= string1 == string2
		equal_args_of_tokens (CharToken char1)		(CharToken char2)		= char1 == char2
		equal_args_of_tokens (CharListToken chars1)	(CharListToken chars2)	= chars1 == chars2
		equal_args_of_tokens (BoolToken bool1)		(BoolToken bool2)		= bool1 == bool2
		equal_args_of_tokens (IntToken int1)		(IntToken int2)			= int1 == int2
		equal_args_of_tokens (LetToken l1)			(LetToken l2)			= l1 == l2
		equal_args_of_tokens (SeqLetToken l1)		(SeqLetToken l2)		= l1 == l2
		equal_args_of_tokens (ErrorToken id1)		(ErrorToken id2)		= id1 == id2
		equal_args_of_tokens _						_						= True

instance < Priority
where
	(<) (Prio assoc1 prio1) (Prio assoc2 prio2)
		= prio1 < prio2 || prio1 == prio2 && assoc1 < assoc2
	(<) _ _ = abort "< of these Priorities (NoPrio) is undefined"
			
instance < Assoc
where
	(<) _ LeftAssoc = True
	(<) LeftAssoc _ = False
	(<) _ _ = True
			
instance toString Priority
where
	toString (Prio assoc prio) = toString assoc + toString prio
	toString NoPrio = "infix"
	
instance toString Assoc
where
	toString LeftAssoc 	= "infixl "
	toString RightAssoc = "infixr "
	toString NoAssoc	= "infix "
	

openScanner :: !String !SearchPaths !*Files -> (!Optional ScanState, !*Files)
openScanner file_name searchPaths files
	= case fopenInSearchPaths file_name searchPaths FReadData files of
		(No, files)
			->	(No, files)
		(Yes file, files)
			->  (Yes	{	ss_input 		= Input
												{ inp_stream		= InFile file
									 			, inp_filename		= file_name
									 			, inp_pos			= {fp_line = 1, fp_col = 0}
												, inp_tabsize		= 4
												, inp_charBuffer	= Buffer0
											//	, inp_curToken		= []
												}
						,	ss_offsides		=	[(1,False)] // to generate offsides between global definitions
						,	ss_useLayout	=	False
						,	ss_tokenBuffer	=	Buffer0
						}
				, files
				)

fopenInSearchPaths :: !{#Char} [!{#Char}] !Int !*f -> (Optional *File,!*f) | FileSystem f
fopenInSearchPaths fileName [] mode f
	=	(No, f)
fopenInSearchPaths fileName [path : paths] mode f
	# (opened, file, f)
		=	fopen (path + fileName) mode f
	| opened
		=	(Yes file, f)
	// otherwise
		=	fopenInSearchPaths fileName paths mode f

closeScanner :: !ScanState !*Files -> *Files
closeScanner scanState=:{ss_input=PushedToken _ input} files
	= closeScanner {scanState & ss_input = input} files 
closeScanner {ss_input=Input {inp_stream}} files
	= case get_file inp_stream of
		Yes file	#	(_,files) = fclose file files
					->	files
		No			->	files
where
	get_file (InFile file)			= Yes file
	get_file (OldChar _ _ stream)	= get_file stream
	get_file (OldChars _ stream)	= get_file stream
	get_file (OldToken _ stream)	= get_file stream
	get_file (InLOC _ )				= No

NewLineChar	:== '\n'
LFChar		:== '\xA'
CRChar		:== '\xD'

//isNewLine c :== c == LFChar || c == CRChar
isNewLine :: !Char -> Bool
isNewLine LFChar = True
isNewLine CRChar = True
isNewLine _      = False

  //------------------------//
 //--- Offside handling ---//
//------------------------//

UseLayout :: !ScanState -> (!Bool, !ScanState)
UseLayout scanState = scanState!ss_useLayout

setUseLayout :: !Bool !ScanState -> ScanState
setUseLayout b ss = { ss & ss_useLayout = b } // -->> ("uselayout set to ",b)

checkOffside :: !FilePosition !Token !ScanState -> (Token,ScanState)
checkOffside pos token scanState=:{ss_offsides,ss_useLayout,ss_input}
	| ~ ss_useLayout
		=	(token, scanState)  //-->> (token,pos,"No layout rule applied")
	| isEmpty ss_offsides
		=	newOffside token scanState  //-->> "Empty offside stack"
	#	(os_col, new_def)	= hd ss_offsides
		col					= pos.fp_col
	| col == os_col && canBeOffside token
		# scanState	= tokenBack scanState
		  newToken	= NewDefinitionToken
		= (	newToken
		  ,	{ scanState
			& ss_tokenBuffer
				= store 
					{	lt_position		= pos
					,	lt_token		= newToken
				//	,	lt_chars		= []
				//	,	lt_context		= FunctionContext
					}
					scanState.ss_tokenBuffer
			}
		  )	-->> (token,"NewDefinitionToken generated col==os && canBeOffside",pos,ss_offsides)
	| col < os_col && token <> InToken
		# (n,os_col,new_def,offsides) = scan_offsides 0 col os_col new_def ss_offsides
		  scanState	= { scanState & ss_offsides = offsides } //-->> (n,"end groups",offsides,new_def)
		  scanState	= snd (newOffside token scanState)
		  scanState	= case new_def && col == os_col && canBeOffside token of
  						True
							#	scanState	= tokenBack scanState
								newToken	= NewDefinitionToken
							->	{ scanState
								& ss_tokenBuffer
									= store 
										{	lt_position		= pos
										,	lt_token		= newToken
									//	,	lt_chars		= []
									//	,	lt_context		= FunctionContext
										}
										scanState.ss_tokenBuffer
								} -->> ("new definition generated",token)
  						False
  							->	scanState
		= gen_end_groups n scanState
		with
			newToken		= EndGroupToken
			scan_offsides n col os_col new_def []
				= (n, os_col, new_def, [])
			scan_offsides n col _ new_def offsides=:[(os_col,b):r]
				| col < os_col
					= scan_offsides (inc n) col os_col b r
					= (n, os_col, new_def, offsides)
			gen_end_groups n scanState
		  	  #	scanState	= tokenBack scanState	// push current token back
		  		scanState	=	{ scanState
								& ss_tokenBuffer
									= store 
										{	lt_position		= pos
										,	lt_token		= newToken
									//	,	lt_chars		= []
									//	,	lt_context		= FunctionContext
										}
										scanState.ss_tokenBuffer
								} -->> ("end group generated",pos) // insert EndGroupToken 
			  | n == 1
			// 	# (new_offsides, scanState) = scanState!ss_offsides // for tracing XXX
			  	= (newToken, scanState) // -->> ("new offsides",new_offsides)
			  	= gen_end_groups (dec n) scanState
	| token == InToken
		= (token, { scanState & ss_offsides = tl ss_offsides })
/*		# scanState			= tokenBack { scanState & ss_offsides = tl ss_offsides }
		  newToken			= EndGroupToken
		= ( newToken
		  , { scanState
			& ss_tokenBuffer
				= store 
					{	lt_position		= pos
					,	lt_token		= newToken
				//	,	lt_chars		= []
				//	,	lt_context		= FunctionContext
					}
					scanState.ss_tokenBuffer
			}
		  ) -->> (token,"EndGroupToken generated: in",pos,ss_offsides)
*/	// otherwise
		= newOffside token scanState
where
	newOffside token scanState=:{ss_offsides}
	| definesOffside token
		#	( _, scanState )		= nextToken FunctionContext scanState
			( os_pos, scanState )	= getPosition scanState // next token defines offside position
			scanState				= tokenBack scanState
			os						= os_pos.fp_col
		|	os == 1
			#	scanState			= tokenBack scanState
				newToken			= ErrorToken "groups should not start in column 1"
			=	( newToken
				, 	{ scanState
					& ss_tokenBuffer
						= store 
							{	lt_position		= pos
							,	lt_token		= newToken
						//	,	lt_chars		= ['groups should not start in column 1']
						//	,	lt_context		= FunctionContext
							}
							scanState.ss_tokenBuffer
					}
				)
		// otherwise // os <> 1
			=	( token
				, { scanState
				  & ss_offsides = [ (os, needsNewDefinitionToken token) : ss_offsides ]
				  }
				) -->> (token,pos,"New offside defined at ",os_pos,[ (os, token == CaseToken) : ss_offsides ])
	// otherwise // ~ (definesOffside token)
	= (token, scanState) -->> (token,pos," not offside")

definesOffside :: !Token -> Bool
definesOffside (LetToken _) 	= True
definesOffside (SeqLetToken _)	= True
definesOffside WhereToken		= True
definesOffside WithToken		= True
definesOffside SpecialToken		= True
definesOffside OfToken			= True
//definesOffside BarToken			= True // There are too many BarTokens in Clean
definesOffside _				= False

needsNewDefinitionToken :: !Token -> Bool
needsNewDefinitionToken OfToken			= True
//needsNewDefinitionToken WithToken		= True
needsNewDefinitionToken SpecialToken	= True
needsNewDefinitionToken _				= False
/*
repeatedOffside :: !Token -> Bool
repeatedOffside BarToken		= True
repeatedOffside EqualToken		= True
repeatedOffside (SeqLetToken _)	= True
repeatedOffside _				= False
*/
canBeOffside :: !Token -> Bool
canBeOffside EqualToken			= False
canBeOffside ColonDefinesToken	= False
canBeOffside DefinesColonToken	= False
canBeOffside (SeqLetToken _)	= False
canBeOffside WhereToken			= False
canBeOffside SpecialToken		= False
canBeOffside WithToken			= False
canBeOffside BarToken			= False
//canBeOffside CurlyOpenToken		= False // not allowed for record patterns
canBeOffside (CodeBlockToken _) = False
canBeOffside _					= True

dropOffsidePosition :: !ScanState -> ScanState
dropOffsidePosition scanState=:{ss_offsides} = { scanState & ss_offsides = drop 1 ss_offsides }

/*
addOffsidePosition :: !ScanState -> (Int, ScanState)
addOffsidePosition scanState=:{ss_useLayout}
	| ss_useLayout
		# (position,scanState=:{ss_offsides})	= getPosition scanState
		  new_offside							= position.fp_col
		= (new_offside, { scanState & ss_offsides = [(new_offside,False): ss_offsides] })
	| otherwise
		= (1, scanState)

atOffsidePosition :: !ScanState -> (!Bool, !ScanState)
atOffsidePosition scanState=:{ss_offsides=[(col,_):_]}
	#	(position, scanState)	= getPosition scanState
	=	(position.fp_col == col, scanState) -->> ("atOffsidePosition",position.fp_col,col)
atOffsidePosition scanState
	=	(False, scanState)
*/
  //-----------------------//
 //--- Buffer handling ---//
//-----------------------//

store :: !x !(Buffer x) -> Buffer x
store x  Buffer0        = Buffer1 x
store x (Buffer1 y)     = Buffer2 x y
store x (Buffer2 y z)   = Buffer3 x y z
store x (Buffer3 y z _) = Buffer3 x y z

isEmptyBuffer :: !(Buffer x) -> Bool
isEmptyBuffer Buffer0 = True
isEmptyBuffer _       = False

get :: !(Buffer x) -> (x,Buffer x)
get  Buffer0        = abort "get from empty buffer"
get (Buffer1 x)     = (x, Buffer0)
get (Buffer2 x y)   = (x, Buffer1 y)
get (Buffer3 x y z) = (x, Buffer2 y z)

head :: !(Buffer x) -> x
head  Buffer0			= abort "head of empty buffer"
head (Buffer1 x)		= x
head (Buffer2 x _)		= x
head (Buffer3 x _ _)	= x

instance <<< (Buffer a) | <<< a
where
	(<<<) file  Buffer0			= file <<< "Empty buffer"
	(<<<) file (Buffer1 x)		= file <<< "Buffer1 (" <<< x <<< ")"
	(<<<) file (Buffer2 x y)	= file <<< "Buffer2 (" <<< x <<< ") (" <<< y <<< ")"
	(<<<) file (Buffer3 x y z)	= file <<< "Buffer3 (" <<< x <<< ") (" <<< y <<< ") (" <<< z <<< ")"

  //---------------//
 //--- Tracing ---//
//---------------//

(-->>) val _ :== val
//(-->>) val message :== val ---> ("Scanner",message)
