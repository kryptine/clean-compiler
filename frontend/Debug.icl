implementation module Debug

import StdArray, StdEnum
from StdFile	import <<<, ferror, stderr
from StdMisc	import abort
from StdTuple	import fst
from StdList	import ++
from StdBool	import && 
from StdString	import %

import	Wrap, ShowWrapped

print :: ![{#Char}] .b -> .b
print debugStrings value
	| fst (ferror (stderr <<< debugStrings))
		=	abort "Debug, print: couldn't write to stderr"
	// otherwise
		=	value

debugBefore :: !.a !(DebugShowFunction .a) .b -> .b
debugBefore debugValue show value
	=	print (show debugValue) value

debugAfter :: !.a !(DebugShowFunction .a) !.b -> .b
debugAfter debugValue show value
	=	print (show debugValue) value

debugValue :: !(DebugShowFunction .a) !.a -> .a
debugValue show value
	=	print (show copy1) copy2
	where
		(copy1, copy2)
			=	copyUniqueValue value

		copyUniqueValue :: !.a -> (!.a, !.a)
		copyUniqueValue value
			=	code {
				.o 1 0
					push_a	0				
				.d 2 0
				}

:: DebugShowFunction a :== !a -> [{#Char}]

debugShow :: DebugShowFunction .a
debugShow
	=	\debugValue -> showWrapped (wrapNode debugValue) ++ ["\n"]


:: DebugOptionRecord
	=	{maxDepth :: !Int, maxBreadth :: !Int, maxChars :: !Int, terminator :: !{#Char}}
DebugDefaultOptions
	:== {maxDepth = MaxInt, maxBreadth = MaxInt, maxChars = MaxInt, terminator = "\n"}

MaxInt
	:== (1<<31)-1

:: DebugShowOption 
	=	DebugMaxDepth !Int			// default MaxInt
	|	DebugMaxBreadth !Int		// default MaxInt
	|	DebugMaxChars !Int			// default MaxInt
	|	DebugTerminator !{#Char}	// default "\n"

debugShowWithOptions :: [DebugShowOption] -> DebugShowFunction .a
debugShowWithOptions debugOptions 
	=	\debug -> chop maxChars (showWrapped (pruneWrappedNode maxDepth maxBreadth (wrapNode debug))) ++ [terminator]
	where
		{maxDepth, maxBreadth, maxChars, terminator}
			=	set debugOptions DebugDefaultOptions
			where
				set [] options
					=	options
				set [DebugMaxDepth maxDepth:t] options
					=	set t {options & maxDepth=maxDepth}
				set [DebugMaxBreadth maxBreadth:t] options
					=	set t {options & maxBreadth=maxBreadth}
				set [DebugMaxChars maxChars:t] options
					=	set t {options & maxChars=maxChars}
				set [DebugTerminator terminator:t] options
					=	set t {options & terminator=terminator}

:: Indicators
	=	...
	|	.+.

MaxCharsString
	:== ".."
MaxBreadthString
	:== "..."
MaxBreadthIndicator
	:==	wrapNode ...
MaxDepthIndicator
	:==	wrapNode .+.

pruneWrappedNode :: !Int !Int !WrappedNode -> !WrappedNode
pruneWrappedNode maxDepth maxBreadth value
	=	prune 0 value
	where
		prune :: !Int WrappedNode -> WrappedNode
		prune depth value
			| depth == maxDepth
				=	MaxDepthIndicator
		prune depth (WrappedIntArray a)
			=	pruneBasicArray depth a
		prune depth (WrappedBoolArray a)
			=	pruneBasicArray depth a
		prune depth (WrappedRealArray a)
			=	pruneBasicArray depth a
		prune depth (WrappedFileArray a)
			=	pruneBasicArray depth a
		prune depth (WrappedString a)
			| size a > maxBreadth
				=	WrappedString ((a % (0, maxBreadth-1)) +++ MaxBreadthString)
		prune depth (WrappedArray a)
			=	WrappedArray (pruneArray depth a)
		prune depth (WrappedRecord descriptor args)
			=	WrappedRecord descriptor (pruneArray depth args)
		prune depth (WrappedOther WrappedDescriptorCons args)
			| size args == 2
				=	WrappedOther WrappedDescriptorCons
						{prune (depth+1) args.[0], prune depth args.[1]}
		prune depth (WrappedOther WrappedDescriptorTuple args)
			=	WrappedOther WrappedDescriptorTuple (pruneArray depth args)
		prune depth (WrappedOther descriptor args)
			=	WrappedOther descriptor (pruneArray depth args)
		prune _ a
			=	a

		pruneArray :: !Int !{WrappedNode} -> {WrappedNode}
		pruneArray depth a
			| size a > maxBreadth
				=	{{prune (depth+1) e \\ e <-: a & i <- [0 .. maxBreadth]}
						& [maxBreadth] = MaxBreadthIndicator}
			// otherwise
				=	{prune (depth+1) e \\ e <-: a}

		pruneBasicArray :: !Int !(a b) -> WrappedNode | Array .a & ArrayElem b
		pruneBasicArray depth a
			| size a > maxBreadth
				=	WrappedArray (pruneArray depth {wrapNode e \\ e <-: a & i <- [0 .. maxBreadth]})
			// otherwise
				=	WrappedArray {wrapNode e \\ e <-: a}

chop :: !Int ![{#Char}] -> [{#Char}]
chop _ []
	=	[]
chop maxSize list=:[string:strings]
	| maxSize < stringSize + sizeMaxCharsString
		| fits maxSize list
			=	list
		| stringSize > sizeMaxCharsString
			=	[string % (0, maxSize-sizeMaxCharsString-1), MaxCharsString]
		// otherwise
			=	[MaxCharsString]
	// otherwise
		=	[string : chop (maxSize - stringSize) strings]
	where
		fits _ []
			=	True
		fits maxSize [h : t]
			=	maxSize >= size h && fits (maxSize - size h) t

		stringSize
			=	size string
		sizeMaxCharsString
			=	size MaxCharsString

instance <<< [a] | <<< a where
	(<<<) :: *File [a] -> *File | <<< a
	(<<<) file []
		=	file
	(<<<) file [h:t]
		=	file <<< h <<< t
