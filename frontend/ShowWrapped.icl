implementation module ShowWrapped

import StdEnv
import Wrap

ShowWrapped :: WrappedNode -> [{#Char}]
ShowWrapped node
	=	Show False node

Show _ (WrappedInt i)
	=	[toString i]
Show _ (WrappedChar c)
	=	["\'" +++ toString c +++ "\'"]
Show _ (WrappedBool b)
	=	[toString b]
Show _ (WrappedReal r)
	=	[toString r]
Show _ (WrappedFile f)
	=	[toString f]
Show _ (WrappedString s)
	=	["\"" +++ s +++ "\""]
Show _ (WrappedIntArray a)
	=	ShowBasicArray a
Show _ (WrappedBoolArray a)
	=	ShowBasicArray a
Show _ (WrappedRealArray a)
	=	ShowBasicArray a
Show _ (WrappedFileArray a)
	=	ShowBasicArray a
Show _ (WrappedArray a)
	=	["{" : flatten (Separate [", "] [Show False el \\ el <-: a])] ++ ["}"]
Show _ (WrappedRecord descriptor args)
	=	["{" : flatten (Separate [" "] [[ShowDescriptor descriptor] : [Show True arg \\ arg <-: args]])] ++ ["}"]
Show _ (WrappedOther WrappedDescriptorCons args)
	| size args == 2
	=	["[" : flatten [Show False args.[0] : ShowTail args.[1]]] ++ ["]"]
	where
		ShowTail (WrappedOther WrappedDescriptorCons args)
			| size args == 2
				=	[[", "], Show False args.[0] : ShowTail args.[1]]
		ShowTail (WrappedOther WrappedDescriptorNil args)
			| size args == 0
				=	[]
		ShowTail graph // abnormal list
			=	[[" : " : Show False graph]]
Show _ (WrappedOther WrappedDescriptorTuple args)
	=	["(" : flatten (Separate [", "] [Show False arg \\ arg <-: args])] ++ [")"]
Show pars (WrappedOther descriptor args)
	| pars && size args > 0
		=	["(" : application] ++ [")"]
	// otherwise
		=	application
	where
		application
			=	flatten (Separate [" "] [[ShowDescriptor descriptor] : [Show True arg \\ arg <-: args]])

ShowDescriptor (WrappedDescriptorOther id)
	=	toString id
ShowDescriptor WrappedDescriptorNil
	=	"[]"
ShowDescriptor WrappedDescriptorCons
	=	"[:]"
ShowDescriptor WrappedDescriptorTuple
	=	"(..)"

ShowBasicArray a
	=	["{" : Separate ", " [toString el \\ el <-: a]] ++ ["}"]
ShowWrappedArray a
	=	["{" : flatten (Separate [", "] [Show False el \\ el <-: a])] ++ ["}"]

Separate :: a [a] -> [a]
Separate separator [a : t=:[b : _]]
	=	[a, separator : Separate separator t]
Separate _ l
	=	l

instance toString File
where
	toString _
		=	"File"
