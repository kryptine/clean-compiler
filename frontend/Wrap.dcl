/*
	Wrap Clean nodes (for debugging purposes).

	Version 1.0.1
	Ronny Wichers Schreur
	ronny@cs.kun.nl
*/
definition module Wrap

from StdOverloaded import toString 

::	WrappedDescriptorId

instance toString WrappedDescriptorId

::	WrappedDescriptor
    =   WrappedDescriptorCons
    |   WrappedDescriptorNil
    |   WrappedDescriptorTuple
    |   WrappedDescriptorOther !WrappedDescriptorId

::  WrappedNode
	//	basic types
    =   WrappedInt !Int
    |   WrappedChar !Char
    |   WrappedBool !Bool
    |   WrappedReal !Real
    |   WrappedFile !File

	// unboxed arrays of basic types
    |   WrappedString !{#Char}
    |   WrappedIntArray !{#Int}
    |   WrappedBoolArray !{#Bool}
    |   WrappedRealArray !{#Real}
    |   WrappedFileArray !{#File}

	// other arrays
    |   WrappedArray !{WrappedNode}

	// records
    |   WrappedRecord !WrappedDescriptor !{WrappedNode}

	// other nodes
    |   WrappedOther !WrappedDescriptor !{WrappedNode}

wrapNode :: !.a -> WrappedNode