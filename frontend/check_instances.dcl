definition module check_instances

from syntax import
	::Global,::Index,
	::CommonDefs,::CommonDefsR,::DclInstanceMemberTypeAndFunction,
	::TypeVarHeap,::Heap,::TypeVarInfo
from overloading import ::ClassInstanceInfo,::InstanceTree(..)
from checksupport import ::ErrorAdmin

check_if_class_instances_overlap :: !*ClassInstanceInfo !{#CommonDefs} !*TypeVarHeap !*ErrorAdmin -> (!*ClassInstanceInfo,!*TypeVarHeap,!*ErrorAdmin)
