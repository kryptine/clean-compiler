implementation module cheat

i :: !a -> b
i x =
	code
	{	.inline i
			no_op
		.end
	}

uniqueCopy :: !*a -> (!*a, !*a)
uniqueCopy x =
	code
	{	.inline uniqueCopy
			push_a 0
		.end
	}
