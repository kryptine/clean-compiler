system module _aconcat

import _SystemArray,StdInt,StdEnum,StdList

arrayConcat a1 a2
	:==r2
where
	r2={r1 & [i+s1]=a2.[i] \\ i<-[0..s2-1]}
	r1={r0 & [i]=a1.[i] \\ i<-[0..s1-1]}
	r0=_createArrayc (s1+s2)
	s1=size a1
	s2=size a2

arrayPlusList a l
	:==r2
where
	r2={r1 & [i+s1]=e \\ i<-[0..s2-1] & e<-l}
	r1={r0 & [i]=a.[i] \\ i<-[0..s1-1]}
	r0=_createArrayc (s1+s2)
	s1=size a
	s2=length l


arrayPlusRevList a l
	:==r2
where
	r2={r1 & [sr-i]=e \\ i<-[1..s2] & e<-l}
	r1={r0 & [i]=a.[i] \\ i<-[0..s1-1]}
	r0=_createArrayc sr
	sr=s1+s2
	s2=length l
	s1=size a

