system module _aconcat

import StdArray,StdInt,StdEnum,StdList

arrayConcat a1 a2
	:==r2
where
	r2={r1 & [i+s1]=a2.[i] \\ i<-[0..s2-1]}
	r1={r0 & [i]=a1.[i] \\ i<-[0..s1-1]}
/*2.0
	r0=_createArray (s1+s2)
0.2*/
//1.3
	r0=_createArrayc (s1+s2)
//3.1
	s1=size a1
	s2=size a2

arrayPlusList a l
	:==r2
where
	r2={r1 & [i+s1]=e \\ i<-[0..s2-1] & e<-l}
	r1={r0 & [i]=a.[i] \\ i<-[0..s1-1]}
/*2.0
	r0=_createArray (s1+s2)
0.2*/
//1.3
	r0=_createArrayc (s1+s2)
//3.1
	s1=size a
	s2=length l

arrayPlusRevList a l
	:==r2
where
	r2={r1 & [sr-i]=e \\ i<-[1..s2] & e<-l}
	r1={r0 & [i]=a.[i] \\ i<-[0..s1-1]}
/*2.0
	r0=_createArray sr	// 2.0
0.2*/
//1.3
	r0=_createArrayc sr
//3.1
	sr=s1+s2
	s1=size a
	s2=length l

arrayCopyBegin a s
	:== copy_elements a r0 0
where
/*2.0
	r0=_createArray s
0.2*/
//1.3
	r0=_createArrayc s
//3.1
	copy_elements a1 a2 i
		| i<size a2
			# (e,a1) = a1![i]
			= copy_elements a1 {a2 & [i]=e} (i+1)
			= (a2,a1)
