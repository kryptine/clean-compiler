/*
	Version 1.0 26/08/1994

	Author:  Sjaak Smetsers
*/

#pragma segment checktypedefs

#define COMPLEX_ABSTYPES

#include "compiledefines.h"
#include "types.t"
#include "syntaxtr.t"
#include "comsupport.h"
#include "scanner.h"
#include "comparser.h"
#include "buildtree.h"
#include "statesgen.h"
#include "settings.h"
#include "sizes.h"

#include "checker.h"
#include "checksupport.h"
#include "checktypedefs.h"
#include "overloading.h"
#include "typechecker.h"

TypeArgClass GeneralTypeClass,FunTypeClass;
