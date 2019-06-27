
#ifndef _COMSUPPORT_
#define _COMSUPPORT_

#ifndef _THE__TYPES_
#include "types.t"
#endif

#ifndef _SYSTEM_
#include "system.h"
#endif

#define   NoError 	0
#define   ErrKind1 	1
#define   ErrKind2	2

#define MINIMUM(a,b)	(((a)<(b)) ? (a) : (b))
#define MAXIMUM(a,b)	(((a)>(b)) ? (a) : (b))

extern void StaticMessage (Bool error, char *symbol_format, char *message_format, ...);

struct symbol;
extern void PrintSymbol (struct symbol *symbol,File file);

extern Bool  CompilerError;
extern char *CurrentModule, *CurrentExt, *CurrentPhase, *CompilerVersion;

extern struct symbol *CurrentSymbol;

extern unsigned CurrentLine;

extern int ExitEnv_valid;
extern File OpenedFile;

extern jmp_buf ExitEnv;

#endif

#define CompAllocType(t) ((t*)CompAlloc (SizeOf (t)))
#define CompAllocArray(s,t) ((t*)CompAlloc ((s)*SizeOf (t)))
extern void *CompAlloc (SizeT size);
extern void InitStorage (void);
extern void CompFree (void);

extern Bool ArgParser (int argc, char *argv[]);
extern void FatalCompError (char *mod, char *proc, char *mess);

extern void InitSettings (void);
extern void ExitOnInterrupt (void);
extern void InitCompiler (void);
extern void ExitCompiler (void);

#ifdef _DEBUG_
extern void ErrorInCompiler (char *mod, char *proc, char *msg);
extern void Assume (Bool cond, char *mod, char *proc);
extern void AssumeError (char *mod, char *proc);
#define ifnot(cond) if(!(cond))
#endif
