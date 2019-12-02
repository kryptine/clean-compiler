
#ifndef _COMSUPPORT_
#define _COMSUPPORT_

#ifndef _THE__TYPES_
#include "types.t"
#endif

#ifndef _SYSTEM_
#include "system.h"
#endif

#define MINIMUM(a,b)	(((a)<(b)) ? (a) : (b))
#define MAXIMUM(a,b)	(((a)>(b)) ? (a) : (b))

extern void StaticMessage_D_s (Bool error,struct symbol_def *symb_def_p,char *message);
extern void StaticMessage_S_Ss (Bool error,struct symbol *symbol_p1,struct symbol *symbol_p2,char *message);
extern void StaticMessage_S_s (Bool error,struct symbol *symbol_p,char *message);
extern void StaticMessage_s_s (Bool error,char *symbol_s,char *message);
extern void StaticErrorMessage_S_ss (struct symbol *symbol_p,char *message1,char *message2);
extern void StaticErrorMessage_s_Ss (char *symbol_s,struct symbol *symbol_p,char *message);
extern void StaticErrorMessage_s_ss (char *symbol_s,char *message1,char *message2);

struct symbol;
extern void PrintSymbol (struct symbol *symbol,File file);

extern Bool  CompilerError;
extern char *CurrentModule, *CompilerVersion;

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

extern void int_to_string (char *s,long i);

extern void FatalCompError (char *mod, char *proc, char *mess);

extern void InitSettings (void);
extern void InitCompiler (void);
extern void ExitCompiler (void);

#ifdef _DEBUG_
extern void ErrorInCompiler (char *mod, char *proc, char *msg);
extern void Assume (Bool cond, char *mod, char *proc);
extern void AssumeError (char *mod, char *proc);
#define ifnot(cond) if(!(cond))
#endif
