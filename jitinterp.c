/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*      Basile Starynkevitch, projet Cristal, INRIA Rocquencourt       */
/*                                                                     */
/*  Copyright 2004 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file LICENSE of      */
/*  the Ocaml source tree.                                             */
/*                                                                     */
/***********************************************************************/


/***
   cvs $Id: jitinterp.c,v 1.52 2004-10-10 20:30:52 basile Exp $
***/

/* a bytecode just-in-time translator (to plain machine code), using
   the GNU lightning library */

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <time.h>
#include <errno.h>
#include <lightning.h>


#include "alloc.h"
#include "backtrace.h"
#include "callback.h"
#include "debugger.h"
#include "fail.h"
#include "md5.h"
#include "fix_code.h"
#include "instrtrace.h"
#include "instruct.h"
#include "interp.h"
#include "stacks.h"
#include "prims.h"
#include "signals.h"

#ifdef ARCH_SIXTYFOUR
#define LOG2WORDSIZE 3		/*log2 of word size in bytes */
#define WORDSIZE 8
#else
#define LOG2WORDSIZE 2
#define WORDSIZE 4
#endif

#ifdef DEBUG
#include <sys/times.h>
#include <signal.h>

#ifndef NO_PTRACE
/* some systems don't have <sys/ptrace.h> or the ptrace system call -
   on these (like Solaris2.9) compile with -DNO_PTRACE */
#include <sys/ptrace.h>
#endif /*NO_PTRACE */

#endif /*DEBUG*/
#ifdef __STDC__
const char caml_jitinterp_ident[] =
  "$Id: jitinterp.c,v 1.52 2004-10-10 20:30:52 basile Exp $"
  " on " __DATE__ " at " __TIME__;
#endif

/* some systems, such as MacOSX only have MAP_ANON */

#if defined(MAP_ANON) && !defined(MAP_ANONYMOUS)
#define MAP_ANONYMOUS MAP_ANON
#endif

#ifndef NO_PTRACE
/* some systems, like MacOSX, have PT_TRACE_ME for PTRACE_TRACEME */
#if defined(PT_TRACE_ME) && !defined(PTRACE_TRACEME)
#define PTRACE_TRACEME PT_TRACE_ME
#endif
#endif /*NO_PTRACE */

#if !defined(MAP_ANONYMOUS) || !defined(PROT_EXEC)
#error jitinterp.c requires a mmap syscall providing MAP_ANONYMOUS and PROT_EXEC
#endif

#ifndef  JIT_R_NUM
#error too old version of GNU lightning - please upgrade it (see comment)
// you might use the CVS snapshort (or any release newer than 9th july
// 2004) of GNU lightning on savannah.gnu.org
#endif

/* Registers for the abstract machine:
        pc         the code pointer
        sp         the stack pointer (grows downward)
        accu       the accumulator
        env        heap-allocated environment
        caml_trapsp     pointer to the current trap frame
        extra_args number of extra arguments provided by the caller
        

sp is a local copy of the global variable caml_extern_sp. */


/****
     mapping from bytecode PC to jit-machine-code PC a global pointer
     [caml_jit_pc_tblptr] points to an big hashed array; this array has a
     size which is a power of two, ie 2 ** [caml_jit_pc_logsz] each
     element in this array is a non-null pointer to a bucket, i.e. an
     array of structures (bytepc, machinepc) which is null terminated
     the common (optimised) case is a 2-array with one entry followed
     by null. Unused buckets are pointers to a common empty bucket.
 ****/

/* a bucket is an array of such entries, the last entry being zeroed */
struct caml_jit_pc_entry_st {
  code_t jml_bytepc;
  void *jml_machinepc;
};

#define JML_EMPTYPC   ((code_t)(-1))
int caml_jit_nb_entries;	/* total number of entries */
int caml_jit_pc_logsz;		/* log2 of size of both tables below */
unsigned caml_jit_pc_mask;	/* always 1<<caml_jit_pc_logsz -1 */
struct caml_jit_pc_entry_st **caml_jit_pc_tblptr;	/* hashed array of buckets */
int *caml_jit_pc_tblsiz;	/** hashed array of bucket allocated sizes */

/* we declare fields volatile so that they are more setjmp friendly */
struct caml_jit_state_st {
  volatile value js_accu;
  volatile value js_env;
  volatile long js_extra_args;
  volatile code_t js_bytepc;
  volatile long js_wosize;
  volatile long js_tag;
  volatile value *js_modifdest;
  volatile value js_modifval;
  volatile code_t js_savedbytepc;
  double js_dblx;
  double js_dbly;
  volatile value js_temp1;
  volatile value js_temp2;
  volatile void *js_spare1;
  volatile void *js_spare2;
  volatile void *js_spare3;
};

#define JML_OFF_ACCU         offsetof(struct caml_jit_state_st, js_accu)
#define JML_OFF_ENV          offsetof(struct caml_jit_state_st, js_env)
#define JML_OFF_EXTRA_ARGS   offsetof(struct caml_jit_state_st, js_extra_args)
#define JML_OFF_BYTEPC       offsetof(struct caml_jit_state_st, js_bytepc)
#define JML_OFF_WOSIZE       offsetof(struct caml_jit_state_st, js_wosize)
#define JML_OFF_TAG          offsetof(struct caml_jit_state_st, js_tag)
#define JML_OFF_MODIFDEST    offsetof(struct caml_jit_state_st, js_modifdest)
#define JML_OFF_MODIFVAL     offsetof(struct caml_jit_state_st, js_modifval)
#define JML_OFF_SAVEDBYTEPC  offsetof(struct caml_jit_state_st, js_savedbytepc)
#define JML_OFF_TEMP1        offsetof(struct caml_jit_state_st, js_temp1)
#define JML_OFF_TEMP2        offsetof(struct caml_jit_state_st, js_temp2)
#define JML_OFF_DBLX         offsetof(struct caml_jit_state_st, js_dblx)
#define JML_OFF_DBLY         offsetof(struct caml_jit_state_st, js_dbly)

volatile struct caml_jit_state_st *caml_jitstate;

static const struct caml_jit_pc_entry_st caml_jit_empty_bucket = { 0, 0 };


#define JIT_CODBL_MAGIC 0x5e61a7f
#define JIT_CHUNK_MAGIC 0x2a34981
struct caml_jit_codeblock_st {	/* malloced structure */
  unsigned cb_magic;		/* always JIT_CODBL_MAGIC */
  jit_insn *cb_jumppcref;	/* reference to label to jump to bytepc */
  code_t cb_byprog;		/* bytecode, actually "word"code */
  int cb_bysize;		/* length of bytecode IN BYTES (not in bytecode) */
  unsigned long cb_bycheck;	/* checksum of bytecode */
  int cb_rank;			/* unique rank */
  struct caml_jit_codechunk_st *cb_firstchunk;	/* first chunk in block */
  struct caml_jit_codechunk_st *cb_lastchunk;	/* last chunk in block */
  void *cb_start;		/* entry point (to call) = first instr of prologue */
  jit_insn *cb_curinstr;	/* current native machine intruction */
  struct jml_forward_st *cb_forwards;	/* forward reference array */
  int cb_tbidx;			/* index in caml_jit_codtable */
};


/* we usually have only one codeblock - the code block of the initial
   bytecode; however, there are pathological cases where we could have
   many hundreds of codeblocks: deeply recursive C callbacks;
   long-lived toplevel; so we keep an hashcode table of code blocks */
struct caml_jit_codbtable_st {
  int ct_size;			/* allocated size */
  int ct_nbblock;		/* number of blocks */
  struct caml_jit_codeblock_st *ct_tab[0];	/* actual array of ct_size length */
};
static volatile struct caml_jit_codbtable_st *caml_jit_codtable;

/* to accelerate finding a codeblock by a bytecode inside it, we maintain a small cache */
#define JML_CBLOCKCACHELEN 8
static volatile struct caml_jit_codeblock_st
 *caml_jit_cachecb[JML_CBLOCKCACHELEN];


#define JML_EMPTYBLOCKSLOT  (struct caml_jit_codeblock_st*)1

struct caml_jit_codechunk_st {	/* mmapped structure (in an executable segment) */
  unsigned ch_magic;		/* always JIT_CHUNK_MAGIC */
  struct caml_jit_codeblock_st *ch_cblock;	/* owning block */
  struct caml_jit_codechunk_st *ch_prev;	/* previous chunk */
  struct caml_jit_codechunk_st *ch_next;	/* next chunk */
  void *ch_end;			/* end of this chunk */
  jit_insn ch_instrzone[0];	/* instruction zone */
};

struct {
  int jitopt_bycod_chunk_size;
#ifdef DEBUG
  int jitopt_count_flag;
  FILE *jitopt_to_debugger_file;
  FILE *jitopt_from_debugger_file;
  int jitopt_measure_time;
#endif
} caml_jit_options;

/* bytecode are compiled in chunks - the minimal chunk size (in bytecode) is */
#define MIN_BYCOD_CHUNK_SIZE 500
#define DEFAULT_BYCOD_CHUNK_SIZE 2000


/* estimate of number of machine instructions in bytes per bytecode -
   on x86 it is about 6.5, rounded up to 10 for less dense instruction
   set architectures */
#ifdef DEBUG
#define JIT_NATIVEBYTE_PER_BYTECODE  (caml_jit_options.jitopt_count_flag?32:15)
#else
#define JIT_NATIVEBYTE_PER_BYTECODE 10
#endif


// the generated routine takes a state vector and return an integer state number
enum jitstate_st {
  MLJSTATE_NONE = 0,
  MLJSTATE_RETURN,		/*normal return */
  MLJSTATE_MODIF,		/*modify a pointer */
  MLJSTATE_ABEND,		/*abnormal end of code */
  MLJSTATE_PROCESS_SIGNAL,	/*process pending signal */
  MLJSTATE_RAISE,		/*raise exception */
  MLJSTATE_JITRANSLATE,		/*jit translation required */
  MLJSTATE_GRAB,		/*execute GRAB */
  MLJSTATE_MAKEBIGBLOCK,	/*make a big block */
  MLJSTATE_MAKEBIGFLOATB,	/*make a big float block */
};



#ifdef DEBUG
char caml_jit_disname[256];
long caml_jit_inscounter;
code_t caml_jit_bytepc;
double caml_jit_gentime;
long long caml_jit_nbgen;

const int caml_jit_1234567[] = { 0x1234567 };

extern char *caml_instr_string (code_t pc);
#define JML_DBGPRINTF(Fmt,...) do {if(caml_trace_flag) \
  fprintf(stderr,"%s:%d:" Fmt "\n", \
  __FILE__, __LINE__, ##__VA_ARGS__);} while(0)

#define JML_TODEBUGGER_PRINTF(Fmt,...) do {			\
 if(caml_jit_options.jitopt_to_debugger_file)			\
 {fprintf(caml_jit_options.jitopt_to_debugger_file, Fmt "\n",	\
 ##__VA_ARGS__);						\
 fflush(caml_jit_options.jitopt_to_debugger_file);}} while(0)

#else
#define JML_DBGPRINTF(Fmt,...) do {}while(0)
#define JML_TODEBUGGER_PRINTF(Fmt,...) do {}while(0)
#endif

static unsigned long caml_jit_code_checksum (code_t prog, int progsize);

static void
caml_jit_register_code_block (struct caml_jit_codeblock_st *cblock)
{
  int h = 0, i = 0;
  JML_DBGPRINTF ("register code block %p (prog %p size %d chksum %#x",
		 cblock, cblock->cb_byprog, (int) cblock->cb_bysize,
		 (int) cblock->cb_bycheck);
  if (!caml_jit_codtable) {
    int sz = 13;
    caml_jit_codtable = calloc (1, sizeof (struct caml_jit_codbtable_st)
				+ sz * sizeof (void *));
    if (!caml_jit_codtable)
      caml_fatal_error_arg
	("camljitrun cannot allocate code table of %d elements", (char *) sz);
    caml_jit_codtable->ct_size = sz;
  } else if (caml_jit_codtable->ct_nbblock + 4 >=
	     3 * caml_jit_codtable->ct_size / 4) {
    volatile struct caml_jit_codbtable_st *oldcodtable = caml_jit_codtable;
    int oldsz = caml_jit_codtable->ct_size;
    int sz = (oldsz <= 13) ? 37 : (oldsz <= 41) ? 97 : (oldsz <= 97) ? 211
      : (oldsz <= 211) ? 467 : (oldsz <= 467) ? 1033
      : (oldsz <= 1033) ? 2593 : (oldsz <= 2593) ? 6053
      : ((9 * oldsz) / 4 + 500) | 0xff;
    caml_jit_codtable = calloc (1, sizeof (struct caml_jit_codbtable_st)
				+ sz * sizeof (void *));
    if (!caml_jit_codtable)
      caml_fatal_error_arg
	("camljitrun cannot grow code table to %d elements", (char *) sz);
    caml_jit_codtable->ct_size = sz;
    for (i = 0; i < oldsz; i++) {
      struct caml_jit_codeblock_st *oldbl = oldcodtable->ct_tab[i];
      if (!oldbl || oldbl == JML_EMPTYBLOCKSLOT)
	continue;
      Assert (oldbl->cb_magic == JIT_CODBL_MAGIC);
      Assert (oldbl->cb_tbidx == i);
      oldbl->cb_tbidx = -1;
      caml_jit_register_code_block (oldbl);
      oldcodtable->ct_tab[i] = 0;
    };
    oldcodtable->ct_size = 0;
    free ((void *) oldcodtable);
  }
  Assert (caml_jit_codtable && caml_jit_codtable->ct_size > 2);
  h = (cblock->cb_bycheck & 0xfffffff) % (caml_jit_codtable->ct_size);
  for (i = h; i < caml_jit_codtable->ct_size; i++) {
    if (!caml_jit_codtable->ct_tab[i]
	|| caml_jit_codtable->ct_tab[i] == JML_EMPTYBLOCKSLOT) {
      caml_jit_codtable->ct_tab[i] = cblock;
      caml_jit_codtable->ct_nbblock++;
      cblock->cb_tbidx = i;
      JML_DBGPRINTF ("registered codeblock %p idx %d", cblock, i);
      return;
    }
  }
  for (i = 0; i < h; i++) {
    if (!caml_jit_codtable->ct_tab[i]
	|| caml_jit_codtable->ct_tab[i] == JML_EMPTYBLOCKSLOT) {
      caml_jit_codtable->ct_tab[i] = cblock;
      caml_jit_codtable->ct_nbblock++;
      cblock->cb_tbidx = i;
      JML_DBGPRINTF ("registered codeblock %p idx %d", cblock, i);
      return;
    }
  }
  /* should never happen that we get here */
  caml_fatal_error ("camljitrun corrupted table of code blocks");
}				/* end of caml_jit_register_code_block */

static void
caml_jit_unregister_code_block (struct caml_jit_codeblock_st *cblock)
{
  int i = 0;
  Assert (caml_jit_codtable);
  Assert (cblock && cblock->cb_magic == JIT_CODBL_MAGIC);
  JML_DBGPRINTF ("unregister code block %p (prog %p size %d chksum %#x ix%d",
		 cblock, cblock->cb_byprog, (int) cblock->cb_bysize,
		 (int) cblock->cb_bycheck, cblock->cb_tbidx);
  Assert (cblock->cb_tbidx >= 0
	  && cblock->cb_tbidx < caml_jit_codtable->ct_size);
  Assert (caml_jit_codtable->ct_tab[cblock->cb_tbidx] == cblock);
  for (i = 0; i < JML_CBLOCKCACHELEN; i++)
    if (caml_jit_cachecb[i] == cblock)
      caml_jit_cachecb[i] = 0;
  caml_jit_codtable->ct_tab[cblock->cb_tbidx] = JML_EMPTYBLOCKSLOT;
  cblock->cb_tbidx = -1;
  caml_jit_codtable->ct_nbblock--;
  if (caml_jit_codtable->ct_size > 30
      && caml_jit_codtable->ct_nbblock * 4 < caml_jit_codtable->ct_size) {
    int nbblock = caml_jit_codtable->ct_nbblock;
    volatile struct caml_jit_codbtable_st *oldcodtable = caml_jit_codtable;
    int oldsz = caml_jit_codtable->ct_size;
    int sz = (nbblock < 6) ? 13 : (nbblock < 20) ? 37 : (nbblock < 45) ? 97
      : (nbblock < 120) ? 211 : (nbblock < 280) ? 467 : (nbblock < 650) ? 1033
      : (nbblock < 1200) ? 2593 : ((2 * nbblock + 10) | 0xff);
    if (sz < caml_jit_codtable->ct_size) {
      caml_jit_codtable = calloc (1, sizeof (struct caml_jit_codbtable_st)
				  + sz * sizeof (void *));
      if (!caml_jit_codtable)
	caml_fatal_error_arg
	  ("camljitrun cannot shrink code table to %d elements", (char *) sz);
      caml_jit_codtable->ct_size = sz;
      for (i = 0; i < oldsz; i++) {
	struct caml_jit_codeblock_st *oldbl = oldcodtable->ct_tab[i];
	if (!oldbl || oldbl == JML_EMPTYBLOCKSLOT)
	  continue;
	Assert (oldbl->cb_magic == JIT_CODBL_MAGIC);
	Assert (oldbl->cb_tbidx == i);
	oldbl->cb_tbidx = -1;
	caml_jit_register_code_block (oldbl);
	oldcodtable->ct_tab[i] = 0;
      };
      oldcodtable->ct_size = 0;
      free ((void *) oldcodtable);
    }
  }
}				/* end of caml_jit_unregister_code_block */

static struct caml_jit_codeblock_st *
caml_jit_find_code_block (code_t prog, asize_t prog_size)
{
  unsigned long bycheck = caml_jit_code_checksum (prog, prog_size);
  int i = 0, h = 0;
  if (!caml_jit_codtable || caml_jit_codtable->ct_nbblock <= 0)
    return 0;
  Assert (caml_jit_codtable->ct_size > 2
	  && caml_jit_codtable->ct_nbblock < caml_jit_codtable->ct_size);
  h = (bycheck & 0xfffffff) % (caml_jit_codtable->ct_size);
  for (i = h; i < caml_jit_codtable->ct_size; i++) {
    struct caml_jit_codeblock_st *bl = caml_jit_codtable->ct_tab[i];
    if (!bl || bl == JML_EMPTYBLOCKSLOT)
      continue;
    Assert (bl->cb_magic == JIT_CODBL_MAGIC);
    Assert (bl->cb_tbidx == i);
    if (bl->cb_byprog == prog && bl->cb_bysize == prog_size) {
      int j = prog_size - 1;
      if (j > 1000)
	j = 1000;
      for (; j > 0; j--)
	if (prog[j] != bl->cb_byprog[j])
	  goto diffblock;
      JML_DBGPRINTF ("found codeblock %p prog %p siz %d", bl, prog,
		     prog_size);
      return bl;
    }
  diffblock:
    continue;
  };
  for (i = 0; i < h; i++) {
    struct caml_jit_codeblock_st *bl = caml_jit_codtable->ct_tab[i];
    if (!bl || bl == JML_EMPTYBLOCKSLOT)
      continue;
    Assert (bl->cb_magic == JIT_CODBL_MAGIC);
    Assert (bl->cb_tbidx == i);
    if (bl->cb_byprog == prog && bl->cb_bysize == prog_size) {
      int j = prog_size - 1;
      if (j > 1000)
	j = 1000;
      for (; j > 0; j--)
	if (prog[j] != bl->cb_byprog[j])
	  goto diffblock2;
      JML_DBGPRINTF ("found codeblock %p prog %p siz %d", bl, prog,
		     prog_size);
      return bl;
    }
  diffblock2:
    continue;
  };
  return 0;
}				/* end of caml_jit_find_code_block */

static volatile struct caml_jit_codeblock_st *
caml_jit_code_block_at_bytecode (code_t bpc)
{
  int i = 0;
  static int misscount;
  volatile struct caml_jit_codeblock_st *cblock = 0;
  for (i = 0; i < JML_CBLOCKCACHELEN; i++) {
    cblock = caml_jit_cachecb[i];
    if (!cblock)
      continue;
    if ((char *) bpc >= (char *) cblock->cb_byprog
	&& (char *) bpc < (char *) cblock->cb_byprog + cblock->cb_bysize)
      return cblock;
  };
  if (!caml_jit_codtable)
    return 0;
  for (i = caml_jit_codtable->ct_size - 1; i >= 0; i--) {
    cblock = caml_jit_codtable->ct_tab[i];
    if (!cblock || cblock == JML_EMPTYBLOCKSLOT)
      continue;
    if ((char *) bpc >= (char *) cblock->cb_byprog
	&& (char *) bpc < (char *) cblock->cb_byprog + cblock->cb_bysize) {
      caml_jit_cachecb[misscount % JML_CBLOCKCACHELEN] = cblock;
      misscount++;
      return cblock;
    }
  };
  return 0;
}				/* end of caml_jit_code_block_at_bytecode */

static struct caml_jit_codechunk_st *
caml_jit_new_chunk (struct caml_jit_codeblock_st *cblock, size_t siz)
{
  struct caml_jit_codechunk_st *ch = 0;
  static int pagesize;
  Assert (cblock != 0);
  if (!pagesize)
    pagesize = getpagesize ();
  if (siz < pagesize + 1000)
    siz = pagesize + 1000;
  siz += 100 + sizeof (struct caml_jit_codechunk_st);
  siz |= (pagesize - 1);
  siz++;
  ch = mmap ((void *) 0, (size_t) siz,
	     PROT_READ | PROT_WRITE | PROT_EXEC,
	     MAP_ANONYMOUS | MAP_PRIVATE, (int) -1 /*fd */ ,
	     (off_t) 0);
  if (MAP_FAILED == ch) {
    fprintf (stderr,
	     "ocaml cannot allocate jit code buffer of %d kilobytes - %s\n",
	     (int) (siz >> 10), strerror (errno));
    exit (2);
  };
  ch->ch_magic = JIT_CHUNK_MAGIC;
  ch->ch_cblock = cblock;
  ch->ch_next = 0;
  ch->ch_prev = 0;
  if (cblock->cb_lastchunk) {
    Assert (cblock->cb_lastchunk->ch_next == 0);
    cblock->cb_lastchunk->ch_next = ch;
    ch->ch_prev = cblock->cb_lastchunk;
    cblock->cb_lastchunk = ch;
  } else {
    Assert (cblock->cb_firstchunk == 0);
    cblock->cb_firstchunk = cblock->cb_lastchunk = ch;
  };
  ch->ch_end = (char *) ch + siz;
  return ch;
}				/* end of caml_jit_new_chunk */


#ifdef DEBUG
static void
caml_jit_display_generation_time (void)
{
  fprintf (stderr, "\nOcamlJIT generation time ("
	   "$Revision: 1.52 $"
	   "):\n  %g seconds for %lld bytecode instructions = %g usec/bci = %g Mbci/sec\n",
	   caml_jit_gentime, caml_jit_nbgen,
	   (caml_jit_gentime * 1.0e6) / (double) caml_jit_nbgen,
	   (double) (1.0e-6 * caml_jit_nbgen) / (double) caml_jit_gentime);
  fflush (stderr);
}
#endif /*DEBUG*/
  static void
caml_jit_parse_option (char *jit_option)
{
  char *po = 0;
#ifdef DEBUG
  int fd = -1;
#endif
  JML_DBGPRINTF ("jitoption '%s'", jit_option);
  caml_jit_options.jitopt_bycod_chunk_size = DEFAULT_BYCOD_CHUNK_SIZE;
  po = strstr (jit_option, "chunk");
  if (po) {
    sscanf (po, "chunk=%d", &caml_jit_options.jitopt_bycod_chunk_size);
  } else if (strstr (jit_option, "batch"))
    caml_jit_options.jitopt_bycod_chunk_size = 0;
  if (caml_jit_options.jitopt_bycod_chunk_size > 0
      && caml_jit_options.jitopt_bycod_chunk_size < MIN_BYCOD_CHUNK_SIZE)
    caml_jit_options.jitopt_bycod_chunk_size = MIN_BYCOD_CHUNK_SIZE;
  JML_DBGPRINTF ("jit options chunk %d",
		 caml_jit_options.jitopt_bycod_chunk_size);
#ifdef DEBUG
  po = strstr (jit_option, "count");
  if (po)
    caml_jit_options.jitopt_count_flag = 1;
  JML_DBGPRINTF ("jit options count=%d", caml_jit_options.jitopt_count_flag);
  fd = -1;
  po = strstr (jit_option, "todbgfd=");
  if (po && sscanf (po, "todbgfd=%d", &fd) > 0 && fd > 0)
    caml_jit_options.jitopt_to_debugger_file = fdopen (fd, "w");
  fd = -1;
  po = strstr (jit_option, "fromdbgfd=");
  if (po && sscanf (po, "fromdbgfd=%d", &fd) > 0 && fd > 0)
    caml_jit_options.jitopt_from_debugger_file = fdopen (fd, "r");
  po = strstr (jit_option, "time");
  if (po) {
    caml_jit_options.jitopt_measure_time = 1;
    atexit (caml_jit_display_generation_time);
  };
#endif /*DEBUG*/
}



void
caml_jit_init (long codelen)
{
  int nbent = 0;
  int logent = 0;
  int i = 0;
  char *jit_option = 0;
  if (caml_jit_pc_tblptr)	/* already initialized */
    return;
  if (sizeof (double) != sizeof (value)
      && sizeof (double) != 2 * sizeof (value))
    caml_fatal_error
      ("camljit requires that double fits in a value word or two\n");
  logent = 16;
  if (codelen < 10000)
    codelen = 10000;
  codelen += 1024 + (3 * codelen) / 4;
  while ((1 << logent) < codelen)
    logent++;
  nbent = 1 << logent;
  caml_jit_pc_tblptr = calloc (nbent, sizeof (*caml_jit_pc_tblptr));
  caml_jit_pc_tblsiz = calloc (nbent, sizeof (int));
  if (!caml_jit_pc_tblptr || !caml_jit_pc_tblsiz) {
    fprintf (stderr,
	     "ocaml (caml_jit_init) cannot allocate bytecode tables for %d entries - %s\n",
	     nbent, strerror (errno));
    exit (2);
  };
  caml_jit_pc_logsz = logent;
  caml_jit_pc_mask = (1 << logent) - 1;
  caml_jit_nb_entries = 0;
  for (i = nbent - 1; i >= 0; i--) {
    caml_jit_pc_tblptr[i] =
      (struct caml_jit_pc_entry_st *) &caml_jit_empty_bucket;
    caml_jit_pc_tblsiz[i] = 0;
  };
  JML_DBGPRINTF (" nbent=%d", nbent);
#ifdef DEBUG
  {
    char *disnam = getenv ("OCAMLJITASM");
    if (disnam) {
      strncpy (caml_jit_disname, disnam, sizeof (caml_jit_disname) - 1);
      JML_DBGPRINTF ("disassembly file name %s", caml_jit_disname);
    };
  }
#endif
  jit_option = getenv ("OCAMLJITOPTION");
  if (jit_option && jit_option[0])
    caml_jit_parse_option (jit_option);
#ifdef DEBUG
  JML_TODEBUGGER_PRINTF ("# fd%d to debugger opened by pid %d camljit built "
			 __DATE__ "@" __TIME__,
			 caml_jit_options.
			 jitopt_to_debugger_file ? fileno (caml_jit_options.
							   jitopt_to_debugger_file)
			 : (-1), (int) getpid ());
  JML_TODEBUGGER_PRINTF ("JITREVISION \"%s " __DATE__ "@" __TIME__ "\"",
			 "$Revision: 1.52 $");
  JML_TODEBUGGER_PRINTF
    ("STATEOFFSETS accu=%d env=%d xtra=%d bypc=%d savbpc=%d", JML_OFF_ACCU,
     JML_OFF_ENV, JML_OFF_EXTRA_ARGS, JML_OFF_BYTEPC, JML_OFF_SAVEDBYTEPC);
  if (caml_jit_options.jitopt_to_debugger_file)
    fprintf (stderr, "jittodebugger debug with fd todebugger %d\n",
	     fileno (caml_jit_options.jitopt_to_debugger_file));
  fflush (stderr);
  fflush (stdout);
  signal (SIGUSR1, SIG_IGN);
#endif /*DEBUG*/
}				/* end of caml_jit_init */


inline jit_insn *
caml_jit_get_pc (code_t bytepc)
{
  struct caml_jit_pc_entry_st *buck = 0;
  unsigned long h =
    (((unsigned long) bytepc ^ (((unsigned long) bytepc) >> 13))
     & caml_jit_pc_mask);
  int bucksiz = caml_jit_pc_tblsiz[h];
  int i = 0;
  buck = caml_jit_pc_tblptr[h];
  for (i = 0; i < bucksiz; i++)
    if (buck[i].jml_bytepc == bytepc)
      return buck[i].jml_machinepc;
  return 0;
}

inline void *
caml_jit_remove_pc (code_t bytepc)
{
  struct caml_jit_pc_entry_st *buck = 0;
  unsigned long h =
    (((unsigned long) bytepc ^ (((unsigned long) bytepc) >> 13))
     & caml_jit_pc_mask);
  int bucksiz = caml_jit_pc_tblsiz[h];
  int i = 0;
  buck = caml_jit_pc_tblptr[h];
  for (i = 0; i < bucksiz; i++)
    if (buck[i].jml_bytepc == bytepc) {
      buck[i].jml_bytepc = JML_EMPTYPC;
      caml_jit_nb_entries--;
      return buck[i].jml_machinepc;
    }
  return 0;
}

static inline void
caml_jit_add_pc_unsave (code_t bytepc, void *machinepc)
{
  struct caml_jit_pc_entry_st *buck = 0;
  unsigned long h =
    (((unsigned long) bytepc ^ (((unsigned long) bytepc) >> 13))
     & caml_jit_pc_mask);
  int bucksiz = caml_jit_pc_tblsiz[h];
  if (bucksiz <= 0) {
#define MINBUCKSIZE 3
    buck = calloc (MINBUCKSIZE, sizeof (*buck));
    if (!buck) {
      fprintf (stderr,
	       "ocaml (caml_jit_add_pc..) cannot allocate new bucket - %s\n",
	       strerror (errno));
      exit (2);
    };
    caml_jit_pc_tblsiz[h] = MINBUCKSIZE;
    caml_jit_pc_tblptr[h] = buck;
    buck[0].jml_bytepc = bytepc;
    buck[0].jml_machinepc = machinepc;
    caml_jit_nb_entries++;
  } else {
    int i;
    buck = caml_jit_pc_tblptr[h];
    for (i = 0; i < bucksiz - 1; i++) {
      code_t thispc = buck[i].jml_bytepc;
      if (thispc == bytepc) {
	buck[i].jml_machinepc = machinepc;
	return;
      } else if (!thispc || thispc == JML_EMPTYPC) {
	buck[i].jml_bytepc = bytepc;
	buck[i].jml_machinepc = machinepc;
	caml_jit_nb_entries++;
	return;
      }
    };
    {
      int newsiz = 0, i = 0, j = 0;
      struct caml_jit_pc_entry_st *newbuck = 0;
      // should grow the bucket...
      newsiz = (bucksiz + MINBUCKSIZE + bucksiz / 2) | 7;
      newbuck = calloc (newsiz, sizeof (*newbuck));
      newbuck[0].jml_bytepc = bytepc;
      newbuck[0].jml_machinepc = machinepc;
      caml_jit_nb_entries++;
      for (i = 0, j = 1; i < bucksiz; i++)
	if (buck[i].jml_bytepc && buck[i].jml_bytepc != JML_EMPTYPC) {
	  newbuck[j] = buck[i];
	  j++;
	};
      caml_jit_pc_tblsiz[h] = newsiz;
      caml_jit_pc_tblptr[h] = newbuck;
      buck[0].jml_bytepc = 0;
      free (buck);
    };
  };
}				/* end of caml_jit_add_pc_unsave */

static void
caml_jit_add_pc_with_reallocation (code_t bytepc, void *machinepc)
{
  struct caml_jit_pc_entry_st **old_tblptr = caml_jit_pc_tblptr;
  int *old_tblsiz = caml_jit_pc_tblsiz;
  int old_logsz = caml_jit_pc_logsz;
  int new_logsz = old_logsz + 1;
  int newsz = 0, oldsz = 0, i = 0;
  while ((1UL << new_logsz) < 2UL * (1024 + caml_jit_nb_entries))
    new_logsz++;
  newsz = 1 << new_logsz;
  oldsz = 1 << old_logsz;
  JML_DBGPRINTF ("grow - resizing pctbl from %d (=2^%d) to %d (=2^%d)",
		 oldsz, old_logsz, newsz, new_logsz);
  caml_jit_pc_tblptr = calloc (newsz, sizeof (*caml_jit_pc_tblptr));
  caml_jit_pc_tblsiz = calloc (newsz, sizeof (int));
  if (!caml_jit_pc_tblptr || !caml_jit_pc_tblsiz) {
    fprintf (stderr,
	     "ocaml (caml_jit_init) cannot reallocate bytecode tables for %d entries - %s\n",
	     newsz, strerror (errno));
    exit (2);
  };
  caml_jit_pc_logsz = new_logsz;
  caml_jit_pc_mask = (1UL << new_logsz) - 1;
  caml_jit_nb_entries = 0;
  for (i = newsz - 1; i >= 0; i--) {
    caml_jit_pc_tblptr[i] =
      (struct caml_jit_pc_entry_st *) &caml_jit_empty_bucket;
    caml_jit_pc_tblsiz[i] = 0;
  };
  for (i = 0; i < oldsz; i++) {
    struct caml_jit_pc_entry_st *oldbuck = old_tblptr[i];
    int j = 0;
    if (oldbuck == &caml_jit_empty_bucket)
      continue;
    for (j = old_tblsiz[i] - 1; j >= 0; j--) {
      code_t bpc = oldbuck[j].jml_bytepc;
      if (bpc != 0)
	caml_jit_add_pc_unsave (bpc, oldbuck[j].jml_machinepc);
    };
    oldbuck[0].jml_bytepc = 0;
    free (oldbuck);
    old_tblsiz[i] = 0;
    old_tblptr[i] = 0;
  };
  free (old_tblptr);
  free (old_tblsiz);
}

static inline void
caml_jit_add_pc (code_t bytepc, void *machinepc)
{
  if (caml_jit_nb_entries < (1 << (caml_jit_pc_logsz - 1)))
    caml_jit_add_pc_unsave (bytepc, machinepc);
  else				// should reallocate the table
    caml_jit_add_pc_with_reallocation (bytepc, machinepc);
}				// end of caml_jit_add_pc



  /* lightning registers V0 V1 V2 are preserved across function calls
     and R0 R1 R2 are lost */
#define JML_REG_ACC   JIT_V0	/* the interpreter's ACC (call saved) */

  /* we can lose SP since it is always copied to caml_extern_sp before
     calls; for some object oriented bytecodes REG_SP is used as a
     temporary and restored */
#define JML_REG_SP    JIT_R0	/* the interpreter's SP (call lost) */
  /* the rest of the interpreter's state is packed in a C structure */
#define JML_REG_STATE JIT_V1	/* pointer to interpreter's state (call saved) */
  /* temporary registers */
#define JML_REG_TMP0  JIT_V2	/* call saved */
#define JML_REG_TMP1  JIT_R1	/* call lost */
/* we should consider using TMP2 as the env */
#define JML_REG_TMP2ENV  JIT_R2	/* call lost */
#define JML_REG_ENVTMP2  JIT_R2	/* call lost */

#define JMLIT_save_env() jit_stxi_l(JML_OFF_ENV, JML_REG_STATE, JML_REG_ENVTMP2)
#define JMLIT_restore_env() jit_ldxi_l(JML_REG_ENVTMP2, JML_REG_STATE, JML_OFF_ENV)
#define JMLIT_save_temp2() jit_stxi_l(JML_OFF_TEMP2, JML_REG_STATE, JML_REG_TMP2ENV)
#define JMLIT_restore_temp2()  jit_ldxi_l(JML_REG_TMP2ENV, JML_REG_STATE, JML_OFF_TEMP2)

/* TMP2 is used (as a temporary) in the prologue, APPLY3, APPTERM3,
   RESTART, MAKEBLOCK, MAKEBLOCK1, MAKEBLOCK2, MAKEBLOCK3,
   MAKEFLOATBLOCK, GETFLOATFIELD, SETFLOATFIELD, VECTLENGTH, PUSHTRAP,
   GETMETHOD, and is lost in all C calls and returns so should be
   saved if it is the env
 */



// routine to generate code for small allocation (word size & tag are
// constants known at compile time!) tmp0 tmp1 tmp2 are used, and the
// returned pointer is in register resreg. This is a hand-crafted
// compile-time expansion of Alloc_small (using the Setup_for_gc and
// Restore_after_gc)
static void
caml_jit_generate_alloc_small_const (int resreg, int wosize, int tag)
{
  jit_insn *reftest = 0;
  CAMLassert (wosize > 0);
  CAMLassert (wosize <= Max_young_wosize);
  CAMLassert (tag >= 0 && tag < 256);
  JML_DBGPRINTF ("generate alloc wosize=%d tag=%d jitpc %p", wosize, tag,
		 jit_get_ip ().ptr);
  //. tmp0 = caml_young_ptr; tmp0 -= Bhsize_wosize(wosize); 
  jit_ldi_p (JML_REG_TMP0, &caml_young_ptr);
  jit_subi_p (JML_REG_TMP0, JML_REG_TMP0, Bhsize_wosize (wosize));
  //. tmp1 = caml_young_limit; if tmp0 >= tmp1 goto updateyoungptr;
  jit_ldi_p (JML_REG_TMP1, &caml_young_limit);
  reftest = jit_bger_i (jit_forward (), JML_REG_TMP0, JML_REG_TMP1);
  //. sp -= 2w; sp[0] = accu; tmp2 = env; sp[1] = tmp2;
  jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE * 2);
  jit_str_p (JML_REG_SP, JML_REG_ACC);
  jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_ENVTMP2);
  //. caml_extern_sp = sp;
  jit_sti_p (&caml_extern_sp, JML_REG_SP);
  //. caml_minor_collection();
  (void) jit_calli (caml_minor_collection);
  //. acc = sp[0]; env = sp[1]; sp += 2;
  jit_ldi_p (JML_REG_SP, &caml_extern_sp);
  jit_ldr_p (JML_REG_ACC, JML_REG_SP);
  jit_ldxi_p (JML_REG_ENVTMP2, JML_REG_SP, WORDSIZE);
  JMLIT_save_env ();
  jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE * 2);
  //. tmp0 = caml_young_ptr; tmp0 -= Bhsize_wosize(wosize); 
  jit_ldi_p (JML_REG_TMP0, &caml_young_ptr);
  jit_subi_p (JML_REG_TMP0, JML_REG_TMP0, Bhsize_wosize (wosize));
  //. label updateyoungptr:
  jit_patch (reftest);
  //. caml_young_ptr = tmp0;
  jit_sti_p (&caml_young_ptr, JML_REG_TMP0);
  //. tmp1 = Make_header(wosize,tag,Caml_black)
  JML_DBGPRINTF ("generate alloc wosize%d tag%d so header %#lx jitpc %p",
		 wosize, tag, Make_header (wosize, tag, Caml_black),
		 jit_get_label ());
  jit_movi_l (JML_REG_TMP1, Make_header (wosize, tag, Caml_black));
  //. *tmp0 = tmp1
  jit_str_p (JML_REG_TMP0, JML_REG_TMP1);
  //.resreg = tmp0 + 1w
  jit_stxi_p (1 * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
  jit_addi_p (resreg, JML_REG_TMP0, WORDSIZE);
  JML_DBGPRINTF ("generate alloc wosize=%d ended jitpc %p", wosize,
		 jit_get_ip ().ptr);
}				/* end of caml_jit_generate_alloc_small_const */




static void
caml_jit_generate_check_stack_and_signals (int tempreg, code_t bytepc)
{
  jit_insn *reftestsp = 0, *reftestdo = 0;
  JML_DBGPRINTF ("stack&signal check start jitpc %p bytepc %p",
		 jit_get_label (), bytepc);
  //. tempreg = caml_stack_threshold
  jit_ldi_p (tempreg, &caml_stack_threshold);
  //. if sp >= caml_stack_threshold goto ok;
  reftestsp = jit_bger_l (jit_forward (), JML_REG_SP, tempreg);
  //. caml_extern_sp = sp; savedacc = acc; tempreg =  pc; bytepc = tempreg
  jit_sti_p (&caml_extern_sp, JML_REG_SP);
  jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
  JMLIT_save_env ();
  if (bytepc) {
    jit_movi_p (tempreg, bytepc);
    jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, tempreg);
  };
  //. tempreg = Stack_threshold / sizeof (value); caml_realloc_stack(tempreg)
  jit_movi_l (tempreg, Stack_threshold / sizeof (value));
  jit_prepare_i (1);
  jit_pusharg_l (tempreg);
  (void) jit_finish (caml_realloc_stack);
  // restore sp & acc 
  jit_ldi_p (JML_REG_SP, &caml_extern_sp);
  jit_ldxi_p (JML_REG_ACC, JML_REG_STATE, JML_OFF_ACCU);
  JMLIT_restore_env ();
  //. label ok
  jit_patch (reftestsp);
  JML_DBGPRINTF ("stack&signal check end jitpc %p", jit_get_label ());
  //. tempreg = caml_something_to_do
  jit_ldi_p (tempreg, &caml_something_to_do);
  //. if (!tempreg) goto next;
  reftestdo = jit_beqi_l (jit_forward (), tempreg, 0);
  jit_sti_p (&caml_extern_sp, JML_REG_SP);
  jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
  if (bytepc) {
    jit_movi_p (tempreg, bytepc);
    jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, tempreg);
  };
  JMLIT_save_env ();
  jit_movi_l (JIT_RET, MLJSTATE_PROCESS_SIGNAL);
  jit_ret ();
  //. label next
  jit_patch (reftestdo);
  JML_DBGPRINTF ("stack&signal check end jitpc %p bytepc %p",
		 jit_get_label (), bytepc);
}



struct jml_forwardjump_st {
  int jfj_jump;			/* 0 if adress, 1 if jump */
  jit_insn *jfj_ref;		/* reference */
  code_t jfj_dest;		/* bytecode destination */
};

struct jml_forward_st {
  int jf_size;			/* allocated size */
  int jf_nb;			/* number of used entries */
  struct jml_forwardjump_st jf_ent[0];	/* actual length is jf_size */
};

#define FORWARD_JUMP 1
#define FORWARD_ADDR 0

static inline void
jml_add_forward (struct jml_forward_st **pt, void *ref, code_t dest,
		 int isjump)
{
  int i = ((*pt)->jf_nb);
  JML_DBGPRINTF ("add forward#%d ref %p bytdest %p isjump %d",
		 i, ref, dest, isjump);
  if (i + 1 >= (*pt)->jf_size) {
    int newsz = (3 * i / 2 + 30) | 0xf;
    struct jml_forward_st *newtb = 0;
    newtb = calloc (1, sizeof (struct jml_forward_st)
		    + newsz * sizeof (struct jml_forwardjump_st));
    JML_DBGPRINTF ("resizing forward old size %d newsz %d", (*pt)->jf_size,
		   newsz);
    if (!newtb)
      caml_fatal_error_arg
	("cannot grow jit forward jump table to %d entries", (char *) newsz);
    for (i = 0; i < (*pt)->jf_nb; i++)
      newtb->jf_ent[i] = (*pt)->jf_ent[i];
    newtb->jf_size = newsz;
    newtb->jf_nb = (*pt)->jf_nb;
    free (*pt);
    *pt = newtb;
    i = newtb->jf_nb;
  };
  (*pt)->jf_ent[i].jfj_ref = ref;
  (*pt)->jf_ent[i].jfj_dest = dest;
  (*pt)->jf_ent[i].jfj_jump = isjump;
  (*pt)->jf_nb = i + 1;
}

//static struct jit_fp jml_fpbuffer[300];


#ifdef DEBUG

static void
caml_jit_disassemble (FILE * f, char *msg, void *start, void *end)
{
  extern void disassemble (FILE *, void *, void *);
  char *pc;
  fprintf (f, "\n**@@** DISASSEMBLY %s - %p - %p\n", msg, start, end);
  disassemble (f, start, end);
  for (pc = (char *) ((long) start & (~0x1f));
       pc <= (char *) ((long) start | 0xf); pc++) {
    if (((long) pc & 0x1f) == 0)
      fprintf (f, "\n@%#lx:  ", (long) pc);
    else if (((long) pc & 0xf) == 0)
      fputs (" . ", f);
    else if (((long) pc & 0x7) == 0)
      fputs ("  ", f);
    else if (((long) pc & 0x3) == 0)
      fputs (" ", f);
    fprintf (f, "%02x", (*pc) & 0xff);
  };
  putc ('\n', f);
  putc ('\n', f);
  fflush (f);
}
#endif

static struct caml_jit_codechunk_st *
caml_jit_generate_prologue (struct caml_jit_codeblock_st *cblock)
{
  int inum = 0;
  struct caml_jit_codechunk_st *chunk = 0;
  void *start = 0;
  jit_insn *againref = 0, *ref = 0;
  Assert (cblock && cblock->cb_magic == JIT_CODBL_MAGIC);
  chunk = cblock->cb_lastchunk;
  if (!chunk)
    chunk = caml_jit_new_chunk (cblock,
				1000 +
				cblock->cb_bysize *
				JIT_NATIVEBYTE_PER_BYTECODE);
  Assert (chunk && chunk->ch_magic == JIT_CHUNK_MAGIC);
  Assert (cblock->cb_start == 0);
  Assert (cblock->cb_curinstr == 0);
  cblock->cb_curinstr = chunk->ch_instrzone;
  start = cblock->cb_curinstr;
  /* on PowerPC, jit_set_ip actually may generate some trampoline code */
  JML_DBGPRINTF ("set_ip %p", cblock->cb_curinstr);
  (void) jit_set_ip (cblock->cb_curinstr);
  cblock->cb_curinstr = cblock->cb_start = (void *) jit_get_label ();
  JML_DBGPRINTF ("start of prolog chunk %p instrzone %p curinstr %p",
		 chunk, chunk->ch_instrzone, cblock->cb_curinstr);
  /******************* generate the function prologue */
  jit_prolog (1);
  JML_DBGPRINTF ("after jit_prolog jitpc %p", jit_get_label ());
  /* generate: sp = caml_extern_sp */
  jit_ldi_p (JML_REG_SP, &caml_extern_sp);
  JML_DBGPRINTF ("before arg jitpc %p", jit_get_label ());
  /* generate getting the state register from argument */
  inum = jit_arg_p ();
  jit_getarg_p (JML_REG_STATE, inum);
  JML_DBGPRINTF
    ("in prolog loaded caml_extern_sp @%p before jitcode %#x start %p",
     &caml_extern_sp, (int) (jit_get_label ()), start);
  /* generate clearing of temporary registers */
  jit_movi_p (JML_REG_TMP0, 0);
  jit_movi_p (JML_REG_TMP1, 0);
  jit_movi_p (JML_REG_TMP2ENV, 0);
  /*** generate the code to jump at bytecode PC (from the state) ***/
  cblock->cb_jumppcref = jit_get_label ();
#ifdef DEBUG
  JML_DBGPRINTF ("jumppcref %p", cblock->cb_jumppcref);
  jit_nop ();			/* can break here */
  JML_TODEBUGGER_PRINTF ("PROLOGBLOCK bl=%d jpc=%#x",
			 cblock->cb_rank, (int) (cblock->cb_jumppcref));
#endif
  /* generate: get accu from state */
  jit_ldxi_p (JML_REG_ACC, JML_REG_STATE, JML_OFF_ACCU);
  JML_DBGPRINTF ("prolog jitpc %p", jit_get_label ());
  //. tmp2 = caml_jit_pc_mask; tmp0 = bytepc;
  jit_ldi_p (JML_REG_TMP2ENV, &caml_jit_pc_mask);
  jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_BYTEPC);
  //. tmp1 = tmp0; tmp1 = tmp1 >> 13; tmp1 = tmp0 ^ tmp1;
  jit_movr_l (JML_REG_TMP1, JML_REG_TMP0);
  jit_rshi_ul (JML_REG_TMP1, JML_REG_TMP1, 13);
  jit_xorr_l (JML_REG_TMP1, JML_REG_TMP1, JML_REG_TMP0);
  JML_DBGPRINTF ("prolog jitpc %p", jit_get_label ());
  /* generate: tmp1 = (tmp1 & tmp2)) << log2wordsize */
  jit_andr_i (JML_REG_TMP1, JML_REG_TMP2ENV, JML_REG_TMP1);
  jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, LOG2WORDSIZE);
  /* generate: tmp2 = caml_jit_pc_tblptr */
  jit_ldi_p (JML_REG_TMP2ENV, &caml_jit_pc_tblptr);
  /* generate tmp2 = tmp2[tmp1] */
  jit_ldxr_p (JML_REG_TMP2ENV, JML_REG_TMP2ENV, JML_REG_TMP1);
  /* generate label again: */
  againref = jit_get_label ();
  /* generate tmp1 = tmp2 -> jml_bytepc; ## ie tmp1 = *tmp2 */
  JML_DBGPRINTF ("prolog jitpc %p", jit_get_label ());
  jit_ldr_p (JML_REG_TMP1, JML_REG_TMP2ENV);
  /* generate if tmp1 != tmp0 goto next */
  ref = jit_bner_i (jit_forward (), JML_REG_TMP1, JML_REG_TMP0);
  /* generate tmp1 = tmp2 -> jml_machinepc */
  jit_ldxi_p (JML_REG_TMP1, JML_REG_TMP2ENV,
	      offsetof (struct caml_jit_pc_entry_st, jml_machinepc));
  JMLIT_restore_env ();
  /* generate goto *tmp1 */
  jit_jmpr (JML_REG_TMP1);
  /* generate label next: tmp2 += 2 */
  jit_patch (ref);
  jit_addi_p (JML_REG_TMP2ENV, JML_REG_TMP2ENV,
	      sizeof (struct caml_jit_pc_entry_st));
  /* generate if tmp1 != 0 goto again */
  ref = jit_bnei_i (againref, JML_REG_TMP1, 0);
  JML_DBGPRINTF ("prolog jitpc %p", jit_get_label ());
  jit_nop ();
  //. flush accu & sp 
  jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
  jit_sti_p (&caml_extern_sp, JML_REG_SP);
  /* don't flush env since tmp2 has been used above */
  /* generate: return MLJSTATE_JITRANSLATE if target not found */
  jit_movi_l (JIT_RET, MLJSTATE_JITRANSLATE);
  jit_ret ();
  JML_DBGPRINTF ("prolog jitpc after return  MLJSTATE_JITRANSLATE %p",
		 jit_get_label ());
  jit_nop ();
  JML_DBGPRINTF ("flush code %p %p", (char *) start,
		 (char *) jit_get_label ());
  jit_flush_code ((char *) start, (char *) jit_get_label ());
  cblock->cb_curinstr = jit_get_label ();
  return chunk;
}




/** caution; the representation of tagged integers, ie the Val_long
    and Long_val (or Val_int and Int_val) macros is built in the
    generated code, so this translator won't be valid if the tagged
    integers are represented differently */

static struct caml_jit_codechunk_st *
caml_jit_translate (code_t prog, struct caml_jit_codeblock_st *cblock)
{
  register code_t pc = 0, oldpc = 0;
  opcode_t curr_instr = 0;
  void *oldjit = 0;
  int num = 0;
  int nbgen = 0;
  int nbbci = 0;
#ifdef DEBUG
  static int gencnt;
  struct tms genstarttms;
  struct tms genendtms;
#endif
  struct caml_jit_codechunk_st *chunk = 0;
  struct caml_jit_codechunk_st *firstchunk = 0;
  Assert (cblock && cblock->cb_magic == JIT_CODBL_MAGIC);
  firstchunk = chunk = cblock->cb_lastchunk;
  Assert (chunk && chunk->ch_magic == JIT_CHUNK_MAGIC);
  JML_TODEBUGGER_PRINTF ("BEGINGEN bl=%d gen=%d", ++gencnt, cblock->cb_rank);
  JML_DBGPRINTF ("set_ip %p", cblock->cb_curinstr);
  (void) jit_set_ip (cblock->cb_curinstr);
  JML_DBGPRINTF ("jit translate prog=%#x", (int) prog);
#ifdef DEBUG
  if (caml_jit_options.jitopt_measure_time) {
    memset (&genstarttms, 0, sizeof (genstarttms));
    memset (&genendtms, 0, sizeof (genendtms));
    times (&genstarttms);
  };
  nbbci = 1;
#endif
  /***************** loop to generate every instruction */
  for (pc = prog;
       (char *) pc < (char *) cblock->cb_byprog + cblock->cb_bysize;) {
    void *jitpc = 0;
    Assert (pc >= cblock->cb_byprog
	    && (char *) pc <= (char *) cblock->cb_byprog + cblock->cb_bysize);
    jitpc = caml_jit_get_pc (pc);
    if (jitpc) {
      JML_DBGPRINTF ("jit translate known pc %#lx", (long) pc);
      (void) jit_jmpi (jitpc);
      JML_DBGPRINTF ("jit stopping generation pc %#lx", (long) pc);
      goto stop_generation;
    };
    JML_DBGPRINTF ("start loop gen pc%p oldpc%p", pc, oldpc);
    /* RESTART instructions mark the beginning of n-ary (with n>=2)
       functions, so are good places to stop the compilation */
    if (nbgen >= caml_jit_options.jitopt_bycod_chunk_size
	&& caml_jit_options.jitopt_bycod_chunk_size > 0 && *pc == RESTART) {
      JML_DBGPRINTF ("jit translate cutting at RESTART pc %p nbgen%d", pc,
		     nbgen);
      jit_movi_p (JML_REG_TMP0, pc);
      jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
      //. goto jumpbytepc;
      (void) jit_jmpi (cblock->cb_jumppcref);
      jit_nop ();
      jit_nop ();
      goto stop_generation;
    };
    JML_DBGPRINTF ("pc=%p oldpc=%p block%p prog%p",
		   pc, oldpc, cblock, cblock->cb_byprog);
    oldpc = pc;
    oldjit = jit_get_label ();
    if ((char *) oldjit + 256 * sizeof (int) >= (char *) chunk->ch_end)
    add_chunk:			/* come from JML_CHECK_PC */
    {
      int remainbyc =
	(((char *) cblock->cb_byprog + cblock->cb_bysize) -
	 (char *) pc) / sizeof (*pc);
      struct caml_jit_codechunk_st *newchunk = 0;
      jit_insn *jref = 0;
      newchunk = caml_jit_new_chunk (cblock, 500 * sizeof (int)
				     + ((char *) chunk->ch_end -
					(char *) oldjit)
				     +
				     JIT_NATIVEBYTE_PER_BYTECODE * remainbyc);
      JML_DBGPRINTF ("new chunk %p jumping from %p", newchunk,
		     jit_get_label ());
      jref = jit_jmpi (jit_forward ());
      jit_nop ();
      jit_nop ();
      JML_DBGPRINTF ("flush code %p %p", (char *) chunk->ch_instrzone,
		     (char *) (jit_get_label ()) - 1);
      jit_flush_code ((char *) chunk->ch_instrzone,
		      (char *) (jit_get_label ()) - 1);
      chunk = newchunk;
      JML_DBGPRINTF ("set_ip %p", chunk->ch_instrzone);
      (void) jit_set_ip (chunk->ch_instrzone);
      cblock->cb_curinstr = jit_get_label ();
      jit_patch (jref);
    };
    ////
#define JML_CHECK_PC() do {                                        \
    if ((char*)jit_get_label() + 150 * sizeof(int)                 \
        >= (char*)chunk->ch_end) {                                 \
      JML_DBGPRINTF("checkpc jit %p pc %p", jit_get_label(), pc);  \
      pc = oldpc;                                                  \
      /* jit_raw_set_ip(oldjit); */                                \
      jit_get_label () = oldjit;                                   \
      goto add_chunk;                                              \
} } while (0)
    ////
    caml_jit_add_pc (pc, jit_get_label ());
#ifdef DEBUG
    JML_DBGPRINTF ("bytepc %p jitpc %p", pc, jit_get_ip ().ptr);
    JML_DBGPRINTF ("bytepc byteinstr %#x %s before set_instr",
		   *pc, caml_instr_string (pc));
    JML_TODEBUGGER_PRINTF ("INSTR bl=%d off=%d bpc=%#lx nad=%#lx txt=\"%s\"",
			   cblock->cb_rank,
			   pc - cblock->cb_byprog, (long) pc,
			   (long) jit_get_label (), caml_instr_string (pc));
    jit_nop ();			/* insert a nop to ease debugging */
    if (caml_trace_flag) {
      fflush (stderr);
      fflush (stdout);
      printf
	("tracing jit bytpc=%#x (@%d) bytinstr %#x (=%d) jitpc=%#x\n",
	 (int) pc, (int) (pc - cblock->cb_byprog), (int) *pc, (*pc) & 0xff,
	 (int) (jit_get_ip ().ptr));
      fflush (stdout);
      caml_disasm_instr (pc);
      fflush (stderr);
      fflush (stdout);
    };
    if (caml_jit_options.jitopt_count_flag) {
      JML_DBGPRINTF ("generating ins counting jitpc %p", jit_get_label ());
      jit_ldi_l (JML_REG_TMP1, &caml_jit_inscounter);
      jit_movi_p (JML_REG_TMP0, pc);
      jit_addi_l (JML_REG_TMP1, JML_REG_TMP1, nbbci);
      jit_sti_l (&caml_jit_inscounter, JML_REG_TMP1);
      jit_sti_p (&caml_jit_bytepc, JML_REG_TMP0);
    };
    nbbci = 1;
    if (caml_jit_options.jitopt_to_debugger_file && gencnt % 128 == 0) {
      fflush (caml_jit_options.jitopt_to_debugger_file);
      usleep (50000);
    };
#endif
    curr_instr = *(pc++);
    JML_DBGPRINTF ("curr_instr %d = %#x : %s @ jitpc %p = %d",
		   (int) curr_instr, (int) curr_instr,
		   caml_instr_string (pc - 1), jit_get_label (),
		   (int) jit_get_label ());
    switch (curr_instr) {
    case ACC0:			/* acc = sp[0] */
      jit_ldr_p (JML_REG_ACC, JML_REG_SP);
      break;
    case ACC1:			/* acc = sp[1] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 1 * WORDSIZE);
      break;
    case ACC2:			/* acc = sp[2] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 2 * WORDSIZE);
      break;
    case ACC3:			/* acc = sp[3] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 3 * WORDSIZE);
      break;
    case ACC4:			/* acc = sp[4] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 4 * WORDSIZE);
      break;
    case ACC5:			/* acc = sp[5] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 5 * WORDSIZE);
      break;
    case ACC6:			/* acc = sp[6] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 6 * WORDSIZE);
      break;
    case ACC7:			/* acc = sp[7] */
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, 7 * WORDSIZE);
      break;
    case PUSH:
    case PUSHACC0:		/* sp--; *sp = acc;  */
      jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      break;
    /*****/
      /****
	   peephole optim for PUSHACCn&ADDINT 
	   PUSHACCn: sp--; *sp = accu; accu = sp[n];
	   ADDINT: accu = (value)((long) accu + (long) *sp - 1); sp++;
	   ====
	   sp[-1] = accu; accu=sp[n-1];
	   accu = (value)((long) accu + sp[-1] -1
           ====
           tmp1 = accu-1; accu= sp[n-1]
           accu = (value)((long) accu) + tmp1         

	   peephole optim for PUSHACCn&SUBINT 
	   PUSHACCn: sp--; *sp = accu; accu = sp[n];
           SUBINT: accu = (value)((long) accu - (long) *sp + 1); sp++;
	   ====
	   sp[-1] = accu; accu=sp[n-1];
	   accu = (value)((long) accu - sp[-1] +1
           ====
           tmp1 = accu -1 ; accu= sp[n-1]
           accu = (value)((long) accu) - tmp1    
       ****/

#define JMLIT_pushaccn(N)  do {                                 \
   JML_DBGPRINTF("PUSHACC%d jitpc %#x", (N),                    \
                 (int)(jit_get_label()));                       \
   if (pc[0]==ADDINT) {                                         \
     JML_DBGPRINTF("peephole pushacc addint pc.%p=prog+%d",     \
         pc, pc - prog);                                        \
     jit_subi_l(JML_REG_TMP1, JML_REG_ACC, 1);                  \
     jit_ldxi_l(JML_REG_ACC, JML_REG_SP, ((N)-1)*WORDSIZE);     \
     jit_addr_l(JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);        \
     pc += 1; nbbci++;                                          \
     JML_DBGPRINTF("peepedhole pc%p nbbci%d", pc, nbbci);       \
   } else if (pc[0]==SUBINT) {                                  \
     JML_DBGPRINTF("peephole pushacc subint pc.%p=prog+%d",     \
         pc, pc - prog);                                        \
     jit_subi_l(JML_REG_TMP1, JML_REG_ACC, 1);                  \
     jit_ldxi_l(JML_REG_ACC, JML_REG_SP, ((N)-1)*WORDSIZE);     \
     jit_subr_l(JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);        \
     pc += 1; nbbci++;                                          \
     JML_DBGPRINTF("peepedhole pc%p nbbci%d", pc, nbbci);       \
   } else {                                                     \
   jit_subi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);                \
   jit_str_p(JML_REG_SP, JML_REG_ACC);                          \
   jit_ldxi_p(JML_REG_ACC, JML_REG_SP, (N)*WORDSIZE);           \
   }                                                            \
 } while(0)

    /*****/
    case PUSHACC1:		/* sp--; *sp = acc; acc = sp[1] */
      JMLIT_pushaccn (1);
      break;
    case PUSHACC2:		/*  sp--; *sp = acc; acc = sp[2] */
      JMLIT_pushaccn (2);
      break;
    case PUSHACC3:
      JMLIT_pushaccn (3);
      break;
    case PUSHACC4:
      JMLIT_pushaccn (4);
      break;
    case PUSHACC5:
      JMLIT_pushaccn (5);
      break;
    case PUSHACC6:
      JMLIT_pushaccn (6);
      break;
    case PUSHACC7:
      JMLIT_pushaccn (7);
      break;
    case PUSHACC:
      num = *pc;
      pc++;
      JMLIT_pushaccn (num);
      break;
#undef JMLIT_pushaccn

#define JMLIT_pushacc()                                 \
    jit_subi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);       \
    jit_str_p(JML_REG_SP, JML_REG_ACC);
    case ACC:
      /* acc = sp[*pc++] */
      num = *pc++;
      jit_ldxi_p (JML_REG_ACC, JML_REG_SP, num * WORDSIZE);
      break;
    case POP:
      num = *pc++;
      jit_addi_p (JML_REG_SP, JML_REG_SP, num * WORDSIZE);
      break;
    case ASSIGN:
      num = *pc++;
      /* sp[num] = acc; acc = valunit */
      jit_stxi_p (num * WORDSIZE, JML_REG_SP, JML_REG_ACC);
      jit_movi_p (JML_REG_ACC, Val_unit);
      break;
    /*****/
      /*** old definition fetch env from state 
#define JMLIT_envaccn(N)                                                \
    jit_ldxi_p(JML_REG_TMP0, JML_REG_STATE, JML_OFF_ENV);               \
    jit_ldxi_p(JML_REG_ACC, JML_REG_TMP0, (long)(&Field(NULL, (N))))
      ***/
#define JMLIT_envaccn(N) jit_ldxi_p(JML_REG_ACC, JML_REG_ENVTMP2,  (long)(&Field(NULL, (N))))
    case ENVACC1:		/* accu = Field(env, 1) */
      JMLIT_envaccn (1);
      break;
    case ENVACC2:		/* accu = Field(env, 2) */
      JMLIT_envaccn (2);
      break;
    case ENVACC3:		/* accu = Field(env, 3) */
      JMLIT_envaccn (3);
      break;
    case ENVACC4:		/* accu = Field(env, 4) */
      JMLIT_envaccn (4);
      break;
    case ENVACC:
      num = *pc++;
      JMLIT_envaccn (num);
      break;


/***
      peephole optim:
      PUSHENVACCn: sp--; *sp = accu; accu = Field(env, n);
      ADDINT: accu = (value)((long) accu + (long) *sp - 1); sp++;
      ====      PUSHENVACCn&ADDINT
      tmp1 = accu-1; accu = Field(env, n);
      accu = accu + tmp1
      PUSHENVACCn&SUBINT
      tmp1 = accu-1; accu= Field(env, n);
      accu = accu - tmp1;

 ***/

#define JMLIT_pushenvaccn(N) do{					\
	if (*pc == ADDINT) {						\
        JML_DBGPRINTF("peephole pushenvacc addint pc.%p=prog+%d",      	\
	 pc, pc - prog);						\
	 jit_subi_l(JML_REG_TMP1, JML_REG_ACC, 1);			\
	 jit_ldxi_p(JML_REG_ACC, JML_REG_ENVTMP2, (N)*WORDSIZE);	\
	 jit_addr_l(JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);		\
         pc += 1; nbbci++;						\
         JML_DBGPRINTF("peepedhole pc.%p nbbci.%d", pc, nbbci);         \
	} else if (*pc == SUBINT) {					\
        JML_DBGPRINTF("peephole pushenvacc subint pc.%p=prog+%d",	\
	 pc, pc - prog);						\
	 jit_subi_l(JML_REG_TMP1, JML_REG_ACC, 1);			\
	 jit_ldxi_p(JML_REG_ACC, JML_REG_ENVTMP2, (N)*WORDSIZE);	\
	 jit_subr_l(JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);		\
         pc += 1; nbbci++;         	       				\
         JML_DBGPRINTF("peepedhole pc.%p nbbci.%d", pc, nbbci);         \
	} else {							\
	  jit_subi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);			\
	  jit_str_p(JML_REG_SP, JML_REG_ACC);				\
	  jit_ldxi_p(JML_REG_ACC, JML_REG_ENVTMP2, (N)*WORDSIZE);	\
	}								\
      } while(0)

    case PUSHENVACC1:		/* sp--; *sp = acc; acc = Field(env, 1) */
      JMLIT_pushenvaccn (1);
      break;
    case PUSHENVACC2:		/* sp--; *sp = acc; acc = Field(env, 2) */
      JMLIT_pushenvaccn (2);
      break;
    case PUSHENVACC3:		/* sp--; *sp = acc; acc = Field(env, 3) */
      JMLIT_pushenvaccn (3);
      break;
    case PUSHENVACC4:		/* sp--; *sp = acc; acc = Field(env, 4) */
      JMLIT_pushenvaccn (4);
      break;
    case PUSHENVACC:
      num = *pc++;
      JMLIT_pushenvaccn (num);
      break;
    case PUSH_RETADDR:
      num = *pc;
      JML_DBGPRINTF ("PUSH_RETADDR %d pc%p jitaddr%p", num, pc,
		     jit_get_label ());
      //. sp -= 3;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 3 * WORDSIZE);
      //. tmp1 = (value) (pc + num); *sp = tmp0
      jit_movi_p (JML_REG_TMP1, (value) (pc + num));
      jit_str_p (JML_REG_SP, JML_REG_TMP1);
      //. sp[1] = env;
      jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_ENV);
      jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP0);
      //. sp[2] = Val_long(extra_args); so tmp0 = extra_args ...
      jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
      //. shift left tmp0 by 1 bit
      jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      //. add 1 to tmp0
      jit_addi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      //. sp[2] = tmp0
      jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_TMP0);
      pc++;
      break;
    case APPLY:
      num = *pc++;
      JML_DBGPRINTF ("APPLY num%d jitpc%p", num, jit_get_label ());
      //. extra_args = *pc - 1;
      jit_movi_p (JML_REG_TMP0, (num - 1));
      jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
    gen_load_pc_env:
      //. pc = Code_val(acc); #thru tmp0
      {
	int codoff = (int) (&(Code_val (NULL)));
	JML_DBGPRINTF ("genloadpcenv bypc %#lx jitpc %#lx codoff %#x=%d",
		       (long) pc, (long) jit_get_label (), codoff, codoff);
	JML_DBGPRINTF ("genloadpcenv bypc %#lx jitpc %#lx", (long) pc,
		       (long) jit_get_label ());
	//. save acc
	jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
	jit_ldxi_p (JML_REG_TMP0, JML_REG_ACC, codoff);
	JML_DBGPRINTF ("genloadpcenv bypc %#lx jitpc %#lx", (long) pc,
		       (long) jit_get_label ());
	jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
	JML_DBGPRINTF
	  ("genloadpcenv bypc %#lx before save env&acc jitpc %#lx", (long) pc,
	   (long) jit_get_label ());
	//. env = acc;
	jit_movr_p (JML_REG_ENVTMP2, JML_REG_ACC);
	JMLIT_save_env ();
	JML_DBGPRINTF ("genloadpcenv bypc %#lx after save env&acc jitpc %#lx",
		       (long) pc, (long) jit_get_label ());
	/* check the stack */
	caml_jit_generate_check_stack_and_signals (JML_REG_TMP1, (code_t) 0);
	JMLIT_restore_env ();
	//. goto jumpbytepc;
	(void) jit_jmpi (cblock->cb_jumppcref);
	jit_nop ();
	jit_nop ();
	JML_DBGPRINTF ("genloadpcenv end bypc %#lx jitpc %#lx", (long) pc,
		       (long) jit_get_label ());
	if (caml_jit_options.jitopt_bycod_chunk_size > 0
	    && nbgen >
	    3 * caml_jit_options.jitopt_bycod_chunk_size / 2 +
	    MIN_BYCOD_CHUNK_SIZE) {
	  JML_DBGPRINTF
	    ("genload pcenv stop generation bypc %#lx jitpc %#lx nbgen=%d",
	     (long) pc, (long) jit_get_label (), nbgen);
	  goto stop_generation;
	} else if (caml_jit_get_pc (pc + 1)) {
	  JML_DBGPRINTF ("genload stop generation nextpc %p known", pc + 1);
	  goto stop_generation;
	} else {		/* try to align to 16 bytes */
	  unsigned long limpc =
	    ((unsigned long) (jit_get_label ()) | 0xf) + 1;
	  while ((unsigned long) (jit_get_label ()) < limpc)
	    jit_nop ();
	};
      }
      break;
    case APPLY1:
      JML_DBGPRINTF ("APPLY1 start bypc %#lx jitpc %#lx", (long) pc,
		     (long) jit_get_label ());
      //. tmp0 = *sp;
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      // sp -= 3;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 3 * WORDSIZE);
      //. *sp = tmp0;
      jit_str_p (JML_REG_SP, JML_REG_TMP0);
      //. tmp1 = bytepc; sp[1] = tmp1;
      jit_movi_p (JML_REG_TMP1, pc);
      jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      JML_DBGPRINTF ("APPLY1 bypc %#lx jitpc %#lx", (long) pc,
		     (long) jit_get_label ());
      //. sp[2] = env;
      jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_ENVTMP2);
      //. sp[3] = Val_long(extra_args); so tmp1 = extra_args...
      jit_ldxi_p (JML_REG_TMP1, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
      //. tmp1 = tmp1 << 1 + 1
      jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      //. sp[3] = tmp1
      jit_stxi_p (3 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. extra_args = 0;
      jit_movi_l (JML_REG_TMP0, 0);
      jit_stxi_l (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
      JML_DBGPRINTF ("APPLY1 bypc %#lx jitpc %#lx", (long) pc,
		     (long) jit_get_label ());
      goto gen_load_pc_env;
    case APPLY2:
      //. tmp0 = *sp;
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      //. tmp1 = sp[1]
      jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
      // sp -= 3;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 3 * WORDSIZE);
      //. *sp = tmp0;
      jit_str_p (JML_REG_SP, JML_REG_TMP0);
      // sp[1] = tmp1;
      jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. tmp1 = bytepc; sp[2] = tmp1;
      jit_movi_p (JML_REG_TMP1, pc);
      jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. sp[3] = env;
      jit_stxi_p (3 * WORDSIZE, JML_REG_SP, JML_REG_TMP2ENV);
      //. sp[4] = Val_long(extra_args); so tmp1 = extra_args...
      jit_ldxi_l (JML_REG_TMP1, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
      //. tmp1 = tmp1 << 1 + 1
      jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      //. sp[4] = tmp1
      jit_stxi_p (4 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. extra_args = 1;
      jit_movi_l (JML_REG_TMP0, 1);
      jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
      JML_DBGPRINTF ("jitpc=%#x", (int) (jit_get_ip ().ptr));
      goto gen_load_pc_env;
    case APPLY3:
      //. tmp0 = *sp;
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      JMLIT_save_env ();
      //. tmp1 = sp[1]; tmp2 = sp[2]
      jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
      jit_ldxi_p (JML_REG_TMP2ENV, JML_REG_SP, 2 * WORDSIZE);
      //. sp -= 3;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 3 * WORDSIZE);
      //. *sp = tmp0;
      jit_str_p (JML_REG_SP, JML_REG_TMP0);
      //. sp[1] = tmp1; sp[2] = tmp2
      jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_TMP2ENV);
      //. tmp0 = bytepc; sp[3] = tmp0;
      jit_movi_p (JML_REG_TMP0, pc);
      jit_stxi_p (3 * WORDSIZE, JML_REG_SP, JML_REG_TMP0);
      //. restore env;  sp[4] = env;
      JMLIT_restore_env ();
      jit_stxi_p (4 * WORDSIZE, JML_REG_SP, JML_REG_ENVTMP2);
      //. sp[5] = Val_long(extra_args); so tmp1 = extra_args...
      jit_ldxi_p (JML_REG_TMP1, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
      //. tmp2 = tmp2 << 1 + 1
      jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      //. sp[5] = tmp1
      jit_stxi_p (5 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. extra_args = 2;
      jit_movi_l (JML_REG_TMP0, 2);
      jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
      /* restore_env uneeded, since env loaded in gen_load_pc_env */
      goto gen_load_pc_env;
    case APPTERM:
      {
	int nargs = *pc++, slotsize = *pc++, i = 0;
	//. tmp1 = sp + (slotsize-nargs)
	jit_addi_p (JML_REG_TMP1, JML_REG_SP, (slotsize - nargs) * WORDSIZE);
	for (i = nargs - 1; i >= 0; i--) {	// loop at compile time!
	  JML_CHECK_PC ();
	  //. tmp0 = sp[i]; tmp1[i] = tmp0
	  jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, i * WORDSIZE);
	  jit_stxi_p (i * WORDSIZE, JML_REG_TMP1, JML_REG_TMP0);
	};
	//. sp = tmp1
	jit_movr_p (JML_REG_SP, JML_REG_TMP1);
	//.  tmp0 = extra_args; tmp0 += (nargs - 1); extra_args = tmp0
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	jit_addi_l (JML_REG_TMP0, JML_REG_TMP0, (nargs - 1));
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	goto gen_load_pc_env;
      };
    case APPTERM1:
      {
	int delta = *pc++;
	//. tmp0 = sp[0]; sp += (delta-1)
	jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, (delta - 1) * WORDSIZE);
	//. sp[0] = tmp;
	jit_str_p (JML_REG_SP, JML_REG_TMP0);
	goto gen_load_pc_env;
      };
    case APPTERM2:
      {
	int delta = *pc++;
	//. tmp0 = sp[0]; tmp1 = sp[1]; sp += (delta-2)
	jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
	jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
	jit_addi_p (JML_REG_SP, JML_REG_SP, (delta - 2) * WORDSIZE);
	//. sp[0] = tmp0; sp[1] = tmp1;
	jit_str_p (JML_REG_SP, JML_REG_TMP0);
	jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
	//.  tmp0 = extra_args; tmp0 += 1; extra_args = tmp0
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	jit_addi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	goto gen_load_pc_env;
      };
    case APPTERM3:
      {
	int delta = *pc++;
	JMLIT_save_env ();
	//. tmp0 = sp[0]; tmp1 = sp[1]; tmp2 = sp[2]; sp += (delta-3)
	jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
	jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
	jit_ldxi_p (JML_REG_TMP2ENV, JML_REG_SP, 2 * WORDSIZE);
	jit_addi_p (JML_REG_SP, JML_REG_SP, (delta - 3) * WORDSIZE);
	//. sp[0] = tmp0; sp[1] = tmp1; sp[2] = tmp2;
	jit_str_p (JML_REG_SP, JML_REG_TMP0);
	jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
	jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_TMP2ENV);
	//.  tmp0 = extra_args; tmp0 += 2; extra_args = tmp0
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	jit_addi_l (JML_REG_TMP0, JML_REG_TMP0, 2);
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	/* restore_env not needed, since env loaded below */
	goto gen_load_pc_env;
      };
    case RETURN:
      {
	int delta = *pc++;
	jit_insn *ref = 0;
	JML_DBGPRINTF ("RETURN delta %d jitc%#x", delta,
		       (int) jit_get_label ());
	//. sp += delta;
	if (delta != 0)
	  jit_addi_l (JML_REG_SP, JML_REG_SP, delta * WORDSIZE);
	//. save acc
	jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
	//. tmp0 = extra_args; if (extra_args>0) goto next;
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	ref = jit_bgti_i (jit_forward (), JML_REG_TMP0, 0);
	//. tmp1 = sp[0]; bytepc = tmp1
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);
	//. tmp1 = sp[1]; env = tmp1;
	jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
	jit_stxi_p (JML_OFF_ENV, JML_REG_STATE, JML_REG_TMP1);
	//. tmp1 = sp[2]; tmp1 = Long_val(tmp1) // ie tmp2>>1
	jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 2 * WORDSIZE);
	jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
	//. extra_args = tmp1
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP1);
	//. sp += 3; goto jumpbytepc;
	jit_addi_l (JML_REG_SP, JML_REG_SP, 3 * WORDSIZE);
	(void) jit_jmpi (cblock->cb_jumppcref);
	jit_nop ();
	jit_patch (ref);
	//. next: tmp0 = tmp0-1; extra_args = tmp0;
	jit_subi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	goto gen_load_pc_env;
      };
    case RESTART:
      {
	jit_insn *againref = 0, *loopref = 0;
	JMLIT_save_env ();
	//. tmp2 is env; tmp1 = Wosize_val(tmp1)-2 ie (tmp2[-1] >> 10)-2 ## tmp1 is num_args
	jit_ldxi_p (JML_REG_TMP1, JML_REG_TMP2ENV, -1 * WORDSIZE);
	jit_rshi_ul (JML_REG_TMP1, JML_REG_TMP1, 10);
	jit_subi_l (JML_REG_TMP1, JML_REG_TMP1, 2);
	// tmp0 = tmp1 << log_of_word_size
	jit_lshi_l (JML_REG_TMP0, JML_REG_TMP1, LOG2WORDSIZE);
	//. sp -= tmp0; 
	jit_subr_p (JML_REG_SP, JML_REG_SP, JML_REG_TMP0);
	JML_DBGPRINTF ("inside RESTART bypc%#x jitpc%p", (int) pc,
		       jit_get_label ());
	//. tmp0 = extra_args; tmp0 += tmp1; extra_args = tmp0
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	jit_addr_l (JML_REG_TMP0, JML_REG_TMP0, JML_REG_TMP1);
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	// tmp1 = tmp1 << log_of_word_size
	jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, LOG2WORDSIZE);
	//. tmp1 -= 1w; tmp2 += 2w
	jit_subi_p (JML_REG_TMP1, JML_REG_TMP1, WORDSIZE);
	jit_addi_p (JML_REG_TMP2ENV, JML_REG_TMP2ENV, 2 * WORDSIZE);
	//. loop: if (tmp1<0) goto next;
	loopref = jit_get_label ();
	againref = jit_blti_i (jit_forward (), JML_REG_TMP1, 0);
	//. tmp0 = Field(tmp2,tmp1) ie tmp2[tmp1]
	jit_ldxr_p (JML_REG_TMP0, JML_REG_TMP2ENV, JML_REG_TMP1);
	//. sp[tmp1] = tmp0
	jit_stxr_p (JML_REG_SP, JML_REG_TMP1, JML_REG_TMP0);
	//. tmp1 -= WORDSIZE
	jit_subi_l (JML_REG_TMP1, JML_REG_TMP1, WORDSIZE);
	//. goto loop;
	(void) jit_jmpi (loopref);
	jit_patch (againref);
	JMLIT_restore_env ();
	//. tmp1 = env; tmp0 = Field(tmp1, 1) ie tmp1[WORDSIZE]; env = tmp0
	jit_movr_p (JML_REG_TMP1, JML_REG_ENVTMP2);
	jit_ldxi_p (JML_REG_TMP0, JML_REG_TMP1, WORDSIZE);
	jit_movr_p (JML_REG_ENVTMP2, JML_REG_TMP0);
	JMLIT_save_env ();
	break;
      };
    case GRAB:
      {
	int required = *pc;
	jit_insn *endref = 0, *testref = 0;
	JML_DBGPRINTF ("GRAB required%d", required);
	//. tmp0 = extra_args; if (tmp0< required) goto next;
	jit_ldxi_p (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
	testref = jit_blti_l (jit_forward (), JML_REG_TMP0, required);
	//. tmp0 -= required; extra_args = tmp0; goto end;
	jit_subi_l (JML_REG_TMP0, JML_REG_TMP0, required);
	jit_stxi_p (JML_OFF_EXTRA_ARGS, JML_REG_STATE, JML_REG_TMP0);
	endref = jit_jmpi (jit_forward ());
	JML_DBGPRINTF ("inside GRAB jitpc%p", jit_get_label ());
	jit_patch (testref);
	//. save pc & accu
	jit_movi_p (JML_REG_TMP1, pc);
	jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);
	jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
	//. caml_extern_sp = sp
	jit_sti_p (&caml_extern_sp, JML_REG_SP);
	JMLIT_save_env ();
	//. return MLJSTATE_GRAB
	jit_movi_l (JIT_RET, MLJSTATE_GRAB);
	jit_ret ();
	//. end:
	jit_patch (endref);
	JML_DBGPRINTF ("end GRAB jitpc%p", jit_get_label ());
	pc++;
	break;
      };
    case CLOSURE:
      {
	int nvars = *pc++;
	int off = *pc, i = 0;
	code_t clopc = pc + off;
	pc++;
	JML_DBGPRINTF ("CLOSURE nvar%d off%d clopc%#lx", nvars, off,
		       (long) clopc);
	if (nvars > 0) {	//compile time test
	  //. sp--; *sp = accu
	  jit_subi_l (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
	  jit_str_p (JML_REG_SP, JML_REG_ACC);
	};
	//useless JMLIT_save_env();
	/* uses TMP0 TMP1  */
	caml_jit_generate_alloc_small_const (JML_REG_ACC, 1 + nvars,
					     Closure_tag);
	//. tmp0 = clopc; *acc = tmp0 ## ie Code_val(acc) = tmp0
	jit_movi_p (JML_REG_TMP0, clopc);
	jit_str_p (JML_REG_ACC, JML_REG_TMP0);
	JML_DBGPRINTF ("closure jitpc%p", jit_get_label ());
	if (nvars > 0) {
	  //. tmp0 = acc+1w
	  jit_addi_p (JML_REG_TMP0, JML_REG_ACC, 1 * WORDSIZE);
	  for (i = 0; i < nvars; i++) {	//compiletime loop
	    JML_CHECK_PC ();
	    //. tmp1 = sp[i]; Field(acc,i+1) = tmp1## ie tmp0[i] = tmp1
	    if (0 == i) {
	      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	      jit_str_p (JML_REG_TMP0, JML_REG_TMP1);
	    } else {
	      jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, i * WORDSIZE);
	      jit_stxi_p (i * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	    };
	  };
	  jit_addi_p (JML_REG_SP, JML_REG_SP, nvars * WORDSIZE);
	};
	//useless JMLIT_restore_env();
	break;
      };
    case CLOSUREREC:
      {
	int nfuncs = *pc++;
	int nvars = *pc++;
	int off = *pc;
	int i;
	JML_DBGPRINTF ("CLOSUREREC nfuncs%d nvars%d off%d jitpc%#x",
		       nfuncs, nvars, off, (int) jit_get_label ());
	//useless JMLIT_save_env();
	if (nvars > 0) {	//compile time test
	  //. sp--; *sp = accu
	  jit_subi_l (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
	  jit_str_p (JML_REG_SP, JML_REG_ACC);
	};
	/* use TMP0 TMP1 */
	caml_jit_generate_alloc_small_const (JML_REG_ACC,
					     2 * nfuncs - 1 + nvars,
					     Closure_tag);
	for (i = 0; i < nvars; i++) {	//compile time loop
	  JML_CHECK_PC ();
	  //. tmp1 = sp[i]; acc[i+nfuncs*2-1] = tmp1
	  if (0 == i) {
	    jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	  } else {
	    jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, i * WORDSIZE);
	  };
	  jit_stxi_p ((i + nfuncs * 2 - 1) * WORDSIZE, JML_REG_ACC,
		      JML_REG_TMP1);
	};
	//. sp += nvars words; tmp0 = pc+off; *acc = tmp0
	jit_addi_p (JML_REG_SP, JML_REG_SP, nvars * WORDSIZE);
	jit_movi_p (JML_REG_TMP0, pc + off);
	jit_str_p (JML_REG_ACC, JML_REG_TMP0);
	//. sp--; *sp = acc
	jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
	jit_str_p (JML_REG_SP, JML_REG_ACC);
	for (i = 1; i < nfuncs; i++) {	//compile time loop
	  //. tmp1 =  Make_header(i*2,Infix_tag,Caml_white); acc[2*i-1] = tmp1
	  jit_movi_l (JML_REG_TMP1,
		      Make_header (i * 2, Infix_tag, Caml_white));
	  jit_stxi_p (WORDSIZE * (2 * i - 1), JML_REG_ACC, JML_REG_TMP1);
	  //. tmp0 = pc+pc[i]; acc[2*i] = tmp0
	  jit_movi_l (JML_REG_TMP0, pc + pc[i]);
	  jit_stxi_l (WORDSIZE * (2 * i), JML_REG_ACC, JML_REG_TMP0);
	  //. sp--; tmp0 = acc + (2*i)word; *sp = tmp0
	  jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	  jit_addi_p (JML_REG_TMP0, JML_REG_ACC, WORDSIZE * (2 * i));
	  jit_str_p (JML_REG_SP, JML_REG_TMP0);
	};
	//useless JMLIT_restore_env();
	pc += nfuncs;
	break;
      };
    case PUSHOFFSETCLOSURE:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case OFFSETCLOSURE:
      num = *pc++;
      //. acc = env + num * sizeof(value)
      jit_addi_l (JML_REG_ACC, JML_REG_ENVTMP2, num * sizeof (value));
      break;
    case PUSHOFFSETCLOSUREM2:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case OFFSETCLOSUREM2:
      //. acc = env - 2 * sizeof(value)
      jit_subi_l (JML_REG_ACC, JML_REG_ENVTMP2, 2 * sizeof (value));
      break;
    case PUSHOFFSETCLOSURE0:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case OFFSETCLOSURE0:
      //. acc = env
      jit_movr_p (JML_REG_ACC, JML_REG_ENVTMP2);
      break;
    case PUSHOFFSETCLOSURE2:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case OFFSETCLOSURE2:
      //.  acc = env + 2 * sizeof(value)
      jit_addi_l (JML_REG_ACC, JML_REG_ENVTMP2, 2 * sizeof (value));
      break;
    case PUSHGETGLOBAL:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case GETGLOBAL:
      num = *(pc++);
      JML_DBGPRINTF ("GETGLOBAL %d", num);
      //. tmp1 = caml_global_data; acc = tmp1[num]
      jit_ldi_p (JML_REG_TMP1, &caml_global_data);
      jit_ldxi_p (JML_REG_ACC, JML_REG_TMP1, num * WORDSIZE);
      break;
    case PUSHGETGLOBALFIELD:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      JML_DBGPRINTF ("PUSHGETGLOBALFIELD jitpc %p", jit_get_label ());
      /* fallthrough */
    case GETGLOBALFIELD:
      {
	int num = *(pc++);
	int off = *(pc++);
	JML_DBGPRINTF ("GETGLOBALFIELD num %d off %d jitpc %p", num, off,
		       jit_get_label ());
	//. tmp1 = caml_global_data; acc = tmp1[num]; acc = acc[off]
	jit_ldi_p (JML_REG_TMP1, &caml_global_data);
	JML_DBGPRINTF ("GETGLOBALFIELD caml_global_data@%p jitpc %p",
		       &caml_global_data, jit_get_label ());
	jit_ldxi_p (JML_REG_ACC, JML_REG_TMP1, num * WORDSIZE);
	jit_ldxi_p (JML_REG_ACC, JML_REG_ACC, off * WORDSIZE);
	JML_DBGPRINTF ("GETGLOBALFIELD done jitpc %p", jit_get_label ());
	break;
      };
    case SETGLOBAL:
      num = *(pc++);
      //. tmp1 = caml_global_data; (saved)acc = acc
      jit_ldi_p (JML_REG_TMP1, &caml_global_data);
      JML_DBGPRINTF ("SETGLOBAL num %d jitpc %p", num, jit_get_label ());
      jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
      //. push acc, push tmp1+num words
      jit_addi_p (JML_REG_TMP1, JML_REG_TMP1, num * WORDSIZE);
      //. caml_extern_sp = sp
      jit_sti_p (&caml_extern_sp, JML_REG_SP);
      JMLIT_save_env ();
      //. caml_modify(tmp1, acc);
      jit_prepare_i (2);
      jit_pusharg_p (JML_REG_ACC);
      jit_pusharg_p (JML_REG_TMP1);
      jit_finish (caml_modify);
      //. sp = caml_extern_sp ##since REG_SP not call safe; acc=Val_unit
      jit_ldi_p (JML_REG_SP, &caml_extern_sp);
      JMLIT_restore_env ();
      JML_DBGPRINTF ("jitpc %p", jit_get_label ());
      jit_movi_p (JML_REG_ACC, Val_unit);
      break;
    case PUSHATOM0:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_ldr_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case ATOM0:
      JML_DBGPRINTF ("ATOM0 jitpc %p caml_atom_table=%p",
		     jit_get_label (), caml_atom_table);
      jit_movi_p (JML_REG_ACC, Atom (0));
      break;
    case PUSHATOM:
      //. sp--; *sp = acc;
      jit_subi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      jit_ldr_p (JML_REG_SP, JML_REG_ACC);
      /* fallthrough */
    case ATOM:
      num = *(pc++);
      jit_movi_p (JML_REG_ACC, Atom (num));
      break;
    case MAKEBLOCK:
      {
	mlsize_t wosize = *pc++;
	tag_t tag = *pc++;
	mlsize_t i;
	JMLIT_save_env ();
	if (wosize <= Max_young_wosize) {
	  /* this call uses TMP0 TMP1 */
	  caml_jit_generate_alloc_small_const (JML_REG_TMP0, wosize, tag);
	  //. *tmp0 = acc;
	  jit_str_p (JML_REG_TMP0, JML_REG_ACC);
	  for (i = 1; i < wosize; i++) {	// compiletime loop
	    JML_CHECK_PC ();
	    //. tmp1 = sp[i-1]; tmp0[i] = tmp1
	    jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, (i - 1) * WORDSIZE);
	    jit_stxi_p (i * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	  };
	  //. sp += (wosize-1)*word
	  if (wosize > 1)
	    jit_addi_p (JML_REG_SP, JML_REG_SP, (wosize - 1) * WORDSIZE);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	} else {		/* big wosize */
	  /* return with MLJSTATE_MAKEBIGBLOCK */
	  //. save acc and sp
	  jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
	  jit_sti_p (&caml_extern_sp, JML_REG_SP);
	  //. tmp0 = (next)pc tmp1 = wosize; save state's bytepc & wosize
	  jit_movi_p (JML_REG_TMP0, pc);
	  jit_movi_l (JML_REG_TMP1, wosize);
	  jit_stxi_l (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
	  jit_stxi_l (JML_OFF_WOSIZE, JML_REG_STATE, JML_REG_TMP1);
	  // save state's tag and return
	  jit_movi_l (JML_REG_TMP1, tag);
	  jit_stxi_l (JML_OFF_TAG, JML_REG_STATE, JML_REG_TMP1);
	  /// don't bother restoring the env
	  jit_movi_i (JIT_RET, MLJSTATE_MAKEBIGBLOCK);
	  jit_ret ();
	};
	JML_DBGPRINTF ("MAKEBLOCK ended jit %p", jit_get_label ());
	break;
      };
    case MAKEBLOCK1:
      {
	tag_t tag = *pc++;
	JML_DBGPRINTF ("MAKEBLOCK1 tag %d", tag);
	JMLIT_save_env ();
	/* this call uses TMP0 TMP1 */
	caml_jit_generate_alloc_small_const (JML_REG_TMP0, 1, tag);
	//. *tmp0 = acc; acc = tmp0
	jit_str_p (JML_REG_TMP0, JML_REG_ACC);
	jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	JMLIT_restore_env ();
	JML_DBGPRINTF ("MAKEBLOCK1 ended jit %p", jit_get_label ());
	break;
      };
    case MAKEBLOCK2:
      {
	tag_t tag = *pc++;
	JMLIT_save_env ();
	/* this call uses TMP0 TMP1  */
	caml_jit_generate_alloc_small_const (JML_REG_TMP0, 2, tag);
	//. *tmp0 = acc; tmp1=sp[0]; tmp0[1]=tmp1; sp++; acc=tmp0
	jit_str_p (JML_REG_TMP0, JML_REG_ACC);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_stxi_p (1 * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	jit_addi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
	jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	JMLIT_restore_env ();
	JML_DBGPRINTF ("MAKEBLOCK2 ended jit %p", jit_get_label ());
	break;
      };
    case MAKEBLOCK3:
      {
	tag_t tag = *pc++;
	JMLIT_save_env ();
	/* this call uses TMP0 TMP1 TMP2 */
	caml_jit_generate_alloc_small_const (JML_REG_TMP0, 3, tag);
	//. *tmp0 = acc; tmp1=sp[0]; tmp0[1]=tmp1; tmp2=sp[1]; tmp0[2]=tmp2; 
	jit_str_p (JML_REG_TMP0, JML_REG_ACC);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_stxi_p (1 * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	jit_ldxi_p (JML_REG_TMP2ENV, JML_REG_SP, 1 * WORDSIZE);
	jit_stxi_p (2 * WORDSIZE, JML_REG_TMP0, JML_REG_TMP2ENV);
	jit_addi_p (JML_REG_SP, JML_REG_SP, 2 * WORDSIZE);
	//. sp += 2; acc = tmp0
	jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	JMLIT_restore_env ();
	JML_DBGPRINTF ("MAKEBLOCK3 ended jit %p", jit_get_label ());
	break;
      };
    case MAKEFLOATBLOCK:
      {
	mlsize_t size = *pc++;
	int i = 0, k = 0, d = 0;
	// jitfp_begin (jml_fpbuffer);
	if (size <= Max_young_wosize / Double_wosize) {
	  JMLIT_save_env ();
	  /* this call uses TMP0 TMP1 TMP2 */
	  caml_jit_generate_alloc_small_const (JML_REG_TMP0,
					       size * Double_wosize,
					       Double_array_tag);

	  // Store_double_field(tmp0, 0, Double_val(accu));
	  for (k = 0; k < sizeof (double) / sizeof (value); k++) {
	    jit_ldxi_p (JML_REG_TMP1, JML_REG_ACC, k * WORDSIZE);
	    jit_stxi_p (k * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	  };
	  for (i = 1; i < size; i++) {	//compile time loop
	    JML_CHECK_PC ();
	    d = i * (sizeof (double) / WORDSIZE);
	    //. Store_double_field(block, i, Double_val(sp[i-1])); ###ie
	    //. tmp2 = sp[i-1]
	    jit_ldxi_p (JML_REG_TMP2ENV, JML_REG_SP, (i - 1) * WORDSIZE);
	    for (k = 0; k < sizeof (double) / sizeof (value); k++) {
	      jit_ldxi_p (JML_REG_TMP1, JML_REG_TMP2ENV, k * WORDSIZE);
	      jit_stxi_p ((d + k) * WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	    };
	  };
	  //. acc = tmp0
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  //. sp += size-1
	  jit_addi_p (JML_REG_SP, JML_REG_SP, (size - 1) * WORDSIZE);
	  JMLIT_restore_env ();
	} else {		/* big size floating block */
	  /* return with MLJSTATE_MAKEBIGFLOATB */
	  //. save acc and sp and env
	  jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
	  JMLIT_save_env ();
	  jit_sti_p (&caml_extern_sp, JML_REG_SP);
	  //. tmp0 = (next)pc tmp1 = wosize; tmp2 = tag
	  jit_movi_p (JML_REG_TMP0, pc);
	  jit_movi_l (JML_REG_TMP1, size);
	  jit_movi_l (JML_REG_TMP2ENV, Double_array_tag);
	  jit_stxi_l (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
	  jit_stxi_l (JML_OFF_WOSIZE, JML_REG_STATE, JML_REG_TMP1);
	  jit_stxi_l (JML_OFF_TAG, JML_REG_STATE, JML_REG_TMP2ENV);
	  /* dont save env since tmp2 used above */
	  jit_movi_i (JIT_RET, MLJSTATE_MAKEBIGFLOATB);
	  jit_ret ();
	};
	break;
      };
#define JML_GET_FIELD(N) jit_ldxi_p(JML_REG_ACC, JML_REG_ACC, (N)*WORDSIZE)
    case GETFIELD0:		//. acc = acc[0] ## ie Field(acc, 0)
      JML_GET_FIELD (0);
      break;
    case GETFIELD1:		//. acc = acc[1] ## ie Field(acc, 1)
      JML_GET_FIELD (1);
      break;
    case GETFIELD2:		//. acc = acc[2] ## ie Field(acc, 2)
      JML_GET_FIELD (2);
      break;
    case GETFIELD3:		//. acc = acc[2] ## ie Field(acc, 2)
      JML_GET_FIELD (3);
      break;
    case GETFIELD:
      num = *(pc++);
      JML_GET_FIELD (num);
      break;
#undef JML_GET_FIELD
    case GETFLOATFIELD:
      {
	//jitfp_begin (jml_fpbuffer);
	num = *(pc++);
	JMLIT_save_env ();
	/* this call uses TMP0 TMP1 TMP2 */
	caml_jit_generate_alloc_small_const (JML_REG_TMP0, Double_wosize,
					     Double_tag);
	//. (double*)tmp0 [0] = (double*)acc [num]
	jit_ldxi_l (JML_REG_TMP1, JML_REG_ACC, num * sizeof (double));
	jit_stxi_l (0, JML_REG_TMP0, JML_REG_TMP1);
	if (sizeof (double) >= 2 * WORDSIZE) {
	  jit_ldxi_l (JML_REG_TMP1, JML_REG_ACC,
		      num * sizeof (double) + WORDSIZE);
	  jit_stxi_l (WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);
	};
	jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	JMLIT_restore_env ();
	break;
      };



      /* the following macro is actually not useful; it inlines the
         field setting when the destination is in the young region;
         sadly and surprisingly (and against my intuition), it is a
         few percents slower than the original version below on x86 */

#define JML_SET_FIELD_INLINE(N) do {                           \
  jit_insn* t1ref=0, *t2ref=0, *jref=0;                        \
  JML_DBGPRINTF("SETFIELD %d jitpc%#x",                        \
                (N), (int)jit_get_label());                    \
  /* tmp0 = *sp; sp++;  */                                     \
  jit_ldr_p(JML_REG_TMP0, JML_REG_SP);                         \
  jit_addi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);                \
  /* modifdest = &acc[N] ie tmp1 = acc+N; modifdest=tmp1 */    \
  jit_addi_p(JML_REG_TMP1, JML_REG_ACC, (N)*WORDSIZE);         \
  /* accu=unit; save env */                                    \
  jit_movi_l(JML_REG_ACC, Val_unit);                           \
  JMLIT_save_env();                                            \
  /* tmp2 = caml_young_start; if tmp1 <=U tmp2 goto modif */   \
  jit_ldi_l(JML_REG_TMP2ENV, &caml_young_start);               \
  t1ref = jit_bler_ul(jit_forward(),                           \
                      JML_REG_TMP1, JML_REG_TMP2ENV);          \
  /* tmp2 = caml_young_end; if tmp1 >=U tmp2 goto modif */     \
  jit_ldi_l(JML_REG_TMP2ENV, &caml_young_start);               \
  t2ref = jit_bger_ul(jit_forward(), JML_REG_TMP1,             \
                      JML_REG_TMP2ENV);                        \
  /* goto inlinemodif */                                       \
  jref =  jit_jmpi (jit_forward ());                           \
  jit_nop();                                                   \
  /* label modif: */                                           \
  jit_patch(t1ref); jit_patch(t2ref);                          \
  /* save sp accu and env */                                   \
  jit_sti_p (&caml_extern_sp, JML_REG_SP);                     \
  jit_stxi_l(JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);        \
  /*   modval= tmp0; modifdest= tmp1 */                        \
  jit_stxi_l(JML_OFF_MODIFVAL, JML_REG_STATE, JML_REG_TMP0);   \
  jit_stxi_p(JML_OFF_MODIFDEST, JML_REG_STATE, JML_REG_TMP1);  \
  /*save pc thru tmp1*/                                        \
  jit_movi_p(JML_REG_TMP1, pc);                                \
  jit_stxi_p(JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);     \
  /* return MLJSTATE_MODIF */                                  \
  jit_movi_i(JIT_RET, MLJSTATE_MODIF);                         \
  jit_ret();  jit_nop();                                       \
  /* label inlinemodif: */                                     \
  jit_patch(jref);                                             \
  /* *tmp0 = tmp1 */                                           \
  jit_str_l(JML_REG_TMP0, JML_REG_TMP1);                       \
  JMLIT_restore_env();                                         \
} while(0)



      /* same as above, but surprisingly a bit faster */
#define JML_SET_FIELD(N) do {					\
  JML_DBGPRINTF("SETFIELD %d jitpc%#x",				\
		(N), (int)jit_get_label());			\
  /*save pc thru tmp1*/						\
  jit_movi_p(JML_REG_TMP1, pc);					\
  jit_stxi_p(JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);	\
  /* tmp0 = *sp; sp++; modval= tmp0; caml_extern_sp=sp */	\
  jit_ldr_p(JML_REG_TMP0, JML_REG_SP);				\
  jit_addi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);			\
  jit_stxi_l(JML_OFF_MODIFVAL, JML_REG_STATE, JML_REG_TMP0);	\
  jit_sti_p (&caml_extern_sp, JML_REG_SP);			\
  /* modifdest = &acc[N] ie tmp1 = acc+N; modifdest=tmp1 */	\
  jit_addi_p(JML_REG_TMP1, JML_REG_ACC, (N)*WORDSIZE);		\
  jit_stxi_p(JML_OFF_MODIFDEST, JML_REG_STATE, JML_REG_TMP1);	\
  /* accu=unit; save accu and env */	             		\
  jit_movi_l(JML_REG_ACC, Val_unit);                            \
  jit_stxi_l(JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);		\
  JMLIT_save_env();                                             \
  /* return MLJSTATE_MODIF */					\
  jit_movi_i(JIT_RET, MLJSTATE_MODIF);				\
  jit_ret();							\
} while(0)



    case SETFIELD0:
      JML_SET_FIELD (0);
      break;
    case SETFIELD1:
      JML_SET_FIELD (1);
      break;
    case SETFIELD2:
      JML_SET_FIELD (2);
      break;
    case SETFIELD3:
      JML_SET_FIELD (3);
      break;
    case SETFIELD:
      num = *(pc++);
      JML_SET_FIELD (num);
      break;
    case SETFLOATFIELD:
      {
	num = *(pc++);
	//. tmp0 = sp[0];
	jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
#ifndef ARCH_ALIGN_DOUBLE
	//jitfp_begin (jml_fpbuffer);
	//. ((*double)acc) [num] = *(double*)(tmp0);
	jit_ldr_d (JIT_FPR0, JML_REG_TMP0);
	jit_stxi_d (num * sizeof (double), JML_REG_ACC, JIT_FPR0);
#else
	jit_ldr_l (JML_REG_TMP1, JML_REG_TMP0);
	jit_stxi_l (num * sizeof (double), JML_REG_ACC, JML_REG_TMP1);
	if (sizeof (double) >= 2 * sizeof (value)) {
	  JMLIT_save_env ();
	  jit_ldxi_l (JML_REG_TMP2ENV, JML_REG_TMP0, WORDSIZE);
	  jit_stxi_l (num * sizeof (double) + WORDSIZE, JML_REG_ACC,
		      JML_REG_TMP2ENV);
	  JMLIT_restore_env ();
	};
#endif
	//. acc = Val_unit
	jit_movi_l (JML_REG_ACC, Val_unit);
	//. sp++;
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	break;
      };
    case VECTLENGTH:
      {
	jit_insn *reftest = 0;
	JMLIT_save_env ();
	/* compile time expansion of Wosize_val && Tag_val */
	//. tmp0 = (header_t*)acc[-1]; tmp2 = tmp0 & 0xff; tmp1 = tmp0 >> 10
	jit_ldxi_l (JML_REG_TMP0, JML_REG_ACC, -1 * WORDSIZE);
	jit_andi_l (JML_REG_TMP2ENV, JML_REG_TMP0, 0xff);
	jit_rshi_ul (JML_REG_TMP1, JML_REG_TMP0, 10);
	//. if tmp2 != Double_array_tag goto next
	reftest =
	  jit_bnei_i (jit_forward (), JML_REG_TMP2ENV, Double_array_tag);
	//. tmp1 = tmp1 / Double_wosize
	if (Double_wosize == 2) {
	  jit_rshi_ul (JML_REG_TMP1, JML_REG_TMP1, 1);
	} else {
	  jit_divi_l (JML_REG_TMP1, JML_REG_TMP1, Double_wosize);
	};
	jit_patch (reftest);
	//. acc = Val_long(tmp1) ie tmp1<<1 + 1
	jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
	jit_addi_l (JML_REG_ACC, JML_REG_TMP1, 1);
	JMLIT_restore_env ();
	break;
      };
    case GETVECTITEM:
      //. tmp0 = sp[0]; tmp0 = (tmp0 >> 1) << log2wordsize; acc = acc[tmp0]
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      jit_rshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      jit_lshi_ul (JML_REG_TMP0, JML_REG_TMP0, LOG2WORDSIZE);
      jit_ldxr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP0);
      //. sp++;
      jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
      break;
    case SETVECTITEM:
      //. tmp0 = sp[0]; tmp0 = (tmp0 >> 1) << log2wordsize; modifdest= acc+tmp0
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      jit_rshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      jit_lshi_ul (JML_REG_TMP0, JML_REG_TMP0, LOG2WORDSIZE);
      jit_addr_l (JML_REG_TMP1, JML_REG_ACC, JML_REG_TMP0);
      jit_stxi_l (JML_OFF_MODIFDEST, JML_REG_STATE, JML_REG_TMP1);
      //. tmp1 = sp[1]; modifnewval = tmp1
      jit_ldxi_l (JML_REG_TMP1, JML_REG_SP, WORDSIZE);
      jit_stxi_l (JML_OFF_MODIFVAL, JML_REG_STATE, JML_REG_TMP1);
      //. sp += 2w; save sp
      jit_addi_p (JML_REG_SP, JML_REG_SP, 2 * WORDSIZE);
      jit_sti_p (&caml_extern_sp, JML_REG_SP);
      /*save pc thru tmp1 */
      jit_movi_p (JML_REG_TMP1, pc);
      jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);
      JMLIT_save_env ();
      /* return MLJSTATE_MODIF */
      jit_movi_i (JIT_RET, MLJSTATE_MODIF);
      jit_ret ();
      break;
    case GETSTRINGCHAR:
      //. tmp0 = sp[0]; tmp0 = (tmp0 >> 1) ; 
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      jit_rshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      //. tmp1 = (char*)acc [tmp0]; acc = tmp1<<1 + 1
      jit_ldxr_c (JML_REG_TMP1, JML_REG_ACC, JML_REG_TMP0);
      jit_lshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addi_l (JML_REG_ACC, JML_REG_TMP1, 1);
      //. sp += 1w
      jit_addi_p (JML_REG_SP, JML_REG_SP, 1 * WORDSIZE);
      break;
    case SETSTRINGCHAR:
      //. tmp0 = sp[0]; tmp0 = (tmp0 >> 1) ; 
      jit_ldr_p (JML_REG_TMP0, JML_REG_SP);
      jit_rshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      //. tmp1 = sp[1]; tmp1 = tmp1 >> 1;
      jit_ldxi_l (JML_REG_TMP1, JML_REG_SP, WORDSIZE);
      jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      //. (char*) acc[tmp0] = tmp1
      jit_stxr_c (JML_REG_TMP0, JML_REG_ACC, JML_REG_TMP1);
      //. acc = Val_unit
      jit_movi_l (JML_REG_ACC, Val_unit);
      //. sp += 2w
      jit_addi_p (JML_REG_SP, JML_REG_SP, 2 * WORDSIZE);
      break;
    case BRANCH:
      num = *pc;
#define JML_GENERATE_BRANCH(TmpReg,TargetBytePc) do {			\
        code_t targbytepc =(TargetBytePc);				\
        int tmpreg = (TmpReg);						\
        jit_insn *targad = caml_jit_get_pc (targbytepc), *ref = 0;	\
        JML_DBGPRINTF("at bytpc %p branch to %p (jitpc %p)",		\
                      pc, targbytepc, jit_get_label());			\
      jit_movi_p (tmpreg, targbytepc);					\
      jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, tmpreg);		\
      if (targad)							\
        jit_jmpi (targad);						\
      else {								\
        ref = jit_jmpi (cblock->cb_jumppcref);				\
        jml_add_forward (&cblock->cb_forwards, ref, targbytepc,		\
                         FORWARD_JUMP);					\
      }									\
      jit_nop() /* for delay slot */;					\
    }   while (0)
      //. tmp0 = pc + num; bytepc = tmp0
      JML_DBGPRINTF ("BRANCH num%d", num);
      JML_GENERATE_BRANCH (JML_REG_TMP0, pc + num);
      pc++;
      break;
    case BRANCHIF:
      {
	jit_insn *jumpref = 0;
	num = *pc;
	JML_DBGPRINTF ("BRANCHIF num%d jitpc %#x", num,
		       (int) jit_get_label ());
	//. if (acc == Val_false) goto next;
	jumpref = jit_beqi_l (jit_forward (), JML_REG_ACC, Val_false);
	JML_GENERATE_BRANCH (JML_REG_TMP0, pc + num);
	//. next: ;
	jit_patch (jumpref);
	pc++;
	break;
      };
    case BRANCHIFNOT:
      {
	jit_insn *jumpref = 0;
	num = *pc;
	JML_DBGPRINTF ("BRANCHIFNOT num%d jitpc %#x", num,
		       (int) jit_get_label ());
	//. if (acc != Val_false) goto next;
	jumpref = jit_bnei_l (jit_forward (), JML_REG_ACC, Val_false);
	JML_GENERATE_BRANCH (JML_REG_TMP0, pc + num);
	//. next: ;
	jit_patch (jumpref);
	pc++;
	break;
      };
    case SWITCH:
      {


	jit_insn *testref = 0, *ldtagref = 0, *ldnumref = 0;
	int i = 0;
	void *p = 0, **tagtbl = 0, **numtbl = 0, *endtbl = 0;
	unsigned long l = 0;
	uint32 sizes = *(pc++);
	int tagsize = ((unsigned) sizes >> 16);
	int numsize = ((unsigned) sizes & 0xffff);
	JML_DBGPRINTF ("SWITCH sizes %08x tagsize %d numsize %d",
		       sizes, tagsize, numsize);
	if ((char *) jit_get_label () +
	    ((128 + tagsize + numsize) * (3 * sizeof (long))) / 2
	    >= (char *) chunk->ch_end) {
	  JML_DBGPRINTF
	    ("not enough jitspace for SWITCH tagsize %d numsize %d",
	     tagsize, numsize);
	  pc = oldpc;
	  /* I want to set the IP without generating the setup code,
	     so I cannot use jit_set_ip because it does jit_setup_code  */
	  ///  jit_raw_set_ip (oldjit);
	  jit_get_label () = oldjit;
	  goto add_chunk;
	}
	JMLIT_save_env ();
	/* compile time expansion of Is_block Tag_val .... */
	//. if (acc & 1 ==0) goto next ## Is_block
	testref = jit_bmci_l (jit_forward (), JML_REG_ACC, 1);
	//. tmp1 = acc>>1 ## ie Long_val(acc); tmp1 = tmp1<<log2wordsize; 
	jit_rshi_l (JML_REG_TMP1, JML_REG_ACC, 1);
	JML_DBGPRINTF ("switch jitpc=%p", jit_get_label ());
	jit_lshi_ul (JML_REG_TMP1, JML_REG_TMP1, LOG2WORDSIZE);
	ldnumref = jit_movi_p (JML_REG_TMP0, 0x54320123 /*placeholder */ );
	JML_DBGPRINTF ("first ldnumref %p", ldnumref);
	jit_ldxr_p (JML_REG_TMP0, JML_REG_TMP1, JML_REG_TMP0);
	jit_jmpr (JML_REG_TMP0);
	jit_nop ();
	jit_nop ();
	jit_patch (testref);
	JML_DBGPRINTF ("switch jitpc=%p", jit_get_label ());
	//. next:  tmp0 = acc[-1w]; tmp0 &= 0xff; ## Tag_val(acc); tmp0 <<= log2wordsize
	jit_ldxi_p (JML_REG_TMP0, JML_REG_ACC, -1 * WORDSIZE);	/* get the Header */
	jit_andi_l (JML_REG_TMP0, JML_REG_TMP0, 0xff);
	jit_lshi_l (JML_REG_TMP1, JML_REG_TMP0, LOG2WORDSIZE);
	ldtagref = jit_movi_p (JML_REG_TMP0, 0x65432012 /*placeholder */ );
	JML_DBGPRINTF ("second ldtagref %p", ldtagref);
	jit_ldxr_p (JML_REG_TMP0, JML_REG_TMP1, JML_REG_TMP0);
	jit_jmpr (JML_REG_TMP0);
	jit_nop ();
	jit_nop ();
	JML_DBGPRINTF ("switch jitpc=%p", jit_get_label ());
	jit_nop ();
	jit_nop ();
#if defined(__i386__) && defined(DEBUG)
	HLT_ ();
	jit_nop ();
	jit_nop ();
#endif
	jit_nop ();
	jit_nop ();
	// check jit space and round up jit pc to 8 words
	p = jit_get_ip ().ptr;
	if ((char *) p + (45 + tagsize + numsize) * WORDSIZE
	    >= (char *) chunk->ch_end)
	  caml_fatal_error ("not enough jit code space for switch tables");
	l = (unsigned long) p + 2 * WORDSIZE;
	l |= (4 * WORDSIZE) - 1;
	l++;
	p = numtbl = (void **) l;
	// skip space for the table
	while ((char *) jit_get_label () <=
	       (char *) numtbl + 2 * sizeof (long)) {
	  jit_nop ();
	};
	/* generate the jump table for number constant */
	for (i = 0; i < numsize; i++) {
	  code_t destbytepc = pc + pc[i];
	  jit_insn *destmachpc = caml_jit_get_pc (destbytepc);
	  JML_DBGPRINTF
	    ("switch constant num table %d @%p destbytepc %#lx destmachpc %p",
	     i, (void **) numtbl + i, (long) destbytepc, destmachpc);
	  if (destmachpc)
	    ((void **) numtbl)[i] = destmachpc;
	  else
	    jml_add_forward (&cblock->cb_forwards, ((void **) numtbl) + i,
			     destbytepc, FORWARD_ADDR);
	};
	tagtbl = numtbl + numsize + 1;
	endtbl = (void *) ((void **) tagtbl + tagsize + 2);
	// skip space for the table
	while ((char *) jit_get_label () <=
	       (char *) endtbl + 2 * sizeof (long)) {
	  jit_nop ();
	};
	jit_nop ();
	/* generate the jump table for tags */
	for (i = 0; i < tagsize; i++) {
	  code_t destbytepc = pc + pc[numsize + i];
	  jit_insn *destmachpc = caml_jit_get_pc (destbytepc);
	  JML_DBGPRINTF
	    ("switch tag table %d @%p destbytepc %#lx destmachpc %p", i,
	     (void **) tagtbl + i, (long) destbytepc, destmachpc);
	  if (destmachpc)
	    ((void **) tagtbl)[i] = destmachpc;
	  else
	    jml_add_forward (&cblock->cb_forwards, ((void **) tagtbl) + i,
			     destbytepc, FORWARD_ADDR);
	};

	/* We cannot use jit_set_ip because on some architectures
	   (PowerPC at least) it emit some non-trivial code with
	   jit_setup_code; we miss a jit_raw_set_ip */

	if (numsize > 0) {
	  /* patch the load num jump code */
	  jit_patch_movi (ldnumref, numtbl);
	  JML_DBGPRINTF
	    ("switch num.constant table at %#x (patched load at %p)",
	     (int) numtbl, ldnumref);
	};
	if (tagsize > 0) {
	  /* patch the load tag jump code */
	  jit_patch_movi (ldtagref, tagtbl);
	  JML_DBGPRINTF ("switch tag table at %#x (patched load at %p)",
			 (int) tagtbl, ldtagref);
	};
	jit_nop ();
	jit_nop ();
	jit_nop ();
	jit_nop ();
#if defined(__i386__) && defined(DEBUG)
	jit_nop ();
	jit_nop ();
	jit_nop ();
	jit_nop ();
	jit_nop ();
	jit_nop ();
	HLT_ ();
	HLT_ ();
	jit_nop ();
	jit_nop ();
#endif
	pc += tagsize + numsize;
	JML_DBGPRINTF ("end generation switch nextpc %p jitpc %p",
		       pc, jit_get_label ());
	break;
      };
    case BOOLNOT:
      //. acc = Val_not(acc) ## ie Val_not(0) - acc
      jit_rsbi_l (JML_REG_ACC, JML_REG_ACC, Val_not (0));
      break;
    case PUSHTRAP:
      /* expansion of Trap_pc (@0) & Trap_link (@1) */
      //. sp -=4; tmp1= pc+ (*pc); *sp = tmp1; tmp1= caml_trapsp; sp[1]= tmp1
      num = *pc;
      JML_DBGPRINTF ("PUSHTRAP %d jitpc %#x", num, (int) jit_get_label ());
      jit_subi_p (JML_REG_SP, JML_REG_SP, 4 * WORDSIZE);
      jit_movi_p (JML_REG_TMP1, pc + num);
      jit_str_p (JML_REG_SP, JML_REG_TMP1);
      jit_ldi_p (JML_REG_TMP1, &caml_trapsp);
      jit_stxi_p (1 * WORDSIZE, JML_REG_SP, JML_REG_TMP1);
      //. sp[2]= env;
      jit_stxi_p (2 * WORDSIZE, JML_REG_SP, JML_REG_ENVTMP2);
      //. tmp0 = extra_args << 1 +1
      jit_ldxi_l (JML_REG_TMP0, JML_REG_STATE, JML_OFF_EXTRA_ARGS);
      jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      jit_addi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
      //. sp[3] = tmp0; caml_trapsp = sp
      jit_stxi_p (3 * WORDSIZE, JML_REG_SP, JML_REG_TMP0);
      jit_sti_p (&caml_trapsp, JML_REG_SP);
      JMLIT_save_env ();
      pc++;
      break;
    case POPTRAP:
      caml_jit_generate_check_stack_and_signals (JML_REG_TMP0, pc - 1);
      //. caml_trapsp = Trap_link(sp) ## ie sp[1] thru tmp1
      jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 1 * WORDSIZE);
      jit_sti_p (&caml_trapsp, JML_REG_TMP1);
      //. sp += 4w
      jit_addi_p (JML_REG_SP, JML_REG_SP, 4 * WORDSIZE);
      break;
    case RAISE:
      /* save pc and acc and sp and env; return MLJSTATE_RAISE */
      jit_movi_l (JML_REG_TMP1, pc);
      jit_stxi_l (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);
      jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
      JMLIT_save_env ();
      jit_sti_p (&caml_extern_sp, JML_REG_SP);
      jit_movi_i (JIT_RET, MLJSTATE_RAISE);
      jit_ret ();
      break;
    case CHECK_SIGNALS:
      caml_jit_generate_check_stack_and_signals (JML_REG_TMP0, pc);
      break;

      /**
	 in interp.c Setup_for_c_call is
	 { saved_pc = pc; *--sp = env; caml_extern_sp = sp; }
      **/
#define JML_CCALL_PROLOG() do    {/* like Setup_for_c_call */   \
   /* save savebytepc */                                        \
   jit_movi_p(JML_REG_TMP0, pc);                                \
   jit_stxi_p(JML_OFF_SAVEDBYTEPC, JML_REG_STATE, JML_REG_TMP0);\
   /* save next bytepc */                                       \
   jit_movi_p(JML_REG_TMP1, pc+2);                              \
   jit_stxi_p(JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);     \
   JMLIT_save_env();                                            \
   /* sp--; tmp1 = env; *sp = tmp1; save sp */                  \
   jit_subi_p(JML_REG_SP, JML_REG_SP, 1*WORDSIZE);              \
   jit_ldxi_p(JML_REG_TMP1, JML_REG_STATE, JML_OFF_ENV);        \
   jit_str_p(JML_REG_SP, JML_REG_TMP1);                         \
   jit_sti_p(&caml_extern_sp, JML_REG_SP);                      \
  } while(0)

      /** in interp.c Restore_after_c_call is
          { sp = caml_extern_sp; env = *sp; sp++; }
      **/
#define JML_CCALL_EPILOG(N) do {                                \
  /* acc = retval */                                            \
  jit_movr_p(JML_REG_ACC, JIT_RET);                             \
  /* sp = caml_extern_sp; envtmp2 = *sp; sp ++ */               \
  jit_ldi_p(JML_REG_SP, &caml_extern_sp);                       \
  jit_ldr_p(JML_REG_ENVTMP2, JML_REG_SP);                       \
  jit_addi_p(JML_REG_SP, JML_REG_SP, (N+1)*WORDSIZE);           \
  JMLIT_save_env();                                             \
  jit_sti_p(&caml_extern_sp, JML_REG_SP);                       \
  } while (0)


      // define macro JMLIT_load_double_val to load into floating
      // register FpR the Double_val pointed by a pointer in register
      // AdR -- use tmp0

      // define macro JMLIT_alloc_double_val to allocate into a
      // pointer register tmp0 a double containing the floating point
      // register FpR -- use tmp0 tmp1 tmp2env

#ifdef ARCH_ALIGN_DOUBLE
#define JMLIT_load_double_val(FpR,AdR)  do {			\
    jit_ldr_p(JML_REG_TMP0, (AdR));				\
    jit_stxi_p(JML_OFF_DBLX, JML_REG_STATE, JML_REG_TMP0);	\
    if (sizeof(double)==2*sizeof(void*)) {  			\
 	jit_ldxi_p(JML_REG_TMP0, (AdR), WORDSIZE); 		\
 	jit_stxi_p(JML_OFF_DBLX+WORDSIZE, JML_REG_STATE, 	\
                   JML_REG_TMP0);				\
    };								\
    jit_ldxi_d((FpR), JML_REG_STATE, JML_OFF_DBLX);		\
  } while(0)

#define JMLIT_alloc_double_val(FpR) do {				\
    jit_stxi_d(JML_OFF_DBLX, JML_REG_STATE, (FpR));			\
    caml_jit_generate_alloc_small_const(JML_REG_TMP0,			\
					Double_wosize,Double_tag);	\
    jit_ldxi_l(JML_REG_TMP1, JML_REG_STATE, JML_OFF_DBLX);		\
    jit_str_p(JML_REG_TMP0, JML_REG_TMP1);				\
    if (sizeof(double)==2*sizeof(void*)) {				\
      jit_ldxi_l(JML_REG_TMP1, JML_REG_STATE, JML_OFF_DBLX+WORDSIZE);	\
      jit_stxi_p(WORDSIZE, JML_REG_TMP0, JML_REG_TMP1);			\
    }									\
  } while(0)
#else /* no ARCH_ALIGN_DOUBLE eg on x86 */
#define JMLIT_load_double_val(FpR,AdR) jit_ldr_d((FpR),(AdR))

      /* we have to store the floating register because it is not
         preserved on GC call */
#define JMLIT_alloc_double_val(FpR) do {				\
    jit_stxi_d(JML_OFF_DBLX, JML_REG_STATE, (FpR));			\
    caml_jit_generate_alloc_small_const(JML_REG_TMP0,			\
					Double_wosize,Double_tag);      \
    jit_ldxi_d((FpR), JML_REG_STATE, JML_OFF_DBLX);		        \
    jit_str_d(JML_REG_TMP0, (FpR));					\
  } while(0)
#endif /* ARCH_ALIGN_DOUBLE */


    case C_CALL1:
      num = *pc;
      pc++;
      {
	extern value caml_neg_float (value);
	extern value caml_int_of_float (value);
	extern value caml_float_of_int (value);
	extern value caml_floor_float (value);
#if 0
	if (Primitive (num) == (c_primitive) caml_neg_float) {
	  JMLIT_save_env ();
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
#ifndef jit_negr_d
	  /* older versions of lightning had jit_neg_d instead of jit_negr_d */
	  jit_neg_d (JIT_FPR0, JIT_FPR0);
#else
	  jit_negr_d (JIT_FPR0, JIT_FPR0);
#endif
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	} else
#endif
  if (Primitive (num) == (c_primitive) caml_floor_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_floorr_d_i (JML_REG_TMP0, JIT_FPR0);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
	} else if (Primitive (num) == (c_primitive) caml_int_of_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_truncr_d_i (JML_REG_TMP0, JIT_FPR0);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
#ifdef jit_extr_i_d		/* gnu lightning bug : sometimes this macro dont exist */
	} else if (Primitive (num) == (c_primitive) caml_float_of_int) {
	  JMLIT_save_env ();
	  jit_rshi_l (JML_REG_TMP1, JML_REG_ACC, 1);
	  jit_extr_i_d (JIT_FPR0, JML_REG_TMP1);
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
#endif
	} else {
	  JML_CCALL_PROLOG ();
	  jit_prepare_i (1);
	  jit_pusharg_p (JML_REG_ACC);
	  (void) jit_finish (Primitive (num));
	  JML_CCALL_EPILOG (0);
	};
      };
      break;
    case C_CALL2:
      num = *pc;
      pc++;
      {
	extern value caml_add_float (value, value);
	extern value caml_sub_float (value, value);
	extern value caml_mul_float (value, value);
	extern value caml_div_float (value, value);
	extern value caml_eq_float (value, value);
	extern value caml_neq_float (value, value);
	extern value caml_le_float (value, value);
	extern value caml_lt_float (value, value);
	extern value caml_ge_float (value, value);
	extern value caml_gt_float (value, value);
	if (Primitive (num) == (c_primitive) caml_add_float) {
	  JMLIT_save_env ();
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_addr_d (JIT_FPR0, JIT_FPR0, JIT_FPR1);
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_sub_float) {
	  JMLIT_save_env ();
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_subr_d (JIT_FPR0, JIT_FPR0, JIT_FPR1);
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_mul_float) {
	  JMLIT_save_env ();
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_mulr_d (JIT_FPR0, JIT_FPR0, JIT_FPR1);
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_div_float) {
	  JMLIT_save_env ();
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_divr_d (JIT_FPR0, JIT_FPR0, JIT_FPR1);
	  JMLIT_alloc_double_val (JIT_FPR0);
	  jit_movr_p (JML_REG_ACC, JML_REG_TMP0);
	  JMLIT_restore_env ();
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_eq_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_eqr_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_neq_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_ner_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_le_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_ler_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_lt_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_ltr_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_ge_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_ger_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else if (Primitive (num) == (c_primitive) caml_gt_float) {
	  JMLIT_load_double_val (JIT_FPR0, JML_REG_ACC);
	  jit_ldxi_p (JML_REG_TMP1, JML_REG_SP, 0 * WORDSIZE);
	  JMLIT_load_double_val (JIT_FPR1, JML_REG_TMP1);
	  jit_gtr_d (JML_REG_TMP0, JIT_FPR0, JIT_FPR1);
	  jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, 1);
	  jit_ori_l (JML_REG_ACC, JML_REG_TMP0, 1);
	  jit_addi_l (JML_REG_SP, JML_REG_SP, WORDSIZE);
	} else {
	  JML_CCALL_PROLOG ();
	  jit_prepare_i (2);
	  jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 1 * WORDSIZE);
	  jit_pusharg_p (JML_REG_TMP0);
	  jit_pusharg_p (JML_REG_ACC);
	  (void) jit_finish (Primitive (num));
	  JML_CCALL_EPILOG (1);
	}
      }
      break;
    case C_CALL3:
      num = *pc;
      pc++;
      JML_CCALL_PROLOG ();
      jit_prepare_i (3);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 2 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 1 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_pusharg_p (JML_REG_ACC);
      (void) jit_finish (Primitive (num));
      JML_CCALL_EPILOG (2);
      break;
    case C_CALL4:
      num = *pc;
      pc++;
      JML_CCALL_PROLOG ();
      jit_prepare_i (4);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 3 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 2 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 1 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_pusharg_p (JML_REG_ACC);
      (void) jit_finish (Primitive (num));
      JML_CCALL_EPILOG (3);
      break;
    case C_CALL5:
      num = *pc;
      pc++;
      JML_CCALL_PROLOG ();
      jit_prepare_i (5);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 4 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 3 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 2 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_ldxi_p (JML_REG_TMP0, JML_REG_SP, 1 * WORDSIZE);
      jit_pusharg_p (JML_REG_TMP0);
      jit_pusharg_p (JML_REG_ACC);
      (void) jit_finish (Primitive (num));
      JML_CCALL_EPILOG (4);
      break;
    case C_CALLN:
      {
	int nargs = *pc++;
	num = *pc;
	pc++;
	//. sp--; *sp = acc;
	jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_str_p (JML_REG_SP, JML_REG_ACC);
	JML_CCALL_PROLOG ();
	jit_addi_p (JML_REG_TMP0, JML_REG_SP, WORDSIZE);
	jit_movi_l (JML_REG_TMP1, nargs);
	jit_prepare_i (2);
	jit_pusharg_l (JML_REG_TMP1);
	jit_pusharg_p (JML_REG_TMP0);
	(void) jit_finish (Primitive (num));
	JML_CCALL_EPILOG (nargs);
	break;
      };
    case CONST0:
      jit_movi_l (JML_REG_ACC, Val_int (0));
      break;
    case CONST1:
      if (pc[0] == ADDINT) {
	JML_DBGPRINTF ("peephole optimisation of CONST1&ADDINT pc.%p=prog+%d",
		       pc, pc - prog);
	// accu = (value) ((long)(Val_int(1)-1) + (long) *sp++);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_addi_l (JML_REG_ACC, JML_REG_TMP1, Val_int (1) - 1);
	pc += 2;
	nbbci++;
      } else
	jit_movi_l (JML_REG_ACC, Val_int (1));
      break;
    case CONST2:
      if (pc[0] == ADDINT) {
	JML_DBGPRINTF ("peephole optimisation of CONST2&ADDINT pc.%p=prog+%d",
		       pc, pc - prog);
	// accu = (value) ((long)(Val_int(2)-1) + (long) *sp++);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_addi_l (JML_REG_ACC, JML_REG_TMP1, Val_int (2) - 1);
	pc += 2;
	nbbci++;
      } else
	jit_movi_l (JML_REG_ACC, Val_int (2));
      break;
    case CONST3:
      if (pc[0] == ADDINT) {
	JML_DBGPRINTF ("peephole optimisation of CONST3&ADDINT pc.%p=prog+%d",
		       pc, pc - prog);
	// accu = (value) ((long)(Val_int(3)-1) + (long) *sp++);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_addi_l (JML_REG_ACC, JML_REG_TMP1, Val_int (3) - 1);
	pc += 2;
	nbbci++;
      } else
	jit_movi_l (JML_REG_ACC, Val_int (3));
      break;
#define JML_PUSH_ACC() do {                             \
    /* --sp; *sp = acc */                               \
    jit_subi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);       \
    jit_str_p(JML_REG_SP, JML_REG_ACC);                 \
  } while(0)
    case PUSHCONST0:
      JML_PUSH_ACC ();
      jit_movi_l (JML_REG_ACC, Val_int (0));
      break;
    case PUSHCONST1:
      if (pc[0] == ADDINT) {
	JML_DBGPRINTF
	  ("peephole optimisation of PUSHCONST1&ADDINT pc.%p=prog+%d", pc,
	   pc - prog);
	//// sp[-1] = accu; accu = (value) ((long)Val_int(1) - 1) + acc
	jit_stxi_l (-WORDSIZE, JML_REG_SP, JML_REG_ACC);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, Val_int (1) - 1);
	pc += 1;
	nbbci++;
	JML_DBGPRINTF ("peepedhole pc.%p nbbci:%d", pc, nbbci);
      } else {
	JML_PUSH_ACC ();
	jit_movi_l (JML_REG_ACC, Val_int (1));
      };
      break;
    case PUSHCONST2:
      if (pc[0] == ADDINT) {
	/// sp[-1] = accu; 
	/// accu = (value)((long) Val_int(2) + (long) acc -1)
	JML_DBGPRINTF
	  ("peephole optimisation of PUSHCONST2&ADDINT pc.%p=prog+%d", pc,
	   pc - prog);
	//// sp[-1] = accu; accu = (value) ((long)Val_int(2) - 1) + acc
	jit_stxi_l (-WORDSIZE, JML_REG_SP, JML_REG_ACC);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, Val_int (2) - 1);
	pc += 1;
	nbbci++;
	JML_DBGPRINTF ("peepedhole pc.%p nbbci:%d", pc, nbbci);
      } else {
	JML_PUSH_ACC ();
	jit_movi_l (JML_REG_ACC, Val_int (2));
      }
      break;
    case PUSHCONST3:
      if (pc[0] == ADDINT) {
	JML_DBGPRINTF
	  ("peephole optimisation of PUSHCONST3&ADDINT pc.%p=prog+%d", pc,
	   pc - prog);
	//// sp[-1] = accu; accu = (value) ((long)Val_int(3) - 1) + acc
	jit_stxi_l (-WORDSIZE, JML_REG_SP, JML_REG_ACC);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, Val_int (3) - 1);
	pc += 1;
	nbbci++;
	JML_DBGPRINTF ("peepedhole pc.%p nbbci:%d", pc, nbbci);
      } else {
	JML_PUSH_ACC ();
	jit_movi_l (JML_REG_ACC, Val_int (3));
      }
      break;
    case PUSHCONSTINT:
      if (pc[1] == ADDINT) {
	num = pc[0];
	JML_DBGPRINTF
	  ("peephole optimisation of PUSHCONSTINT#%d&ADDINT pc.%p=prog+%d",
	   num, pc, pc - prog);
	//// sp[-1] = accu; accu = (value) ((long)Val_int(num) - 1) + acc
	jit_stxi_l (-WORDSIZE, JML_REG_SP, JML_REG_ACC);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, Val_int (num) - 1);
	pc += 2;
	nbbci++;
	JML_DBGPRINTF ("peepedhole pc.%p nbbci:%d", pc, nbbci);
	break;
      } else
	JML_PUSH_ACC ();
      /* failthrough */
    case CONSTINT:
      num = *pc;
      JML_DBGPRINTF ("CONSTINT %d jitpc %p", num, jit_get_label ());
      if (pc[1] == ADDINT) {
	JML_DBGPRINTF
	  ("peephole optimisation of CONSTINT#%d&ADDINT pc.%p=prog+%d", num,
	   pc, pc - prog);
	// accu = (value) ((long)(Val_int(num)-1) + (long) *sp++);
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_addi_l (JML_REG_ACC, JML_REG_TMP1, Val_int (num) - 1);
	pc += 2;
	nbbci++;
	JML_DBGPRINTF ("peepedhole pc.%p nbbci:%d", pc, nbbci);
      } else {
	jit_movi_l (JML_REG_ACC, Val_int (num));
	pc++;
      };
      break;
    case NEGINT:
      jit_rsbi_l (JML_REG_ACC, JML_REG_ACC, 2);
      break;
    case ADDINT:
      //. tmp1 = *sp; sp++; tmp1--; acc = acc + tmp1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_subi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addr_p (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      break;
    case SUBINT:
      //. tmp1 = *sp; sp++; tmp1--; acc = acc - tmp1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_subi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_subr_p (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      break;
    case MULINT:
      //. tmp1 = *sp; acc >>= 1; tmp1 >>1 ; sp++; acc = (acc*tmp1)<<1 +1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_rshi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_mulr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      jit_lshi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;
    case DIVINT:
      {
	jit_insn *testref = 0;
	JML_DBGPRINTF ("DIVINT jitpc %x start", (int) (jit_get_label ()));
	//. tmp1 = *sp; sp++; tmp1>>=1; if (tmp1!=0) goto next;
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
	testref = jit_bnei_l (jit_forward (), JML_REG_TMP1, 0);
	JML_CCALL_PROLOG ();
	jit_calli (caml_raise_zero_divide);
	//. next: acc>>=1; acc = (((long) acc / tmp1) << 1) + 1);
	jit_patch (testref);
	jit_rshi_l (JML_REG_ACC, JML_REG_ACC, 1);
	jit_divr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
	jit_lshi_l (JML_REG_ACC, JML_REG_ACC, 1);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
	JML_DBGPRINTF ("DIVINT jitpc %x end", (int) (jit_get_label ()));
	break;
      };
    case MODINT:
      {
	jit_insn *testref = 0;
	//. tmp1 = *sp; sp++; tmp1>>=1; if (tmp1!=val_long(0)) goto next;
	jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
	jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
	testref = jit_bnei_l (jit_forward (), JML_REG_TMP1, 0);
	JML_CCALL_PROLOG ();
	jit_calli (caml_raise_zero_divide);
	//. next: acc>>=1; acc = (((long) acc / tmp1) << 1) + 1);
	jit_patch (testref);
	jit_rshi_l (JML_REG_ACC, JML_REG_ACC, 1);
	jit_modr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
	jit_lshi_l (JML_REG_ACC, JML_REG_ACC, 1);
	jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
	break;
      };
    case ANDINT:
      //. tmp1 = *sp; sp++; acc = acc & tmp1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_andr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      break;
    case ORINT:
      //. tmp1 = *sp; sp++; acc = acc | tmp1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_orr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      break;
    case XORINT:
      //. tmp1 = *sp; sp++; acc = acc ^ tmp1|1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_xorr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      jit_ori_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;
    case LSLINT:
      //. tmp1 = *sp; sp++; tmp1 >>= 1; acc--; acc= (acc<<tmp1)+1;
      jit_ldr_l (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_subi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_lshr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;
    case LSRINT:
      //. tmp1 = *sp; sp++; tmp1 >>= 1; acc--; acc= (acc<<tmp1)|1;
      jit_ldr_l (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_subi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_rshr_ul (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      jit_ori_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;
    case ASRINT:
      //. tmp1 = *sp; sp++; tmp1 >>= 1; acc--; acc= (acc<<tmp1)|1;
      jit_ldr_l (JML_REG_TMP1, JML_REG_SP);
      jit_addi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_rshi_l (JML_REG_TMP1, JML_REG_TMP1, 1);
      jit_subi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_rshr_l (JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);
      jit_ori_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;
#define JML_COMPARE(JitComp) do {                               \
   JML_DBGPRINTF("compare bypc %p jitpc %p " #JitComp,          \
                 pc, (void*) jit_get_label());                  \
   /*tmp1= *sp; sp++; acc= acc compare tmp1; acc <<=1; acc++*/  \
   jit_ldr_l(JML_REG_TMP1, JML_REG_SP);                         \
   jit_addi_p(JML_REG_SP, JML_REG_SP, WORDSIZE);                \
   JitComp(JML_REG_ACC, JML_REG_ACC, JML_REG_TMP1);             \
   jit_lshi_l(JML_REG_ACC, JML_REG_ACC, 1);                     \
   jit_addi_l(JML_REG_ACC, JML_REG_ACC, 1);                     \
 } while(0);
    case EQ:
      JML_COMPARE (jit_eqr_l);
      break;
    case NEQ:
      JML_COMPARE (jit_ner_l);
      break;
    case LTINT:
      JML_COMPARE (jit_ltr_l);
      break;
    case LEINT:
      JML_COMPARE (jit_ler_l);
      break;
    case GTINT:
      JML_COMPARE (jit_gtr_l);
      break;
    case GEINT:
      JML_COMPARE (jit_ger_l);
      break;
    case ULTINT:
      JML_COMPARE (jit_ltr_ul);
      break;
    case UGEINT:
      JML_COMPARE (jit_ger_ul);
      break;
#define JML_TEST_BRANCH(JitBranch) do {                         \
   jit_insn* testref=0;                                         \
   int cnum = *(pc++), off = *pc;                               \
   JML_DBGPRINTF("testbr cnum%d off%d " #JitBranch " jitpc%#x", \
		 cnum, off, (int)jit_get_label());              \
   testref = JitBranch(jit_forward(), JML_REG_ACC,              \
                       Val_long(cnum));                         \
   JML_GENERATE_BRANCH(JML_REG_TMP0, pc + off);                 \
   jit_patch(testref); pc++;     } while (0)
      /* beware that bytecode compare constant to acc while jit
         compare acc to constant, so the compare is reversed (and the
         machine jump should be done when the bytecode-branching
         condition is not met) ! */
    case BEQ:
      JML_TEST_BRANCH (jit_bnei_l);
      break;
    case BNEQ:
      JML_TEST_BRANCH (jit_beqi_l);
      break;
    case BLTINT:		/* if const < acc goto target */
      JML_TEST_BRANCH (jit_blei_l);
      break;
    case BLEINT:		/* if const <= acc goto target */
      JML_TEST_BRANCH (jit_blti_l);
      break;
    case BGTINT:		/* if const > acc goto target */
      JML_TEST_BRANCH (jit_bgei_l);
      break;
    case BGEINT:		/* if const >= acc goto target */
      JML_TEST_BRANCH (jit_bgti_l);
      break;
    case BULTINT:		/* if const  <(unsigned)  acc  goto target */
      /* since we have an unsigned compare, we need to convert the acc
         into an unsigned integer */
      {
	unsigned cnum = (unsigned) *(pc++);
	int off = *pc;
	jit_insn *utestref = 0;
	/* convert ACC into unsigned inside TMP1 (ie Unsigned_long_val)  */
	/// tmp1 = acc >> 1 (unsigned)
	jit_rshi_ul (JML_REG_TMP1, JML_REG_ACC, 1);
	utestref = jit_blei_ul (jit_forward (), JML_REG_TMP1, (cnum));
	JML_GENERATE_BRANCH (JML_REG_TMP0, pc + off);
	jit_patch (utestref);
	pc++;
      }
      break;
    case BUGEINT:		/* if const  >=(unsigned)  acc  goto target */
      /* since we have an unsigned compare, we need to convert the acc
         into an unsigned integer */
      {
	unsigned cnum = (unsigned) *(pc++);
	int off = *pc;
	jit_insn *utestref = 0;
	/* convert ACC into unsigned inside TMP1 (ie Unsigned_long_val)  */
	/// tmp1 = acc >> 1 (unsigned)
	jit_rshi_ul (JML_REG_TMP1, JML_REG_ACC, 1);
	utestref = jit_bgti_ul (jit_forward (), JML_REG_TMP1, (cnum));
	JML_GENERATE_BRANCH (JML_REG_TMP0, pc + off);
	jit_patch (utestref);
	pc++;
      }
      break;
    case OFFSETINT:
      num = *(pc++);
      jit_addi_l (JML_REG_ACC, JML_REG_ACC, num << 1);
      break;
    case OFFSETREF:
      num = *(pc++);
      //. tmp1 = acc[0]; tmp1 += num<<1; acc[0]=tmp1; acc=Val_unit
      jit_ldr_l (JML_REG_TMP1, JML_REG_ACC);
      jit_addi_l (JML_REG_TMP1, JML_REG_TMP1, num << 1);
      jit_str_l (JML_REG_ACC, JML_REG_TMP1);
      jit_movi_l (JML_REG_ACC, Val_unit);
      break;
    case ISINT:
      jit_andi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_lshi_l (JML_REG_ACC, JML_REG_ACC, 1);
      jit_addi_l (JML_REG_ACC, JML_REG_ACC, 1);
      break;



      /*** object-oriented operations 

      the "vtable" format has greatly changed between ocaml 3.07 and
      (future) 3.08 - it is now a dichotomical table, with a (single)
      cache at each call site (implemented as a skipped slot in the
      bytecode). the code below matches the code in
      csl/byterun/interp.c cvs.rev. 1.87

      ****/

	/*** 
	     the method dichotomy is used twice; the equivalent C code is 
		         int li = 3, hi = Field(meths,0), mi;
		         while (li < hi) {
		           mi = ((li+hi) >> 1) | 1;
		           if (accu < Field(meths,mi)) hi = mi-2;
		           else li = mi;
		         }
		         accu = Field (meths, li-1);
             we need to keep li,hi,mi,accu,meths in registers
             we suppose that accu is in JML_REG_ACC and that meths is in JML_REG_TMP0
             we use JML_REG_TMP1 for li JML_REG_TMP2ENV for hi
             since sp is not needed above, we save JML_REG_SP and use it for mi, 
             which we also save in js_tag of the current state, 
             and final li is saved in js_wosize
             (because lightning gives us only 6 registers)
             the code below is tricky
	***/


    case GETMETHOD:
      /** compile time expansion of acc = Lookup(sp[0],accu) where
	  Lookup(obj,lab) is Field(Field(obj,0),Int_val(lab)), so we do
	  accu = Field(Field(sp[0],0),Int_val(accu))
      */
      JML_DBGPRINTF ("GETMETHOD pc=%p", pc);
      //. tmp1 = sp[0]; tmp1 = Field(tmp1,0)  ie *tmp1
      jit_ldr_p (JML_REG_TMP1, JML_REG_SP);
      jit_ldr_p (JML_REG_TMP1, JML_REG_TMP1);
      //. tmp0 = Int_val(accu) ie accu>>1
      jit_rshi_l (JML_REG_TMP0, JML_REG_ACC, 1);
      //. tmp0 = tmp0 << LOGWORDSIZE
      jit_lshi_l (JML_REG_TMP0, JML_REG_TMP0, LOG2WORDSIZE);
      //. accu = Field(tmp1,tmp0) ie tmp1[tmp0]
      jit_ldxr_p (JML_REG_ACC, JML_REG_TMP1, JML_REG_TMP0);
      break;

      /* define CAML_METHOD_CACHE as it is in csl/byterun/interp.c */
#define CAML_METHOD_CACHE

    case GETPUBMET:
      /* accu == object, pc[0] == tag, pc[1] == cache */
      JML_DBGPRINTF ("GETPUBMET pc=%p", pc);
#ifdef CAML_METHOD_CACHE
      {
	/* functions defined in $OCAMLTOPDIR/byterun/obj.c */
	extern value caml_cache_public_method (value meths, value tag,
					       value * cache);
	extern value caml_cache_public_method2 (value * meths, value tag,
						value * cache);
	long valtag;
	value *cacheptr = 0;
	jit_insn *cmpref = 0, *hitref = 0;
	JMLIT_save_env ();
	//. tmp0 = Field(accu,0)   /// ie meths
	jit_ldr_p (JML_REG_TMP0, JML_REG_ACC);
	//. --sp; *sp = accu;
	jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
	jit_str_p (JML_REG_SP, JML_REG_ACC);
	//. accu = Val_int(*pc++) ie the tag
	valtag = Val_int (*pc++);
	jit_movi_l (JML_REG_ACC, valtag);
	cacheptr = (value *) pc;
	pc++;
	JML_DBGPRINTF ("GETPUBMET method cache valtag=%ld cacheptr=%p",
		       valtag, cacheptr);
	//////. ofs = *cacheptr & Field(meths,1);
	//////. if (*(value*)(((char*)&Field(meths,3)) + ofs) == accu)
	//. tmp1 = meths[1]
	jit_ldxi_p (JML_REG_TMP1, JML_REG_TMP0, 1 * WORDSIZE);
	//. tmp2 = (*cacheptr) & tmp1;  //// ie ofs
	jit_ldi_l (JML_REG_TMP2ENV, cacheptr);
	jit_andr_l (JML_REG_TMP2ENV, JML_REG_TMP2ENV, JML_REG_TMP1);
	//. tmp2 = (tmp2 + 3*words + meths); tmp1 = *tmp2
	jit_addi_l (JML_REG_TMP2ENV, JML_REG_TMP2ENV, 3 * WORDSIZE);
	jit_addr_l (JML_REG_TMP2ENV, JML_REG_TMP2ENV, JML_REG_TMP0);
	jit_ldr_p (JML_REG_TMP1, JML_REG_TMP2ENV);
	//. if acc != tmp1 then goto miss
	cmpref = jit_bner_i (jit_forward (), JML_REG_TMP1, JML_REG_ACC);
	//. acc = tmp2[-1w]
	jit_ldxi_l (JML_REG_ACC, JML_REG_TMP2ENV, -1 * WORDSIZE);
	hitref = jit_jmpi (jit_forward ());
	jit_ori_l (JML_REG_TMP0, JML_REG_TMP0, 0);	//.. a kind of nop
	//. miss:
	jit_patch (cmpref);
	//. call  caml_cache_public_method (tmp0, valtag, cacheptr)
	jit_sti_p (&caml_extern_sp, JML_REG_SP);
	jit_prepare_i (3);
	//. tmp1 = cacheptr
	jit_movi_p (JML_REG_TMP1, cacheptr);
	jit_pusharg_p (JML_REG_TMP1);
	jit_movi_l (JML_REG_TMP1, valtag);
	jit_pusharg_l (JML_REG_TMP1);
	jit_pusharg_p (JML_REG_TMP0);
	/* don't need to save REG_ACC - it is the returned value */
	jit_finish (caml_cache_public_method);
	jit_movr_p (JML_REG_ACC, JIT_RET);
	jit_ldi_p (JML_REG_SP, &caml_extern_sp);
	jit_patch (hitref);
	JMLIT_restore_env ();
	break;
      }
#else /*no CAML_METHOD_CACHE */
      /* sp--; *sp = accu; accu = Val_int(*pc); pc += 2 */
      jit_subi_p (JML_REG_SP, JML_REG_SP, WORDSIZE);
      jit_str_p (JML_REG_SP, JML_REG_ACC);
      jit_movi_l (JML_REG_ACC, Val_int (*pc));
      pc += 2;
      /* Failthrough */
#endif /*CAML_METHOD_CACHE */

    case GETDYNMET:
      {
	/* function defined in $OCAMLTOPDIR/byterun/obj.c */
	extern value caml_get_public_method (value obj, value tag);
	JML_DBGPRINTF ("GETDYNMET pc=%p", pc);
	/* accu == tag, sp[0] == object,  */
	//. call  caml_get_public_method (sp[0], accu) ---> result in accu
	JMLIT_save_env ();
	//. tmp0 = sp[0]
	jit_ldr_l (JML_REG_TMP0, JML_REG_SP);
	jit_sti_p (&caml_extern_sp, JML_REG_SP);
	jit_prepare_i (2);
	jit_pusharg_l (JML_REG_ACC);
	jit_pusharg_l (JML_REG_TMP0);
	jit_finish (caml_get_public_method);
	jit_movr_p (JML_REG_ACC, JIT_RET);
	jit_ldi_p (JML_REG_SP, &caml_extern_sp);
	JMLIT_restore_env ();
      }
      break;


    case STOP:
      jit_movi_p (JML_REG_TMP1, pc);
      jit_stxi_l (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP1);
      jit_stxi_p (JML_OFF_ACCU, JML_REG_STATE, JML_REG_ACC);
      jit_sti_p (&caml_extern_sp, JML_REG_SP);
      jit_movi_i (JIT_RET, MLJSTATE_RETURN);
      JMLIT_save_env ();
      jit_ret ();
      JML_DBGPRINTF ("stopping jit translation at STOP %#x ..", (int) pc);
      JML_DBGPRINTF (".. in codeblock %#x - %#x) offset %d (codesize %d)",
		     (int) cblock->cb_byprog,
		     (int) ((char *) cblock->cb_byprog + cblock->cb_bysize),
		     pc - cblock->cb_byprog, cblock->cb_bysize);
      goto stop_generation;
    case EVENT:
      caml_fatal_error_arg
	("ocaml jitinterp don't support EVENT bytecode yet at %p\n",
	 (char *) pc);
    case BREAK:
      caml_fatal_error_arg
	("ocaml jitinterp don't support BREAK bytecode yet at %p\n",
	 (char *) pc);
    default:
      caml_fatal_error_arg ("Fatal error: bad opcode (%lx)\n",
			    (char *) curr_instr);
    };
    JML_DBGPRINTF ("end switch gen pc.%p nbgen.%d\n", pc, nbgen);
    nbgen++;
  }				/* end of generation loop */

stop_generation:
  JML_DBGPRINTF ("stop generation pc=%p - %s\n", pc, caml_instr_string (pc));
  JML_DBGPRINTF ("epilog (unused) jitpc %p", jit_get_label ());
  /* generate the epilog (which should never be executed) */
  jit_movi_i (JIT_RET, MLJSTATE_ABEND);
  jit_movi_l (JML_REG_TMP0, pc);
  jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
  jit_ret ();
  jit_nop ();
  jit_nop ();
  /* following instructions are useless, except for understanding which
     machine registers are actually used, by glancing the generated
     machine code */
  jit_movi_l (JML_REG_TMP0, 0x800);
  jit_movi_l (JML_REG_TMP1, 0x801);
  jit_movi_l (JML_REG_TMP2ENV, 0x802);
  jit_movi_l (JML_REG_ACC, 0xa00);
  jit_movi_l (JML_REG_STATE, 0x500);
  jit_movi_l (JML_REG_SP, 0x600);
  jit_nop ();
  jit_nop ();
  cblock->cb_curinstr = jit_get_label ();
  jit_nop ();
  JML_DBGPRINTF ("end epilog (unused) jitpc %p", cblock->cb_curinstr);
  /* resolve forward references for jumps */
  {
    int i = 0;
    for (i = 0; i < cblock->cb_forwards->jf_nb; i++) {
      void *ref = cblock->cb_forwards->jf_ent[i].jfj_ref;
      code_t bytdest = cblock->cb_forwards->jf_ent[i].jfj_dest;
      jit_insn *machdest = caml_jit_get_pc (bytdest);
      jit_insn *realmachdest = machdest;
      JML_DBGPRINTF ("forwardref#%d %p bytedest %p machdest %p", i, ref,
		     bytdest, machdest);
      if (!machdest) {
	/* if we have no machinecode for the destination, we have to
	   generate a stub which loads the js_bytepc of the state and
	   jump to it */
	JML_DBGPRINTF ("no machdest so generate stub for bytedest %p",
		       bytdest);
	/* if reached end of chunk, make a new one */
	if ((char *) (cblock->cb_curinstr + 32 * sizeof (long))
	    >= (char *) chunk->ch_end) {
	  struct caml_jit_codechunk_st *newchunk = 0;
	  newchunk = caml_jit_new_chunk (cblock, 500 * sizeof (long));
	  chunk = newchunk;
	  cblock->cb_curinstr = chunk->ch_instrzone;
	  /* on PowerPC, jit_set_ip actually may generate some kind of
	     prolog code */
	  JML_DBGPRINTF ("set_ip %p", chunk->ch_instrzone);
	  (void) jit_set_ip (chunk->ch_instrzone);
	  cblock->cb_curinstr = jit_get_label ();
	};
	/* generate the stub */
	// jit_raw_set_ip (cblock->cb_curinstr);
	jit_get_label () = cblock->cb_curinstr;
	machdest = cblock->cb_curinstr;
	//. tmp0 = bytdest;
	jit_movi_l (JML_REG_TMP0, bytdest);
	jit_stxi_p (JML_OFF_BYTEPC, JML_REG_STATE, JML_REG_TMP0);
	//. goto jumpbytepc;
	(void) jit_jmpi (cblock->cb_jumppcref);
	jit_nop ();
	cblock->cb_curinstr = jit_get_label ();
      };
      if (cblock->cb_forwards->jf_ent[i].jfj_jump) {
	// jit_raw_set_ip (machdest);
	jit_get_label () = machdest;
	jit_patch ((jit_insn *) ref);
      } else
	*(void **) ref = machdest;
      JML_DBGPRINTF ("flush code %p - %p", ref,
		     (char *) ref + 8 * sizeof (int));
      jit_flush_code (ref, (char *) ref + 8 * sizeof (int));
      /* if the machdest is not a real one, it is a stub, and the
         forward branch should not be forgotten, but rewritten at next generation */
      if (realmachdest)
	cblock->cb_forwards->jf_ent[i].jfj_dest = 0;
    }
  }
  /* compact the forward references */
  {
    int i /* index before compaction */  = 0;
    int j /*index after compaction */  = 0;
    while (i < cblock->cb_forwards->jf_nb) {
      code_t bytdest = cblock->cb_forwards->jf_ent[i].jfj_dest;
      if (bytdest)
	cblock->cb_forwards->jf_ent[j++] = cblock->cb_forwards->jf_ent[i];
      i++;
    };
    cblock->cb_forwards->jf_nb = j;
    cblock->cb_forwards->jf_ent[j].jfj_dest = 0;
  }
  // flush the generated code in all the chunks
  {
    struct caml_jit_codechunk_st *ch = 0;
    for (ch = firstchunk; ch; ch = ch->ch_next) {
      JML_DBGPRINTF ("flush code ch %p from %p to %p", ch,
		     (char *) (ch->ch_instrzone), (char *) (ch->ch_end) - 1);
      jit_flush_code ((char *) (ch->ch_instrzone), (char *) (ch->ch_end) - 1);
    }
  }
#ifdef DEBUG
  if (caml_trace_flag) {
    jit_insn *nativeprev = 0;
    code_t bpc = 0;
    extern void disassemble (FILE *, void *, void *);
    FILE *bfil = 0;
    FILE *disfil = 0;
    char disfilnam[300];
    char dismsg[200];
    extern char caml_jit_disname[];
    static int disfilcnt;
    char *bfilnam = 0;
    /*** to ease debugging, we may generate a file of lines like
          camljitbp <bytecodeptr> <bytecodeoffset> <machinecode>
     this file might then be sourced by gdb
     If the filename starts with | it is a piped command
     ***/
    disfilcnt++;
    disfil = 0;
    bfilnam = getenv ("OCAMLJITPOINT");
    if (bfilnam) {
      if (bfilnam[0] == '!' || bfilnam[0] == '|')
	bfil = popen (bfilnam + 1, "w");
      else
	bfil = fopen (bfilnam, "w");
      if (bfil)
	JML_DBGPRINTF ("breakpoint file %s", bfilnam);
    };
    memset (disfilnam, 0, sizeof (disfilnam));
    if (caml_jit_disname[0]) {
      char oldfilnam[300];
      snprintf (disfilnam, sizeof (disfilnam) - 2, "%s_%03d",
		caml_jit_disname, disfilcnt);
      snprintf (oldfilnam, sizeof (oldfilnam), "%s~", disfilnam);
      (void) rename (disfilnam, oldfilnam);
      errno = 0;
      disfil = fopen (disfilnam, "w");
      if (!disfil)
	fprintf (stderr, "jitinterp cannot open %s for disassembly - %s\n",
		 disfilnam, strerror (errno));
    };
    if (disfil) {
      time_t nowt = time (0);
      JML_DBGPRINTF ("disassembly into file %s chunk %p block %p",
		     disfilnam, chunk, cblock);
      fprintf (disfil,
	       "file %s generated by pid %d chunk %p block %p at %s\n",
	       disfilnam, (int) getpid (), chunk, cblock, ctime (&nowt));
      fprintf (disfil, "*** disassembly of jit translated code %p - %p\n",
	       chunk->ch_instrzone, jit_get_ip ().ptr);
    };
    nativeprev = chunk->ch_instrzone;
    snprintf (dismsg, sizeof (dismsg), "prolog %p of block", nativeprev);
    if (bfil) {
      fprintf (bfil, "camljumpbc %#lx %d %#lx %#lx\n",
	       (long) cblock->cb_jumppcref, cblock->cb_rank,
	       (long) cblock->cb_byprog,
	       (long) cblock->cb_byprog + cblock->cb_bysize);
      fflush (bfil);
    };
    for (bpc = cblock->cb_byprog;
	 (char *) bpc < (char *) cblock->cb_byprog + cblock->cb_bysize;
	 bpc++) {
      jit_insn *nativebpc = caml_jit_get_pc (bpc);
      if (nativebpc) {
	if (bfil) {
	  fprintf (bfil, "camljitbp %#lx %d %#lx\n",
		   (long) bpc, bpc - prog, (long) nativebpc);
	  fflush (bfil);
	};
	if (disfil) {
	  caml_jit_disassemble (disfil, dismsg, nativeprev, nativebpc);
	  putc ('\n', disfil);
	  fflush (disfil);
	};
	snprintf (dismsg, sizeof (dismsg), "bytecode %#lx @%d : %s",
		  (long) bpc, bpc - prog, caml_instr_string (bpc));
	nativeprev = nativebpc;
      };
    };
    if (bfil) {
      if (bfilnam[0] == '!' || bfilnam[0] == '|')
	pclose (bfil);
      else
	fclose (bfil);
      JML_DBGPRINTF ("closed breakpoint file %s", bfilnam);
      bfil = 0;
    };
    if (disfil) {
      snprintf (dismsg, sizeof (dismsg), "generated epilog of block %p",
		cblock);
      caml_jit_disassemble (disfil, dismsg, nativeprev, cblock->cb_curinstr);
      putc ('\n', disfil);
      fflush (disfil);
      fprintf (disfil, "\n end of file %s \n", disfilnam);
      fclose (disfil);
      JML_DBGPRINTF ("end of disassembly in file %s", disfilnam);
    }
  };
  JML_TODEBUGGER_PRINTF ("ENDGEN bl=%d gen=%d", cblock->cb_rank, gencnt);
  if (caml_jit_options.jitopt_to_debugger_file) {
    int ng = 0;
    fflush (caml_jit_options.jitopt_to_debugger_file);
    usleep (500000);
    JML_DBGPRINTF ("sending SIGUSR1 (%d) to self pid %d",
		   SIGUSR1, (int) getpid ());
    kill (getpid (), SIGUSR1);
    JML_DBGPRINTF ("after selfsending SIGUSR1 mypid %d", (int) getpid ());
    if (caml_jit_options.jitopt_from_debugger_file) {
      if (fscanf
	  (caml_jit_options.jitopt_from_debugger_file, "DIDGEN %d\n",
	   &ng) > 1) {
	JML_DBGPRINTF ("got DIDGEN from debugger %d", ng);
	if (ng == gencnt)
	  goto end;
      };
      caml_fatal_error_arg ("jitinterp did not get GEN%d from debugger\n",
			    (void *) gencnt);
    };
  };
end:
  if (caml_jit_options.jitopt_measure_time) {
    long clktick = sysconf (_SC_CLK_TCK);
    times (&genendtms);
    caml_jit_nbgen += nbgen;
    caml_jit_gentime += (double) (((genendtms.tms_utime + genendtms.tms_stime)
				   - (genstarttms.tms_utime +
				      genstarttms.tms_stime))
				  / (double) clktick);
  };
  JML_DBGPRINTF ("end of jit_translate firstchunk%p\n", firstchunk);
#endif /*DEBUG*/
    return firstchunk;
}				// end of caml_jit_translate


/* use the first word of the md5 as a checksum, avoid recomputing the main program code md5 */
static unsigned long
caml_jit_code_checksum (code_t prog, int progsize)
{
  struct MD5Context ctx;
  char md5[16];
#ifdef ARCH_SIXTYFOUR
#define md5toulong(M) ( (((unsigned long) (((unsigned char*)(M))[0])) << 56)   \
                       |(((unsigned long) (((unsigned char*)(M))[1])) << 48)   \
                       |(((unsigned long) (((unsigned char*)(M))[2])) << 40)   \
                       |(((unsigned long) (((unsigned char*)(M))[3])) << 32)   \
                       |(((unsigned long) (((unsigned char*)(M))[4])) << 24)   \
                       |(((unsigned long) (((unsigned char*)(M))[5])) << 16)   \
                       |(((unsigned long) (((unsigned char*)(M))[6])) << 8)    \
                       |(((unsigned long) (((unsigned char*)(M))[7]))))
#else
#define md5toulong(M) ( (((unsigned long) (((unsigned char*)(M))[0])) << 24)   \
                       |(((unsigned long) (((unsigned char*)(M))[1])) << 16)   \
                       |(((unsigned long) (((unsigned char*)(M))[2])) << 8)    \
                       |(((unsigned long) (((unsigned char*)(M))[3]))))
#endif
  if (prog == caml_start_code && progsize == caml_code_size)
    return Max_long & md5toulong (caml_code_md5);
  memset (&ctx, 0, sizeof (ctx));
  memset (md5, 0, sizeof (md5));
  caml_MD5Init (&ctx);
  caml_MD5Update (&ctx, (unsigned char *) prog, progsize);
  caml_MD5Final (md5, &ctx);
  return Max_long & md5toulong (md5);
#undef md5toulong
}





#ifndef DEBUG
static inline
#endif
  int
caml_jit_run (struct caml_jit_state_st *state)
{
  int n = 0;
  void *machinecode = 0;
  volatile struct caml_jit_codeblock_st *cblock = 0;
  typedef int (*routptr_t) (void *);
  Assert (state != 0);
  JML_DBGPRINTF ("jit_run state %p bytepc %p", state, state->js_bytepc);
  cblock = caml_jit_code_block_at_bytecode (state->js_bytepc);
  if (!cblock)
    caml_fatal_error_arg ("ocamljitrun - no code block for bytepc %p\n",
			  (char *) state->js_bytepc);
  Assert (cblock->cb_magic == JIT_CODBL_MAGIC);
  Assert (cblock->cb_firstchunk
	  && cblock->cb_firstchunk->ch_magic == JIT_CHUNK_MAGIC);
  machinecode = cblock->cb_start;
  JML_DBGPRINTF ("run state@%p machpc %p bypc%#x -> natpc%p",
		 state, machinecode,
		 (int) state->js_bytepc, caml_jit_get_pc (state->js_bytepc));
#ifdef DEBUG
  fflush (stdout);
  fflush (stderr);
#endif
  n = (*(routptr_t) (machinecode)) (state);
  JML_DBGPRINTF ("after run got code %d=%#x externsp=%p jsaccu%#lx",
		 n, n, caml_extern_sp, state->js_accu);
#ifdef DEBUG
  fflush (stdout);
  fflush (stderr);
#endif
  return n;
}


void
caml_jit_remove_block (struct caml_jit_codeblock_st *cblock)
{
  code_t pc;
  void *endpc;
  struct caml_jit_codechunk_st *chk = 0, *nextchk = 0;
  JML_DBGPRINTF ("removing block %p", cblock);
  Assert (cblock && cblock->cb_magic == JIT_CODBL_MAGIC);
  /* remove all bytepc -> nativepc associations */
  endpc = (char *) cblock->cb_byprog + cblock->cb_bysize;
  for (pc = cblock->cb_byprog; pc < (code_t) endpc; pc++) {
    void *ad = caml_jit_remove_pc (pc);
    if (ad)
      JML_TODEBUGGER_PRINTF ("remove_instr(%d,%#x,%#x)",
			     pc - (code_t) caml_start_code, (int) pc,
			     (int) ad);
  };
  /* unmap each chunk */
  for (chk = cblock->cb_firstchunk; chk; chk = nextchk) {
    nextchk = chk->ch_next;
    Assert (chk->ch_cblock == cblock);
    Assert (chk->ch_magic == JIT_CHUNK_MAGIC);
    chk->ch_magic = 1;
    JML_DBGPRINTF ("for block %p unmaping chunk %p-%p", cblock, chk,
		   chk->ch_end);
    if (munmap ((void *) chk, (char *) chk->ch_end - (char *) chk)) {
      fprintf (stderr, "ocaml jit cannot unmap chunk %p-%p - %s\n",
	       chk, chk->ch_end, strerror (errno));
      exit (2);
    };
  };
  free (cblock->cb_forwards);
  memset (cblock, 0, sizeof (*cblock));
  free (cblock);
}				/* end of caml_jit_remove_block */


static struct caml_jit_codeblock_st *
caml_jit_block_of_bytecode (code_t prog, asize_t prog_size)
{
  static int blockcounter;
  int num = 0;
  struct caml_jit_codeblock_st *cblock = 0;
  cblock = calloc (1, sizeof (struct caml_jit_codeblock_st));
  cblock->cb_magic = JIT_CODBL_MAGIC;
  cblock->cb_byprog = prog;
  cblock->cb_bysize = prog_size;
  cblock->cb_rank = ++blockcounter;
  cblock->cb_bycheck = caml_jit_code_checksum (prog, prog_size);
  cblock->cb_tbidx = -1;
  caml_jit_register_code_block (cblock);
  JML_DBGPRINTF
    ("make block %p rank%d byprog %#x bysize %d (byprog+bysize=%#x)",
     cblock, cblock->cb_rank, (int) prog, prog_size,
     (int) prog + (int) prog_size);
  num = ((prog_size / 20) + 256) | 0x1f;
  cblock->cb_forwards = calloc (1, sizeof (struct jml_forward_st)
				+ num * sizeof (struct jml_forwardjump_st));
  if (!cblock->cb_forwards)
    caml_fatal_error ("cannot allocate forward table for jit translation");
  cblock->cb_forwards->jf_size = num;
  JML_TODEBUGGER_PRINTF ("MAKEBLOCK %d %#lx %d", cblock->cb_rank,
			 (long) prog, (int) prog_size);
  caml_jit_generate_prologue (cblock);
  return cblock;
}

value
caml_jit_interpret (code_t prog, asize_t prog_size)
{
  struct longjmp_buffer *initial_external_raise = 0;
  volatile struct caml_jit_state_st *prevstate = caml_jitstate;
  volatile struct caml_jit_codeblock_st *cblock = 0;
  volatile struct caml_jit_codechunk_st *chunk = 0;
  int initial_sp_offset = 0;
  /* volatile prevents collapsing initial_local_roots with another
     local variable, like Digital Unix 4.0 C compiler does (wrongly) */
  struct caml__roots_block *volatile initial_local_roots;
  struct longjmp_buffer raise_buf;
  struct caml_jit_state_st state = { 0, 0 };
  if (prog == NULL) {		/* Interpreter is initializing */
    return Val_unit;
  };
  if (!caml_jit_pc_tblptr) {
    Assert (caml_code_size > 0);	/* the code size should already be known */
    caml_jit_init (caml_code_size);
#ifdef DEBUG
#ifndef NO_PTRACE
    JML_DBGPRINTF ("before ptrace_TRACEME");
    if (caml_jit_options.jitopt_to_debugger_file
	&& ptrace (PTRACE_TRACEME, (pid_t) 0, (void *) 0, (void *) 0))
      perror ("ptrace_TRACEME");
#endif /*NO_PTRACE */
#endif
  };
  memset (&state, 0, sizeof (state));
  cblock = caml_jit_code_block_at_bytecode (prog);
  JML_DBGPRINTF
    ("start jitinterpret found cblock %p for byprog %p progsize %ld sp %p",
     cblock, prog, (long) prog_size, caml_extern_sp);
  if (!cblock)
    cblock = caml_jit_block_of_bytecode (prog, prog_size);
  chunk = caml_jit_translate (prog, (struct caml_jit_codeblock_st *) cblock);
  JML_DBGPRINTF ("jit codechunk %p prog %p prog_size %d", chunk, prog,
		 prog_size);
  initial_local_roots = caml_local_roots;
  initial_sp_offset = (char *) caml_stack_high - (char *) caml_extern_sp;
  initial_external_raise = caml_external_raise;
  caml_callback_depth++;
  state.js_accu = (Val_int (0));
  state.js_env = (Atom (0));
  state.js_extra_args = 0;
  state.js_bytepc = prog;
  state.js_savedbytepc = 0;
  caml_jitstate = &state;
#ifdef DEBUG
  JML_TODEBUGGER_PRINTF ("JITSTATE %#x", (int) caml_jitstate);
#endif
  if (sigsetjmp (raise_buf.buf, 0)) {
    caml_local_roots = initial_local_roots;
    state.js_accu = caml_exn_bucket;
    state.js_bytepc = state.js_savedbytepc + 2;
    JML_DBGPRINTF ("got exception bucket %#lx bytepc %#x",
		   state.js_accu, (int) state.js_bytepc);
    goto handle_exception;
  }
  caml_external_raise = &raise_buf;
  for (;;) {
    int stanum = 0;
    JML_DBGPRINTF ("jit before calling  state &%p bytepc %p @%d",
		   &state, state.js_bytepc, state.js_bytepc - prog);
    if (state.js_bytepc == 0)
      caml_fatal_error ("ocaml jitinterp nil bytepc\n");
#ifdef DEBUG
    if (caml_trace_flag)
      caml_disasm_instr (state.js_bytepc);
    fflush (stderr);
    fflush (stdout);
#endif
    JML_DBGPRINTF ("bytepc %#x @%d - %s - native jitpc %p externsp= %p",
		   (int) state.js_bytepc,
		   (code_t) state.js_bytepc - (code_t) caml_start_code,
		   caml_instr_string (state.js_bytepc),
		   caml_jit_get_pc (state.js_bytepc), caml_extern_sp);
#ifdef DEBUG
    if (caml_jit_inscounter > 0) {
      JML_DBGPRINTF ("inscounter %ld jitbytpc %#x @%d - %s",
		     caml_jit_inscounter, (int) caml_jit_bytepc,
		     (int) ((code_t) caml_jit_bytepc -
			    (code_t) caml_start_code),
		     caml_instr_string (caml_jit_bytepc));
    }
    fflush (stderr);
    fflush (stdout);
#endif
    stanum = caml_jit_run (&state);
    JML_DBGPRINTF
      ("interprete jit after callingcode stanum %d, ext.sp %p",
       stanum, caml_extern_sp);
#ifdef DEBUG
    fflush (stderr);
    fflush (stdout);
#endif
    switch (stanum) {
    case MLJSTATE_RETURN:
      caml_external_raise = initial_external_raise;
      caml_callback_depth--;
      JML_DBGPRINTF ("returning caml_callback_depth %d value %ld ext.sp %p",
		     caml_callback_depth, (value) (state.js_accu),
		     caml_extern_sp);
      caml_jitstate = prevstate;
#ifdef DEBUG
      JML_DBGPRINTF ("return jitinterpret cblock %p for prog %p sp %p",
		     cblock, prog, caml_extern_sp);
      fflush (stderr);
      fflush (stdout);
#endif
      return (value) (state.js_accu);
    case MLJSTATE_MODIF:
      {
	JML_DBGPRINTF ("modify dest %p newval %ld", state.js_modifdest,
		       state.js_modifval);
	Modify ((value *) state.js_modifdest, (value) state.js_modifval);
	state.js_accu = (Val_unit);
	state.js_modifdest = 0;
	state.js_modifval = 0;
	break;
      };
    case MLJSTATE_PROCESS_SIGNAL:
      {
	JML_DBGPRINTF ("process signal start caml_extern_sp %p",
		       caml_extern_sp);
	// Setup_for_event
	caml_extern_sp -= 6;
	caml_extern_sp[0] = state.js_accu;
	caml_extern_sp[1] = Val_unit;
	caml_extern_sp[2] = Val_unit;
	caml_extern_sp[3] = (value) (state.js_bytepc);
	caml_extern_sp[4] = state.js_env;
	caml_extern_sp[5] = Val_long (state.js_extra_args);
	caml_something_to_do = 0;
	caml_process_event ();
	// Restore_after_event
	state.js_accu = (caml_extern_sp[0]);
	state.js_bytepc = (code_t) caml_extern_sp[3];
	state.js_env = (caml_extern_sp[4]);
	state.js_extra_args = Long_val (caml_extern_sp[5]);
	caml_extern_sp += 6;
	JML_DBGPRINTF ("process signal end caml_extern_sp %p",
		       caml_extern_sp);
	break;
      };
    case MLJSTATE_RAISE:
      {
      handle_exception:
	JML_DBGPRINTF ("raise caml_trapsp=%p statebytepc=%#x",
		       caml_trapsp, (int) state.js_bytepc);
	if (caml_trapsp >= caml_trap_barrier)
	  caml_debugger (TRAP_BARRIER);
	if (caml_backtrace_active)
	  caml_stash_backtrace ((value) (state.js_accu),
				state.js_bytepc, caml_extern_sp);
	if ((char *) caml_trapsp
	    >= (char *) caml_stack_high - initial_sp_offset) {
	  caml_external_raise = initial_external_raise;
	  caml_extern_sp =
	    (value *) ((char *) caml_stack_high - initial_sp_offset);
	  caml_callback_depth--;
	  caml_jitstate = prevstate;
	  JML_DBGPRINTF ("raise external trap %#lx", (long) caml_trapsp);
	  return Make_exception_result (state.js_accu);
	};
	caml_extern_sp = caml_trapsp;
	state.js_bytepc = ((code_t *) caml_extern_sp)[0];
	caml_trapsp = Trap_link (caml_extern_sp);
	state.js_env = (caml_extern_sp[2]);
	state.js_extra_args = Long_val (caml_extern_sp[3]);
	caml_extern_sp += 4;
	JML_DBGPRINTF ("raise done sp %p bytepc %#lx",
		       caml_extern_sp, (long) state.js_bytepc);
	break;
      };
    case MLJSTATE_ABEND:
      caml_fatal_error ("abnormal end in caml jit\n");
      return 0;
    case MLJSTATE_GRAB:
      {
#define Setup_for_gc   { caml_extern_sp -= 2; \
   caml_extern_sp[0] = state.js_accu; caml_extern_sp[1] = state.js_env;  }
#define Restore_after_gc { state.js_accu = caml_extern_sp[0]; \
   state.js_env = caml_extern_sp[1]; caml_extern_sp += 2; }
	mlsize_t num_args, i;
	num_args = 1 + state.js_extra_args;	/* arg1 + extra args */
	JML_DBGPRINTF ("MLJSTATE_GRAB numargs%d sp%#x", (int) num_args,
		       (int) caml_extern_sp);
	Alloc_small (state.js_accu, num_args + 2, Closure_tag);
	Field (state.js_accu, 1) = state.js_env;
	for (i = 0; i < num_args; i++)
	  Field (state.js_accu, i + 2) = caml_extern_sp[i];
	Code_val (state.js_accu) = state.js_bytepc - 2;
	/* Point to the preceding RESTART instr. */
	caml_extern_sp += num_args;
	state.js_bytepc = (code_t) (caml_extern_sp[0]);
	state.js_env = caml_extern_sp[1];
	state.js_extra_args = Long_val (caml_extern_sp[2]);
	caml_extern_sp += 3;
	break;
#undef Setup_for_gc
#undef Restore_after_gc
      }
    case MLJSTATE_JITRANSLATE:
      {
	volatile struct caml_jit_codeblock_st *curblock = 0;
	JML_DBGPRINTF ("JITTRANSLATE js_bytepc=%#lx", (long) state.js_bytepc);
	JML_DBGPRINTF
	  ("translating externsp=%p stateaccu=%#lx block %p",
	   caml_extern_sp, state.js_accu, cblock);
	/* test for the common case when we have one single block */
	if (cblock && state.js_bytepc >= cblock->cb_byprog
	    && (char *) state.js_bytepc
	    < ((char *) cblock->cb_byprog) + cblock->cb_bysize)
	  curblock = cblock;
	else
	  curblock = caml_jit_code_block_at_bytecode (state.js_bytepc);
	JML_DBGPRINTF ("JITTRANSLATE bytepc %#x curblock %p",
		       (int) state.js_bytepc, curblock);
	if (!curblock)
	  /* should not happen (bytepc don't belong to any active block) */
	  caml_fatal_error_arg
	    ("ocaml JITTRANSLATE invalid bytepc %#x (outside every code block)\n",
	     (char *) state.js_bytepc);
	chunk = caml_jit_translate (state.js_bytepc,
				    (struct caml_jit_codeblock_st *)
				    curblock);
	break;
      };
      break;
    case MLJSTATE_MAKEBIGBLOCK:
      {
	value vblock = Val_unit;
	int i;
	JML_DBGPRINTF ("MAKEBIGBLOCK wosize %d tag %d",
		       (int) state.js_wosize, (int) state.js_tag);
	vblock = caml_alloc_shr (state.js_wosize, state.js_tag);
	caml_initialize (&Field (vblock, 0), state.js_accu);
	for (i = 1; i < state.js_wosize; i++)
	  caml_initialize (&Field (vblock, i), *caml_extern_sp++);
	state.js_accu = vblock;
      }
      break;
    case MLJSTATE_MAKEBIGFLOATB:
      {
	value vblock = Val_unit;
	int i;
	JML_DBGPRINTF ("MAKEBIGFLOATB wosize %d tag %d",
		       (int) state.js_wosize, (int) state.js_tag);
	vblock =
	  caml_alloc_shr (state.js_wosize * Double_wosize, Double_array_tag);
	Store_double_field (vblock, 0, Double_val (state.js_accu));
	for (i = 1; i < state.js_wosize; i++) {
	  Store_double_field (vblock, i, Double_val (*caml_extern_sp));
	  ++caml_extern_sp;
	}
	state.js_accu = vblock;
      };
      break;
    default:
      caml_fatal_error_arg ("impossible jitstate %d\n", (char *) stanum);
    }
  };
}				/* end of caml_jit_interpret */


/* the progsize is a size in bytes, not in words */
value
caml_interprete (code_t prog, asize_t progsize)
{

#ifdef THREADED_CODE
#warning jitinterp.c incompatible with THREADED_CODE
  caml_fatal_error
    ("caml_interprete in jit incompatible with THREADED_CODE\n");
#endif
  return caml_jit_interpret (prog, progsize);
}


void
caml_prepare_bytecode (code_t prog, asize_t prog_size)
{
  struct caml_jit_codeblock_st *cblock = 0;
  struct caml_jit_codechunk_st *chunk = 0;
  JML_DBGPRINTF ("begin prepare bytecode prog %p progsize %d", prog,
		 (int) prog_size);
  cblock = caml_jit_find_code_block (prog, prog_size);
  if (cblock) {
    JML_DBGPRINTF ("already prepared prog %p cblock %p #%d", prog, cblock,
		   cblock->cb_rank);
    return;
  };
  cblock = caml_jit_block_of_bytecode (prog, prog_size);
  chunk = caml_jit_translate (prog, cblock);
  JML_DBGPRINTF
    ("end of prepare bytecode prog %p progsize %d cblock %p rank %d", prog,
     (int) prog_size, cblock, cblock->cb_rank);
}				/* end of caml_prepare_bytecode */

void
caml_release_bytecode (code_t prog, asize_t progsize)
{
  struct caml_jit_codeblock_st *cblock = 0;
  JML_DBGPRINTF ("release bytecode %p size %d", prog, progsize);
  cblock = caml_jit_find_code_block (prog, progsize);
  if (cblock) {
    JML_DBGPRINTF ("freeing cblock %p", cblock);
    caml_jit_unregister_code_block (cblock);
    caml_jit_remove_block (cblock);
  } else
    caml_fatal_error_arg2 ("camljitrun release_bytecode prog %p\n",
			   (void *) prog,
			   "not found size=%d\n", (void *) progsize);
}				/* end of caml_release_bytecode */

/*****
  DEBUGGING NOTES:
  ---------------

Debugging above code is painful (use the ocamljitrund binary for
debugging).

For bugs appearing with a trivial bytecode program, consider using
your debugger (eg gdb) by setting the following environment variables

   OCAMLJITASM to a path prefix like /tmp/jitasm to have generated
   assembler code written into /tmp/jitasm_001 /tmp/jitasm_002 etc

   OCAMLJITOPTION to the string count (for having each bytecode
   generate machine code which updates caml_jit_bytepc (to current
   byte program counter) & caml_jit_inscounter (incremented)

   OCAMLJITPOINT to a path like /tmp/jitpt which contains, when
   reaching caml_jit_run function, a sequence of GDB macros calls, using 

### start of macros for gdb
define camljumpbc
  printf "jump bytecode native=%#x rank=%d prog=%#x progend=%#x\n", $arg0, $arg1, $arg2, $arg3
  break *  $arg0
end

define camljitbp 
  printf "jit code=%#x off=%d bytepc=%#x\n", $arg0, $arg1, $arg2
  break * $arg0
end

define dispjit
  display /4i $pc
  display /x $eax
  display /x $ebx
  display /x ((long *) $eax)[0] @ (caml_stack_high - (long *) $eax + 1)
  display *caml_jitstate
  display caml_jit_bytepc
  display caml_jit_inscounter
end
### end of macros for gdb

For bugs appearing in bigger programs, you need to use your own
debugging program, which communicates thru pipes (set by
OCAMLJITOPTION set to something like todbgfd=5,fromdbgfd=7,count). The
mlptrace/ subdirectory contains an incomplete such debugger

 *****/

/* eof $Id: jitinterp.c,v 1.52 2004-10-10 20:30:52 basile Exp $ */
