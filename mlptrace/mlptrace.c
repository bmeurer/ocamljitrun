/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*      Basile Starynkevitch, projet Cristal, INRIA Rocquencourt       */
/*                                                                     */
/*  Copyright 2004 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/
/* file mlptrace/mlptrace.c */
/*** cvs $Id: mlptrace.c,v 1.2 2004-04-20 13:58:18 starynke Exp $
 ***/
#define _GNU_SOURCE

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/user.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/types.h>
#include <sys/wait.h>


#include <errno.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>

#ifndef __i386__
#error implementation meaningful only on x86
/* for AMD64, some code might be adapted */
#endif

const char caml_mlptrace_ident[] =
 "$Id: mlptrace.c,v 1.2 2004-04-20 13:58:18 starynke Exp $"
  " at " __DATE__ " on " __TIME__
;

#define Nothing ((value) 0)
#ifndef NO_BLOCKING_SECTION
extern void caml_enter_blocking_section (void);
extern void caml_leave_blocking_section (void);
#else
#define caml_enter_blocking_section  bad_use_caml_enter_blocking_section
#define caml_leave_blocking_section  bad_use_caml_leave_blocking_section
#endif

extern void uerror (char *msg, value v);
value
mlptrace_peek (value pid_v, value adr_v)
{
  pid_t pid;
  long adr;
  long r;
  int savederrno = errno;
  CAMLparam2 (pid_v, adr_v);
  CAMLlocal1 (res_v);
  pid = Long_val (pid_v);
  adr = Nativeint_val (adr_v);
#ifndef NO_BLOCKING_SECTION
  caml_enter_blocking_section ();
#endif
  r = ptrace (PTRACE_PEEKDATA, pid, adr, 0);
#ifndef NO_BLOCKING_SECTION
  caml_leave_blocking_section ();
#endif
  if (r == -1 && errno)
    uerror ("Ptrace.peek", Nothing);
  if (savederrno)
    errno = savederrno;
  res_v = caml_copy_nativeint (r);
  CAMLreturn (res_v);
}

value
mlptrace_peekregisters (value pid_v)
{
  pid_t pid;
  struct user usreg;
  long l = 0;
  int savederrno = errno;
  CAMLparam1 (pid_v);
  CAMLlocal5 (res_v, eip_v, eax_v, ebx_v, ecx_v);
  CAMLlocal5 (edx_v, esi_v, edi_v, ebp_v, esp_v);
  CAMLlocal2 (eflags_v, origeax_v);
  pid = Long_val (pid_v);
  memset (&usreg, 0, sizeof (usreg));
#ifndef NO_BLOCKING_SECTION
  caml_enter_blocking_section ();
#endif
  l = ptrace (PTRACE_GETREGS, pid, (void *) 0, &usreg);
#ifndef NO_BLOCKING_SECTION
  caml_leave_blocking_section ();
#endif
  if (l == -1 && errno)
    uerror ("Ptrace.peekregisters", Nothing);
  if (savederrno)
    errno = savederrno;
  eip_v = caml_copy_nativeint (usreg.regs.eip);
  eax_v = caml_copy_nativeint (usreg.regs.eax);
  ebx_v = caml_copy_nativeint (usreg.regs.ebx);
  ecx_v = caml_copy_nativeint (usreg.regs.ecx);
  edx_v = caml_copy_nativeint (usreg.regs.edx);
  esi_v = caml_copy_nativeint (usreg.regs.esi);
  edi_v = caml_copy_nativeint (usreg.regs.edi);
  ebp_v = caml_copy_nativeint (usreg.regs.ebp);
  esp_v = caml_copy_nativeint (usreg.regs.esp);
  eflags_v = caml_copy_nativeint (usreg.regs.eflags);
  origeax_v = caml_copy_nativeint (usreg.regs.orig_eax);
  res_v = alloc_small (0, 11);
  Field (res_v, 0) = eip_v;
  Field (res_v, 1) = eax_v;
  Field (res_v, 2) = ebx_v;
  Field (res_v, 3) = ecx_v;
  Field (res_v, 4) = edx_v;
  Field (res_v, 5) = esi_v;
  Field (res_v, 6) = edi_v;
  Field (res_v, 7) = ebp_v;
  Field (res_v, 8) = esp_v;
  Field (res_v, 9) = eflags_v;
  Field (res_v, 10) = origeax_v;
  CAMLreturn (res_v);
}




value
mlptrace_patchcode (value pid_v, value adr_v, value byte_v)
{
  pid_t pid;
  int savederrno = errno;
  unsigned long l = 0;
  long adr = 0;
  int byte = 0;
  int oldbyte = 0;
  CAMLparam3 (pid_v, adr_v, byte_v);
  pid = Long_val (pid_v);
  byte = Int_val (byte_v);
  adr = Nativeint_val (adr_v);
  /* on Intel x86 the breakpoint is a single byte 0xCC */
  if (byte < 0)
    byte = 0xCC;
  else
    byte &= 0xff;
  errno = 0;
#ifndef NO_BLOCKING_SECTION
  caml_enter_blocking_section ();
#endif
  l = ptrace (PTRACE_PEEKDATA, pid, adr, 0);
  if (l != -1UL && !errno) {
    oldbyte = l & 0xff;
    l = ((-1L << 8) & l) | byte;
    l = ptrace (PTRACE_POKEDATA, pid, adr, l);
  };
#ifndef NO_BLOCKING_SECTION
  caml_leave_blocking_section ();
#endif
  if (l == -1 && errno)
    uerror ("Ptrace.patch", Nothing);
  if (savederrno)
    errno = savederrno;
  CAMLreturn (Val_int(oldbyte));
}

value
mlptrace_cont (value pid_v, value signum_v)
{
  pid_t pid;
  int signum;
  int savederrno = errno;
  long l = 0;
  CAMLparam2 (pid_v, signum_v);
  pid = Long_val (pid_v);
  signum = Long_val (signum_v);
  if (signum < 0)
    signum = 0;
  errno = 0;
#ifndef NO_BLOCKING_SECTION
  caml_enter_blocking_section ();
#endif
  l = ptrace (PTRACE_CONT, pid, (void *) 0, (void *) 0);
#ifndef NO_BLOCKING_SECTION
  caml_leave_blocking_section ();
#endif
  if (l == -1 && errno)
    uerror ("Ptrace.cont", Nothing);
  if (savederrno)
    errno = savederrno;
  CAMLreturn (Val_unit);
}

value
mlptrace_pread_kilobyte(value fd_v, value kbad_v) {
  CAMLparam2(fd_v, kbad_v);
  CAMLlocal1(res_v);
  char kilobuf[1024+1];
  ssize_t sz;
  int fd;
  int kbad;
  size_t cnt;
  ssize_t rd;
  char* p;
  off_t off;
  int savederrno = errno;
  fd = Long_val(fd_v);
  kbad = Long_val(kbad_v);
  memset(kilobuf, 0, sizeof(kilobuf));
  errno = 0;
  res_v = Val_unit;
#ifndef NO_BLOCKING_SECTION
  caml_enter_blocking_section();
#endif
  p = kilobuf;
  cnt = (size_t)1024;
  off = (off_t)kbad << 10;
  while (cnt>0)  {
    rd = pread(fd, p, cnt, off);
    if (rd<0 && errno == EINTR) continue;
    else if (rd<0) break;
    p += rd;
    cnt -= rd;
    off += rd;
  };
#ifndef NO_BLOCKING_SECTION
  caml_leave_blocking_section ();
#endif
  if (p>kilobuf) {
    int l = p - kilobuf;
    res_v = caml_alloc_string(l);
    memcpy(String_val(res_v), kilobuf, l);
  } 
  else if (errno) 
    uerror ("Ptrace.pread_kilobyte", Nothing);
  else  //got eof
    caml_raise_end_of_file();
  if (savederrno)
    errno = savederrno;
  CAMLreturn(res_v);
}

/* eof $Id: mlptrace.c,v 1.2 2004-04-20 13:58:18 starynke Exp $ */
