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


/***
   cvs $Id: test_callback.c,v 1.3 2004-04-22 09:31:38 basile Exp $
***/

#include <stdio.h>
#include <stdlib.h>
#include "mlvalues.h"
#include "callback.h"
#include "memory.h"

value test_callback(value fun_v, value low_v, value high_v) {
  CAMLparam3(fun_v,low_v,high_v);
  CAMLlocal2(r_v, i_v);
  int low=0, high=0, i=0;
  low = Int_val(low_v);
  high = Int_val(high_v);
  fprintf(stderr, "%s:%d: low=%d high=%d\n", __FILE__, __LINE__, 
	  low, high);
  fflush(stderr);
  for (i=low; i<high; i++) {
    fprintf(stderr, "%s:%d: i=%d\n", __FILE__, __LINE__, i);
  fflush(stderr);
    i_v = Val_int(i);
    r_v = caml_callback(fun_v,i_v);
    fprintf(stderr, "%s:%d: after callback i=%d\n", __FILE__, __LINE__, i);
  fflush(stderr);
  };
  fprintf(stderr, "%s:%d: end\n", __FILE__, __LINE__);
  fflush(stderr);
  CAMLreturn(Val_unit);
}

value test_message(value str_v, value i_v) {
  CAMLparam2(str_v,i_v);
  int i=Int_val(i_v);
  char* s = String_val(str_v);
  fprintf(stderr, "%s:%d: str='%s' i=%d\n", __FILE__, __LINE__, s, i);
  fflush(stderr);
  CAMLreturn(Val_unit);
}

/* eof $Id: test_callback.c,v 1.3 2004-04-22 09:31:38 basile Exp $ */
