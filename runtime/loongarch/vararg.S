// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, INRIA Paris-Rocquencourt
//           Prashanth Mundkur, SRI International
//
// Copyright (c) 2013 Institut National de Recherche en Informatique et
//  en Automatique.
//
//  The contributions by Prashanth Mundkur are reused and adapted
//  under the terms of a Contributor License Agreement between
//  SRI International and INRIA.
//	
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the <organization> nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
// HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// *********************************************************************

// Helper functions for variadic functions <stdarg.h>.  loongarch version.

#include "sysdeps.h"	
	
// typedef void * va_list;
// unsigned int __compcert_va_int32(va_list * ap);
// unsigned long long __compcert_va_int64(va_list * ap);
// double __compcert_va_float64(va_list * ap);

FUNCTION(__compcert_va_int32)
                                   # a0 = ap parameter
	ldptr	$t0, $a0, 0	   # t0 = pointer to next argument
	addi	$t0, $t0, WORDSIZE   # advance ap
	stptr	$t0, $a0, 0	   # update ap
	ld.w	$a0, $t0, -WORDSIZE  # load it and return it in a0
	jr	$ra
ENDFUNCTION(__compcert_va_int32)

FUNCTION(__compcert_va_int64)
				# a0 = ap parameter
	ldptr	$t0, $a0, 0	# t0 = pointer to next argument
	addi	$t0, $t0, 15	# 8-align and advance by 8
	addi	$t1, $zero, -8
	and	$t0, $t0, $t1
	stptr	$t0, $a0, 0	# update ap
#ifdef MODEL_64
	ld.d	$a0, $t0, -8	# return it in a0
#else
	ld.w	$a0, $t0, -8	# return it in [a0,a1]
	ld.w	$a1, $t0, -4
#endif
	jr	$ra
ENDFUNCTION(__compcert_va_int64)

FUNCTION(__compcert_va_float64)
				# a0 = ap parameter
	ldptr	$t0, $a0, 0	# $t0 = pointer to next argument
	addi	$t0, $t0, 15	# 8-align and advance by 8
	addi	$t1, $zero, -8
	and	$t0, $t0, $t1
	stptr	$t0, $a0, 0	# update ap
	fld	$fa0, $t0, -8	# return it in fa0
	jr	$ra
ENDFUNCTION(__compcert_va_float64)

// Right now we pass structs by reference.  This is not ABI conformant.
FUNCTION(__compcert_va_composite)
#ifdef MODEL_64
	b	__compcert_va_int64
#else
	b	__compcert_va_int32
#endif
ENDFUNCTION(__compcert_va_composite)
