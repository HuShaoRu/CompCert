(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(* Printing LoongArch assembly code in asm syntax *)

open Printf
open Camlcoq
open Sections
open AST
open Asm
open AisAnnot
open PrintAsmaux
open Fileinfo

(* Module containing the printing functions *)

module Target : TARGET =
  struct

(* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let use_abi_name = false

    let int_reg_num_name = function
                      | R1  -> "$r1"  | R2  -> "$r2"  | R3  -> "$r3"
      | R4  -> "$r4"  | R5  -> "$r5"  | R6  -> "$r6"  | R7  -> "$r7"
      | R8  -> "$r8"  | R9  -> "$r9"  | R10 -> "$r10" | R11 -> "$r11"
      | R12 -> "$r12" | R13 -> "$r13" | R14 -> "$r14" | R15 -> "$r15"
      | R16 -> "$r16" | R17 -> "$r17" | R18 -> "$r18" | R19 -> "$r19"
      | R20 -> "$r20" | R21 -> "$r21" | R22 -> "$r22" | R23 -> "$r23"
      | R24 -> "$r24" | R25 -> "$r25" | R26 -> "$r26" | R27 -> "$r27"
      | R28 -> "$r28" | R29 -> "$r29" | R30 -> "$r30" | R31 -> "$r31"

    let int_reg_abi_name = function
                      | R1  -> "$ra"  | R2  -> "$tp"  | R3  -> "$sp"
      | R4  -> "$a0"  | R5  -> "$a1"  | R6  -> "$a2"  | R7  -> "$a3"
      | R8  -> "$a4"  | R9  -> "$a5"  | R10 -> "$a6"  | R11 -> "$a7"
      | R12 -> "$t0"  | R13 -> "$t1"  | R14 -> "$t2"  | R15 -> "$t3"
      | R16 -> "$t4"  | R17 -> "$t5"  | R18 -> "$t6"  | R19 -> "$t7"
      | R20 -> "$t8"  | R21 -> "$r21" | R22 -> "$s9"  | R23 -> "$s0"
      | R24 -> "$s1"  | R25 -> "$s2"  | R26 -> "$s3"  | R27 -> "$s4"
      | R28 -> "$s5"  | R29 -> "$s6"  | R30 -> "$s7"  | R31 -> "$s8"

    let float_reg_num_name = function
      | F0  -> "$f0"  | F1  -> "$f1"  | F2  -> "$f2"  | F3  -> "$f3"
      | F4  -> "$f4"  | F5  -> "$f5"  | F6  -> "$f6"  | F7  -> "$f7"
      | F8  -> "$f8"  | F9  -> "$f9"  | F10 -> "$f10" | F11 -> "$f11"
      | F12 -> "$f12" | F13 -> "$f13" | F14 -> "$f14" | F15 -> "$f15"
      | F16 -> "$f16" | F17 -> "$f17" | F18 -> "$f18" | F19 -> "$f19"
      | F20 -> "$f20" | F21 -> "$f21" | F22 -> "$f22" | F23 -> "$f23"
      | F24 -> "$f24" | F25 -> "$f25" | F26 -> "$f26" | F27 -> "$f27"
      | F28 -> "$f28" | F29 -> "$f29" | F30 -> "$f30" | F31 -> "$f31"

    let float_reg_abi_name = function
      | F0  -> "$fa0" | F1  -> "$fa1" | F2  -> "$fa2" | F3  -> "$fa3"
      | F4  -> "$fa4" | F5  -> "$fa5" | F6  -> "$fa6" | F7  -> "$fa7"
      | F8  -> "$ft0" | F9  -> "$ft1" | F10 -> "$ft2" | F11 -> "$ft3"
      | F12 -> "$ft4" | F13 -> "$ft5" | F14 -> "$ft6" | F15 -> "$ft7"
      | F16 -> "$ft8" | F17 -> "$ft9" | F18 -> "$ft10"| F19 -> "$ft11"
      | F20 -> "$ft12"| F21 -> "$ft13"| F22 -> "$ft14"| F23 -> "$ft15"
      | F24 -> "$fs0" | F25 -> "$fs1" | F26 -> "$fs2" | F27 -> "$fs3"
      | F28 -> "$fs4" | F29 -> "$fs5" | F30 -> "$fs6" | F31 -> "$fs7"

    let control_flag_reg_name = function
      | FCC0  -> "$fcc0"  | FCC1  -> "$fcc1"  | FCC2  -> "$fcc2"  | FCC3  -> "$fcc3"
      | FCC4  -> "$fcc4"  | FCC5  -> "$fcc5"  | FCC6  -> "$fcc6"  | FCC7  -> "$fcc7"

    let int_reg_name   = if use_abi_name then int_reg_abi_name   else int_reg_num_name
    let float_reg_name = if use_abi_name then float_reg_abi_name else float_reg_num_name

    let ireg oc r = output_string oc (int_reg_name r)
    let freg oc r = output_string oc (float_reg_name r)
    let cfreg oc r = output_string oc (control_flag_reg_name r)

    let ireg0 oc = function
      | R0 -> output_string oc "$r0"
      | R r -> ireg oc r

    let preg_asm oc ty = function
      | IR r -> ireg oc r
      | FR r -> freg oc r
      | _    -> assert false

    let preg_annot = function
      | IR r -> int_reg_name r
      | FR r -> float_reg_name r
      | _ -> assert false

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          variable_section ~sec:".data" ~bss:".bss" i
      | Section_const i | Section_small_const i ->
          variable_section ~sec:".section	.rodata" i
      | Section_string       -> ".section	.rodata"
      | Section_literal      -> ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")
      | Section_ais_annotation -> sprintf ".section	\"__compcert_ais_annotations\",\"\",@note"

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Associate labels to floating-point constants and to symbols. *)

    let emit_constants oc lit =
      if exists_constants () then begin
         section oc lit;
         if Hashtbl.length literal64_labels > 0 then
           begin
             fprintf oc "	.align 3\n";
             Hashtbl.iter
               (fun bf lbl -> fprintf oc "%a:	.quad	0x%Lx\n" label lbl bf)
               literal64_labels
           end;
         if Hashtbl.length literal32_labels > 0 then
           begin
             fprintf oc "	.align	2\n";
             Hashtbl.iter
               (fun bf lbl ->
                  fprintf oc "%a:	.long	0x%lx\n" label lbl bf)
               literal32_labels
           end;
         reset_literals ()
      end

(* Generate code to load the address of id in register r *)

    let loadsymbol oc r id =     
      fprintf oc "	la %a, %a\n" ireg r id

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

(*
    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)
*)

(* Offset part of a load or store *)

    let offset oc = function
    | (*Ofsimm*) n -> ptrofs oc n

(* Printing of instructions *)
    let print_instruction oc = function
      (* Arithmetic Operation Instructions *)
      | Paddw(rd, rj, rk) ->
         fprintf oc "	add.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Paddd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	add.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psubw(rd, rj, rk) ->
         fprintf oc "	sub.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psubd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	sub.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk

      | Paddiw (rd, rj, si12) ->
         fprintf oc "	addi.w	%a, %a, %a\n" ireg rd ireg0 rj coqint si12
      | Paddid (rd, rj, si12) -> assert Archi.ptr64;
         fprintf oc "	addi.d	%a, %a, %a\n" ireg rd ireg0 rj coqint64 si12

      | Plu12iw (rd, si20) ->
         fprintf oc "	lu12i.w	 %a, %a\n"     ireg rd coqint si20
      | Plu12id (rd, si20) -> assert Archi.ptr64;
         fprintf oc "	lu12i.w	 %a, %a\n"     ireg rd coqint64 si20
      | Plu32id (rd, si20) -> assert Archi.ptr64;
         fprintf oc "	lu32i.d	 %a, %a\n" ireg rd coqint64 si20 
      | Plu52id (rd, rj, si12) -> assert Archi.ptr64;
         fprintf oc "	lu52i.d	 %a, %a, %a\n" ireg rd ireg0 rj coqint64 si12

      | Psltw(rd, rj, rk) ->
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psltwu(rd, rj, rk) ->
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psltd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psltdu(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk

      | Psltiw (rd, rj, si12) ->
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg0 rj coqint si12
      | Psltuiw (rd, rj, si12) ->
         fprintf oc "	sltui	%a, %a, %a\n" ireg rd ireg0 rj coqint si12
      | Psltid (rd, rj, si12) -> assert Archi.ptr64;
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg0 rj coqint64 si12
      | Psltuid (rd, rj, si12) -> assert Archi.ptr64;
         fprintf oc "	sltui	%a, %a, %a\n" ireg rd ireg0 rj coqint64 si12

      | Pandw(rd, rj, rk) ->
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Porw(rd, rj, rk) ->
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pnorw(rd, rj, rk) ->
         fprintf oc "	nor	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pxorw(rd, rj, rk) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pandnw(rd, rj, rk) ->
         fprintf oc "	andn	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pornw(rd, rj, rk) ->
         fprintf oc "	orn	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pandd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pord(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pnord(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	nor	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pxord(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pandnd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	andn	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pornd(rd, rj, rk) ->
         fprintf oc "	orn	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk

      | Pandiw (rd, rj, ui12) ->
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg0 rj coqint ui12
      | Poriw (rd, rj, ui12) ->
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg0 rj coqint ui12
      | Pxoriw (rd, rj, ui12) ->
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg0 rj coqint ui12
      | Pandid (rd, rj, ui12) -> assert Archi.ptr64;
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui12
      | Porid (rd, rj, ui12) -> assert Archi.ptr64;
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui12
      | Pxorid (rd, rj, ui12) -> assert Archi.ptr64;
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui12

      | Pnop ->
        fprintf oc "	nop\n"

      | Pmulw(rd, rj, rk) ->
         fprintf oc "	mul.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmulhw(rd, rj, rk) ->  assert (not Archi.ptr64);
         fprintf oc "	mulh.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmulhwu(rd, rj, rk) ->  assert (not Archi.ptr64);
         fprintf oc "	mulh.wu	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmuld(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	mul.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmulhd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	mulh.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmulhdu(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	mulh.du	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk

      | Pdivw(rd, rj, rk) ->
         fprintf oc "	div.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmodw(rd, rj, rk) ->
         fprintf oc "	mod.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk   
      | Pdivwu(rd, rj, rk) ->
         fprintf oc "	div.wu	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmodwu(rd, rj, rk) ->
         fprintf oc "	mod.wu	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pdivd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	div.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmodd(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	mod.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pdivdu(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	div.du	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pmoddu(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	mod.du	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      (* Bit-shift Instructions *) 
      | Psllw(rd, rj, rk) ->
         fprintf oc "	sll.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psrlw(rd, rj, rk) ->
         fprintf oc "	srl.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psraw(rd, rj, rk) ->
         fprintf oc "	sra.w	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Pslld(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	sll.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psrld(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	srl.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk
      | Psrad(rd, rj, rk) -> assert Archi.ptr64;
         fprintf oc "	sra.d	%a, %a, %a\n" ireg rd ireg0 rj ireg0 rk

      | Pslliw (rd, rj, ui5) ->
         fprintf oc "	slli.w	%a, %a, %a\n" ireg rd ireg0 rj coqint ui5
      | Psrliw (rd, rj, ui5) ->
         fprintf oc "	srli.w	%a, %a, %a\n" ireg rd ireg0 rj coqint ui5
      | Psraiw (rd, rj, ui5) ->
         fprintf oc "	srai.w	%a, %a, %a\n" ireg rd ireg0 rj coqint ui5
      | Protriw (rd, rj, ui5)  ->
         fprintf oc "	rotri.w	%a, %a, %a\n" ireg rd ireg0 rj coqint ui5
      | Psllid (rd, rj, ui6) -> assert Archi.ptr64;
         fprintf oc "	slli.d	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui6
      | Psrlid (rd, rj, ui6) -> assert Archi.ptr64;
         fprintf oc "	srli.d	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui6
      | Psraid (rd, rj, ui6) -> assert Archi.ptr64;
         fprintf oc "	srai.d	%a, %a, %a\n" ireg rd ireg0 rj coqint64 ui6
      
      (* Bit-manipulation Instructions *)
      | Pclzw (rd, rj) ->
         fprintf oc "	clz.w	%a, %a\n" ireg rd ireg0 rj
      | Pclzd (rd, rj) -> assert Archi.ptr64;
         fprintf oc "	clz.d	%a, %a\n" ireg rd ireg0 rj
      | Pctzw (rd, rj) ->
         fprintf oc "	ctz.w	%a, %a\n" ireg rd ireg0 rj
      | Pctzd (rd, rj) -> assert Archi.ptr64;
         fprintf oc "	ctz.d	%a, %a\n" ireg rd ireg0 rj
      | Prevb2h (rd, rj) ->
         fprintf oc "	revb.2h	%a, %a\n" ireg rd ireg0 rj
      | Prevb4h (rd, rj) -> assert Archi.ptr64;
         fprintf oc "	revb.4h	%a, %a\n" ireg rd ireg0 rj
      | Prevhd  (rd, rj) -> assert Archi.ptr64;
         fprintf oc "	revh.d	%a, %a\n" ireg rd ireg0 rj
      | Pbstrpickw (rd, rj, m, l) ->
         fprintf oc "	bstrpick.w	%a, %a, %a, %a\n" ireg rd ireg0 rj coqint m coqint l
  
      (* Branch Instructions *)
      | Pbeqw(rj, rd, l) ->
         fprintf oc "	beq	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbnew(rj, rd, l) ->
         fprintf oc "	bne	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbltw(rj, rd, l) ->
         fprintf oc "	blt	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbgew(rj, rd, l) ->
         fprintf oc "	bge	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbltwu(rj, rd, l) ->
         fprintf oc "	bltu	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbgewu(rj, rd, l) ->
         fprintf oc "	bgeu	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbeqd(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	beq	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbned(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	bne	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbltd(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	blt	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbged(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	bge	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbltdu(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	bltu	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l
      | Pbgedu(rj, rd, l) -> assert Archi.ptr64;
         fprintf oc "	bgeu	%a, %a, %a\n" ireg0 rj ireg0 rd print_label l

      | Pbeqzw(rj, l) ->
         fprintf oc "	beqz	%a, %a\n" ireg0 rj print_label l
      | Pbnezw(rj, l) ->
         fprintf oc "	bnez	%a, %a\n" ireg0 rj print_label l
      | Pbeqzd(rj, l) -> assert Archi.ptr64;
         fprintf oc "	beqz	%a, %a\n" ireg0 rj print_label l
      | Pbnezd(rj, l) -> assert Archi.ptr64;
         fprintf oc "	bnez	%a, %a\n" ireg0 rj print_label l

      | Pj_l(l) ->
         fprintf oc "	b	%a\n" print_label l
      | Pj_s(s, sg) ->
         fprintf oc "	b	%a\n" symbol s
      | Pj_r(r, sg) ->
         fprintf oc "	jr	%a\n" ireg r
      | Pjal_s(s, sg) ->
        if Archi.pic_code () then begin
            fprintf oc "	bl	%%plt(%a)\n" symbol s;
        end else begin
            fprintf oc "	bl	%a\n" symbol s;
        end
      | Pjal_r(r, sg) ->
         fprintf oc "	jirl	$r1, %a, 0\n" ireg r

      (* Common Memory Access Instructions *)
      | Pldb(rd, rj, ofs) ->
         fprintf oc "	ld.b	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pldh(rd, rj, ofs) ->
         fprintf oc "	ld.h	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pldw(rd, rj, ofs) | Pldw_a(rd, rj, ofs) ->
         fprintf oc "	ld.w	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pldd(rd, rj, ofs) | Pldd_a(rd, rj, ofs) -> assert Archi.ptr64;
         fprintf oc "	ld.d	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pldbu(rd, rj, ofs) ->
         fprintf oc "	ld.bu	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pldhu(rd, rj, ofs) ->
         fprintf oc "	ld.hu	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pstb(rd, rj, ofs) ->
         fprintf oc "	st.b	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Psth(rd, rj, ofs) ->
         fprintf oc "	st.h	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pstw(rd, rj, ofs) | Pstw_a(rd, rj, ofs) ->
         fprintf oc "	st.w	%a, %a, %a\n" ireg rd ireg rj offset ofs
      | Pstd(rd, rj, ofs) | Pstd_a(rd, rj, ofs) -> assert Archi.ptr64;
         fprintf oc "	st.d	%a, %a, %a\n" ireg rd ireg rj offset ofs

      (* Floating-Point Arithmetic Operation Instructions *)
      | Pfadds (fd, fj, fk) ->
         fprintf oc "	fadd.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfaddd (fd, fj, fk) ->
         fprintf oc "	fadd.d	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfsubs (fd, fj, fk) ->
         fprintf oc "	fsub.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfsubd (fd, fj, fk) ->
         fprintf oc "	fsub.d	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfmuls (fd, fj, fk) ->
         fprintf oc "	fmul.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfmuld (fd, fj, fk) ->
         fprintf oc "	fmul.d	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfdivs (fd, fj, fk) ->
         fprintf oc "	fdiv.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfdivd (fd, fj, fk) ->
         fprintf oc "	fdiv.d	%a, %a, %a\n" freg fd freg fj freg fk
      
      | Pfmadds (fd, fj, fk, fa) ->
         fprintf oc "	fmadd.s	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfmaddd (fd, fj, fk, fa) ->
         fprintf oc "	fmadd.d	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfmsubs (fd, fj, fk, fa) ->
         fprintf oc "	fmsub.s	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfmsubd (fd, fj, fk, fa) ->
         fprintf oc "	fmsub.d	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfnmadds (fd, fj, fk, fa) ->
         fprintf oc "	fnmadd.s	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfnmaddd (fd, fj, fk, fa) ->
         fprintf oc "	fnmadd.d	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfnmsubs (fd, fj, fk, fa) ->
         fprintf oc "	fnmsub.s	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      | Pfnmsubd (fd, fj, fk, fa) ->
         fprintf oc "	fnmsub.d	%a, %a, %a, %a\n" freg fd freg fj freg fk freg fa
      
      | Pfmaxs (fd, fj, fk) ->
         fprintf oc "	fmax.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfmaxd (fd, fj, fk) ->
         fprintf oc "	fmax.d	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfmins (fd, fj, fk) ->
         fprintf oc "	fmin.s	%a, %a, %a\n" freg fd freg fj freg fk
      | Pfmind (fd, fj, fk) ->
         fprintf oc "	fmin.d	%a, %a, %a\n" freg fd freg fj freg fk
      
      | Pfabss (fd, fj) ->
         fprintf oc "	fabs.s	%a, %a\n"     freg fd freg fj
      | Pfabsd (fd, fj) ->
         fprintf oc "	fabs.d	%a, %a\n"     freg fd freg fj
      | Pfnegs (fd, fj) ->
         fprintf oc "	fneg.s	%a, %a\n"     freg fd freg fj
      | Pfnegd (fd, fj) ->
         fprintf oc "	fneg.d	%a, %a\n"     freg fd freg fj
      
      | Pfsqrts (fd, fj) ->
         fprintf oc "	fsqrt.s %a, %a\n"     freg fd freg fj
      | Pfsqrtd (fd, fj) ->
         fprintf oc "	fsqrt.d	%a, %a\n" freg fd freg fj

      (* Floating-Point Comparison Instructions *)
      | Pfeqs (cc, fs1, fs2) ->
         fprintf oc "	fcmp.ceq.s   %a, %a, %a\n" cfreg cc freg fs1 freg fs2
      | Pflts (cc, fs1, fs2) ->
         fprintf oc "	fcmp.clt.s   %a, %a, %a\n" cfreg cc freg fs1 freg fs2
      | Pfles (cc, fs1, fs2) ->
         fprintf oc "	fcmp.cle.s   %a, %a, %a\n" cfreg cc freg fs1 freg fs2
      | Pfeqd (cc, fs1, fs2) ->
         fprintf oc "	fcmp.ceq.d	%a, %a, %a\n" cfreg cc freg fs1 freg fs2
      | Pfltd (cc, fs1, fs2) ->
         fprintf oc "	fcmp.clt.d	%a, %a, %a\n" cfreg cc freg fs1 freg fs2
      | Pfled (cc, fs1, fs2) ->
         fprintf oc "	fcmp.cle.d	%a, %a, %a\n" cfreg cc freg fs1 freg fs2

      (* Floating-Point Conversion Instructions *)
      | Pfcvtsd (fd, fj) ->
         fprintf oc "	fcvt.s.d	%a, %a\n" freg fd freg fj
      | Pfcvtds (fd, fj) ->
         fprintf oc "	fcvt.d.s	%a, %a\n" freg fd freg fj
      | Pfcvtws (rd, fs) ->
         fprintf oc "	ftintrz.w.s	$f0, %a\n" freg fs;
         fprintf oc "	movfr2gr.s	%a, $f0\n" ireg rd
      | Pfcvtsw (fd, rs) ->
         fprintf oc "	movgr2fr.w	$f0, %a\n" ireg0 rs;
         fprintf oc "	ffint.s.w	%a, $f0\n" freg fd
      | Pfcvtls (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	ftintrz.l.s	$f0, %a\n" freg fs;
         fprintf oc "	movfr2gr.d	%a, $f0\n" ireg rd
      | Pfcvtsl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	movgr2fr.d	$f0, %a\n" ireg0 rs;
         fprintf oc "	ffint.s.l	%a, $f0\n" freg fd
      | Pfcvtwd (rd, fs) ->
         fprintf oc "	ftintrz.w.d	$f0, %a\n" freg fs;
         fprintf oc "	movfr2gr.s	%a, $f0\n" ireg rd
      | Pfcvtdw (fd, rs) ->
         fprintf oc "	movgr2fr.w	$f0, %a\n" ireg0 rs;
         fprintf oc "	ffint.d.w	%a, $f0\n" freg fd
      | Pfcvtld (rd, fs) -> assert Archi.ptr64;
         fprintf oc "	ftintrz.l.d	$f0, %a\n" freg fs;
         fprintf oc "	movfr2gr.d	%a, $f0\n" ireg rd
      | Pfcvtdl (fd, rs) -> assert Archi.ptr64;
         fprintf oc "	movgr2fr.d	$f0, %a\n" ireg0 rs;
         fprintf oc "	ffint.d.l	%a, $f0\n" freg fd
      | Pfmvxs (rd,fs) ->
         fprintf oc "	movfr2gr.s	%a, %a\n"     ireg rd freg fs
      | Pfmvsx (fd,rs) ->
         fprintf oc "	movgr2fr.w	%a, %a\n"     freg fd ireg rs
      | Pfmvxd (rd,fs) ->
         fprintf oc "	movfr2gr.d	%a, %a\n"     ireg rd freg fs
      | Pfmvdx (fd,rs) ->
         fprintf oc "	movgr2fr.d	%a, %a\n"     freg fd ireg rs

      (* Floating-Point Move Instructions *)
      | Pfmv (fd,fs) ->
         fprintf oc "	fmov.d	%a, %a\n"     freg fd freg fs
      | Pmovcf2gr (rd, cj) ->
         fprintf oc "	movcf2gr	%a, %a\n" ireg rd cfreg cj

      (* Floating-Point Branch Instructions *)
      | Pbceqz(cj, l) ->
         fprintf oc "	bceqz	%a, %a\n" cfreg cj print_label l
      | Pbcnez(cj, l) ->
         fprintf oc "	bcnez	%a, %a\n" cfreg cj print_label l

      (* Floating-Point Common Memory Access Instructions *)
      | Pflds (fd, rj, ofs) ->
         fprintf oc "	fld.s	%a, %a, %a\n" freg fd ireg rj offset ofs
      | Pfldd (fd, rj, ofs) | Pfldd_a (fd, rj, ofs) ->
         fprintf oc "	fld.d	%a, %a, %a\n" freg fd ireg rj offset ofs
      | Pfsts (fd, rj, ofs) ->
         fprintf oc "	fst.s	%a, %a, %a\n" freg fd ireg rj offset ofs
      | Pfstd (fd, rj, ofs) | Pfstd_a (fd, rj, ofs) ->
         fprintf oc "	fst.d	%a, %a, %a\n" freg fd ireg rj offset ofs

      (* Pseudo-instructions expanded in Asmexpand *)
      | Pallocframe(sz, ofs) ->
         assert false
      | Pfreeframe(sz, ofs) ->
         assert false
      | Pseqw _ | Psnew _ | Pseqd _ | Psned _ | Pcvtl2w _ | Pcvtw2l _ ->
         assert false

      (* Pseudo-instructions that remain *)
      | Pmv(rd, rs) ->
         fprintf oc "	move	%a, %a\n"     ireg rd ireg rs
      | Plabel lbl ->
         fprintf oc "%a:\n" print_label lbl
      | Ploadsymbol(rd, id) ->
         loadsymbol oc rd symbol_offset (id, Integers.Ptrofs.zero)
      | Ploadli(rd, n) ->
         let d = camlint64_of_coqint n in
         let lbl = label_literal64 d in
         loadsymbol oc rd label lbl;
         fprintf oc "	ld.d	%a, %a, 0 %s %Lx\n" ireg rd ireg rd comment d
      | Ploadfi(rd, f) ->
         let d   = camlint64_of_coqint(Floats.Float.to_bits f) in
         let lbl = label_literal64 d in
         loadsymbol oc R20 label lbl;
         fprintf oc "	fld.s	%a, $r20, 0 %s %.18g\n" freg rd comment (camlfloat_of_coqfloat f)
      | Ploadsi(rd, f) ->
         let s   = camlint_of_coqint(Floats.Float32.to_bits f) in
         let lbl = label_literal32 s in
         loadsymbol oc R20 label lbl;
         fprintf oc "	fld.d	%a, $r20, 0 %s %.18g\n" freg rd comment (camlfloat_of_coqfloat32 f)
      | Pbtbl(r, tbl) ->
         let lbl = new_label() in
         fprintf oc "%s jumptable [ " comment;
         List.iter (fun l -> fprintf oc "%a " print_label l) tbl;
         fprintf oc "]\n";
         if Archi.ptr64 then begin
            fprintf oc "	slli.d	$r12, %a, 2\n" ireg r;
            fprintf oc "	la	$r20, %a\n" label lbl;
            fprintf oc "	add.d	$r12, $r20, $r12\n";
            fprintf oc "	ld.w	$r12, $r12, 0\n";
            fprintf oc "	add.d	$r12, $r20, $r12\n";
         end else begin
            fprintf oc "	slli.w	$r12, %a, 2\n" ireg r;
            fprintf oc "	la	$r20, %a\n" label lbl;
            fprintf oc "	add.w	$r12, $r20, $r12\n";
            fprintf oc "	ld.w	$r12, $r12, 0\n";
            fprintf oc "	add.w	$r12, $r20, $r12\n";
         end;
         fprintf oc "	jr	$r12\n";
         jumptables := (lbl, tbl) :: !jumptables;
         fprintf oc "%s end pseudoinstr btbl\n" comment
      
      | Pbuiltin(ef, args, res) ->
         begin match ef with
           | EF_annot(kind,txt, targs) ->
             begin match (P.to_int kind) with
               | 1 -> let annot = annot_text preg_annot "sp" (camlstring_of_coqstring txt) args  in
                 fprintf oc "%s annotation: %S\n" comment annot
               | 2 -> let lbl = new_label () in
                 fprintf oc "%a:\n" label lbl;
                 add_ais_annot lbl preg_annot "sp" (camlstring_of_coqstring txt) args
               | _ -> assert false
             end
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg_annot "sp" oc
                               (P.to_int kind) (extern_atom txt) args
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg_asm oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment
          | _ ->
              assert false
         end

    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable

    let print_align oc alignment =
      fprintf oc "	.balign %d\n" alignment

    let print_jumptable oc jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.long	%a - %a\n"
                               print_label l label lbl)
          tbl in
      if !jumptables <> [] then
        begin
          section oc jmptbl;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end

    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      List.iter (print_instruction oc) fn.fn_code


(* Data *)

    let address = if Archi.ptr64 then ".quad" else ".long"

    let print_prologue oc =
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let default_falignment = 2

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()

  end

let sel_target () =
  (module Target:TARGET)
