(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
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

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the LoongArch assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open! Integers

exception Error of string

(* Useful constants and helper functions *)

let _0  = Integers.Int.zero
let _1  = Integers.Int.one
let _2  = coqint_of_camlint 2l
let _4  = coqint_of_camlint 4l
let _8  = coqint_of_camlint 8l
let _16  = coqint_of_camlint 16l
let _m1 = coqint_of_camlint (-1l)

let wordsize = if Archi.ptr64 then 8 else 4

let align n a = (n + a - 1) land (-a)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_loadimm32 dst n =
  List.iter emit (Asmgen.loadimm32 dst n [])
let expand_addptrofs dst src n =
  List.iter emit (Asmgen.addptrofs dst src n [])
let expand_storeind_ptr src base ofs =
  List.iter emit (Asmgen.storeind_ptr src base ofs [])

(* Fix-up code around function calls and function entry.
   Some floating-point arguments residing in FP registers need to be
   moved to integer registers or register pairs.
   Symmetrically, some floating-point parameter passed in integer
   registers or register pairs need to be moved to FP registers. *)

let int_param_regs = [| R4; R5; R6; R7; R8; R9; R10; R11 |]

let move_single_arg fr i =
  emit (Pfmvxs(int_param_regs.(i), fr))

let move_double_arg fr i =
  if Archi.ptr64 then begin
    emit (Pfmvxd(int_param_regs.(i), fr))
  end else begin
    emit (Paddiw(R3, Asm.R R3, Integers.Int.neg _16));
    emit (Pfstd(fr, R3, _0));
    emit (Pldw(int_param_regs.(i), R3, _0));
    if i < 7 then begin
      emit (Pldw(int_param_regs.(i + 1), R3, _4))
    end else begin
      emit (Pldw(R20, R3, _4));
      emit (Pstw(R20, R3, _16))
    end;
    emit (Paddiw(R3, Asm.R R3, _16))
  end

let move_single_param fr i =
  emit (Pfmvsx(fr, int_param_regs.(i)))

let move_double_param fr i =
  if Archi.ptr64 then begin
    emit (Pfmvdx(fr, int_param_regs.(i)))
  end else begin
    emit (Paddiw(R3, Asm.R R3, Integers.Int.neg _16));
    emit (Pstw(int_param_regs.(i), R3, _0));
    if i < 7 then begin
      emit (Pstw(int_param_regs.(i + 1), R3, _4))
    end else begin
      emit (Pldw(R20, R3, _16));
      emit (Pstw(R20, R3, _4))
    end;
    emit (Pfldd(fr, R3, _0));
    emit (Paddiw(R3, Asm.R R3, _16))
  end

let float_extra_index = function
  | Machregs.F8 -> Some (F8, 0)
  | Machregs.F9 -> Some (F9, 1)
  | Machregs.F10 -> Some (F10, 2)
  | Machregs.F11 -> Some (F11, 3)
  | Machregs.F12 -> Some (F12, 4)
  | Machregs.F13 -> Some (F13, 5)
  | Machregs.F14 -> Some (F14, 6)
  | Machregs.F15 -> Some (F15, 7)
  | _  -> None

let fixup_gen single double sg =
  let fixup ty loc =
    match ty, loc with
    | Tsingle, One (Locations.R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> single r i
        | None -> ()
        end
    | (Tfloat | Tany64), One (Locations.R r) ->
        begin match float_extra_index r with
        | Some(r, i) -> double r i
        | None -> ()
        end
    | _, _ -> ()
  in
    List.iter2 fixup sg.sig_args (Conventions1.loc_arguments sg)

let fixup_call sg =
  fixup_gen move_single_arg move_double_arg sg

let fixup_function_entry sg =
  fixup_gen move_single_param move_double_param sg

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmv (dst, src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmv (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Handling of memcpy *)

let offset_in_range ofs =
  let ofs = Z.to_int64 ofs in -2048L <= ofs && ofs < 2048L
  
let memcpy_small_arg sz arg tmp =
  match arg with
  | BA (IR r) ->
      (r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Ptrofs.add ofs (Ptrofs.repr (Z.of_uint sz)))
      then (R3, ofs)
      else begin expand_addptrofs tmp R3 ofs; (tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (IR R12) then R12 else R13 in
  let tdst = if src <> BA (IR R12) then R13 else R12 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  let rec copy osrc odst sz =
    if sz >= 8 && al >= 8 then
      begin
        emit (Pfldd (F0, rsrc, osrc));
        emit (Pfstd (F0, rdst, odst));
        copy (Ptrofs.add osrc _8) (Ptrofs.add odst _8) (sz - 8)
      end
    else if sz >= 4 && al >= 4 then
      begin
        emit (Pldw (R20, rsrc, osrc));
        emit (Pstw (R20, rdst, odst));
        copy (Ptrofs.add osrc _4) (Ptrofs.add odst _4) (sz - 4)
      end
    else if sz >= 2 && al >= 2 then
      begin
        emit (Pldh (R20, rsrc, osrc));
        emit (Psth (R20, rdst, odst));
        copy (Ptrofs.add osrc _2) (Ptrofs.add odst _2) (sz - 2)
      end
    else if sz >= 1 then
      begin
        emit (Pldb (R20, rsrc, osrc));
        emit (Pstb (R20, rdst, odst));
        copy (Ptrofs.add osrc _1) (Ptrofs.add odst _1) (sz - 1)
      end
  in copy osrc odst sz

let memcpy_big_arg sz arg tmp =
  match arg with
  | BA (IR r) -> if r <> tmp then emit (Pmv(tmp, r))
  | BA_addrstack ofs ->
      expand_addptrofs tmp R3 ofs
  | _ ->
      assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  let (s, d) =
    if dst <> BA (IR R12) then (R12, R13) else (R13, R12) in
  memcpy_big_arg sz src s;
  memcpy_big_arg sz dst d;
  (* Use R14 as loop count, R20 and F0 as ld/st temporaries. *)
  let (load, store, chunksize) =
    if al >= 8 then
      (Pfldd (F0, s, _0), Pfstd (F0, d, _0), 8)
    else if al >= 4 then
      (Pldw (R20, s, _0), Pstw (R20, d, _0), 4)
    else if al = 2 then
      (Pldh (R20, s, _0), Psth (R20, d, _0), 2)
    else
      (Pldb (R20, s, _0), Pstb (R20, d, _0), 1) in
  expand_loadimm32 R14 (Z.of_uint (sz / chunksize));
  let delta = Z.of_uint chunksize in
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  expand_addptrofs s s delta;
  emit (Paddiw(R14, Asm.R R14, _m1));
  emit store;
  expand_addptrofs d d delta;
  emit (Pbnew (Asm.R R14, R0, lbl))

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Pldbu (res, base, ofs))
  | Mint8signed, BR(IR res) ->
     emit (Pldb  (res, base, ofs))
  | Mint16unsigned, BR(IR res) ->
     emit (Pldhu (res, base, ofs))
  | Mint16signed, BR(IR res) ->
     emit (Pldh  (res, base, ofs))
  | Mint32, BR(IR res) ->
     emit (Pldw  (res, base, ofs))
  | Mint64, BR(IR res) ->
     emit (Pldd  (res, base, ofs))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let ofs' = Ptrofs.add ofs _4 in
     if base <> res2 then begin
         emit (Pldw (res2, base, ofs));
         emit (Pldw (res1, base, ofs'))
       end else begin
         emit (Pldw (res1, base, ofs'));
         emit (Pldw (res2, base, ofs))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pflds (res, base, ofs))
  | Mfloat64, BR(FR res) ->
     emit (Pfldd (res, base, ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk R3 ofs res
      else begin
        expand_addptrofs R20 R3 ofs; (* R20 <- sp + ofs *)
        expand_builtin_vload_common chunk R20 _0 res
      end
  | [BA_addptr(BA(IR addr), (BA_int ofs | BA_long ofs))] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk addr ofs res
      else begin
        expand_addptrofs R20 addr ofs; (* R20 <- addr + ofs *)
        expand_builtin_vload_common chunk R20 _0 res
      end
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Pstb (src, base, ofs))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Psth (src, base, ofs))
  | Mint32, BA(IR src) ->
     emit (Pstw (src, base, ofs))
  | Mint64, BA(IR src) ->
     emit (Pstd (src, base, ofs))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let ofs' = Ptrofs.add ofs _4 in
     emit (Pstw (src2, base, ofs));
     emit (Pstw (src1, base, ofs'))
  | Mfloat32, BA(FR src) ->
     emit (Pfsts (src, base, ofs))
  | Mfloat64, BA(FR src) ->
     emit (Pfstd (src, base, ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk R3 ofs src
      else begin
        expand_addptrofs R20 R3 ofs; (* R20 <- sp + ofs *)
        expand_builtin_vstore_common chunk R20 _0 src
      end
  | [BA_addptr(BA(IR addr), (BA_int ofs | BA_long ofs)); src] ->
      if offset_in_range (Z.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk addr ofs src
      else begin
        expand_addptrofs R20 addr ofs; (* R20 <- addr + ofs *)
        expand_builtin_vstore_common chunk R20 _0 src
      end
  | _ ->
      assert false

(* Handling of varargs *)

(* Number of integer registers, FP registers, and stack words
   used to pass the (fixed) arguments to a function. *)

let arg_int_size ri rf ofs k =
  if ri < 8
  then k (ri + 1) rf ofs
  else k ri rf (ofs + 1)

let arg_single_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_int_size ri rf ofs k

let arg_long_size ri rf ofs k =
  if Archi.ptr64 then
    if ri < 8
    then k (ri + 1) rf ofs
    else k ri rf (ofs + 1)
  else
    if ri < 7 then k (ri + 2) rf ofs
    else if ri = 7 then k (ri + 1) rf (ofs + 1)
    else k ri rf (align ofs 2 + 2)

let arg_double_size ri rf ofs k =
  if rf < 8
  then k ri (rf + 1) ofs
  else arg_long_size ri rf ofs k

let rec args_size l ri rf ofs =
  match l with
  | [] -> (ri, rf, ofs)
  | (Tint | Tany32) :: l ->
      arg_int_size ri rf ofs (args_size l)
  | Tsingle :: l ->
      arg_single_size ri rf ofs (args_size l)
  | Tlong :: l ->
      arg_long_size ri rf ofs (args_size l)
  | (Tfloat | Tany64) :: l ->
      arg_double_size ri rf ofs (args_size l)

(* Size in words of the arguments to a function.  This includes both
   arguments passed in integer registers and arguments passed on stack,
   but not arguments passed in FP registers. *)

let arguments_size sg =
  let (ri, _, ofs) = args_size sg.sig_args 0 0 0 in
  ri + ofs

let save_arguments first_reg base_ofs =
  for i = first_reg to 7 do
    expand_storeind_ptr
      int_param_regs.(i)
      R3
      (Ptrofs.repr (Z.add base_ofs (Z.of_uint ((i - first_reg) * wordsize))))
  done

let vararg_start_ofs : Z.t option ref = ref None

let expand_builtin_va_start r =
  match !vararg_start_ofs with
  | None ->
      invalid_arg "Fatal error: va_start used in non-vararg function"
  | Some ofs ->
      expand_addptrofs R20 R3 (Ptrofs.repr ofs);
      expand_storeind_ptr R20 r Ptrofs.zero

(* Auxiliary for 64-bit integer arithmetic built-ins.  They expand to
   two instructions, one computing the low 32 bits of the result,
   followed by another computing the high 32 bits.  In cases where
   the first instruction would overwrite arguments to the second
   instruction, we must go through R20 to hold the low 32 bits of the result.
*)

let expand_int64_arith conflict rl fn =
  if conflict then (fn R20; emit (Pmv(rl, R20))) else fn rl

(* Byte swaps. *)

let expand_bswap16 d s =
  emit (Pbstrpickw(d, Asm.R s, coqint_of_camlint 15l, _0));
  emit (Prevb2h(d, Asm.R d));
  emit (Pbstrpickw(d, Asm.R d, coqint_of_camlint 15l, _0))

let expand_bswap32 d s =
  emit (Prevb2h(d, Asm.R s));
  emit (Protriw(d, Asm.R d, coqint_of_camlint 16l))

let expand_bswap64 d s =
  emit (Prevb4h(d, Asm.R s));
  emit (Prevhd(d, Asm.R d))

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_membar", [], _ ->
     ()
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (* Byte swaps *)
  | "__builtin_bswap16", [BA(IR a1)], BR(IR res) ->
     expand_bswap16 res a1
  | ("__builtin_bswap"| "__builtin_bswap32"), [BA(IR a1)], BR(IR res) ->
     expand_bswap32 res a1
  | "__builtin_bswap64", [BA(IR a1)], BR(IR res) ->
     expand_bswap64 res a1
  | "__builtin_bswap64", [BA_splitlong(BA(IR ah), BA(IR al))],
                         BR_splitlong(BR(IR rh), BR(IR rl)) ->
     assert (ah = R13 && al = R12 && rh = R12 && rl = R13);
     expand_bswap32 R12 R12;
     expand_bswap32 R13 R13
  (* Count zeros *)
  | "__builtin_clz", [BA(IR a)], BR(IR res) ->
     emit (Pclzw(res, Asm.R a))
  | "__builtin_clzl", [BA(IR a)], BR(IR res) ->
     if Archi.ptr64 then emit (Pclzd (res, Asm.R a))
     else emit (Pclzw (res, Asm.R a))
  | "__builtin_clzll", [BA(IR a)], BR(IR res) ->
     emit (Pclzd (res, Asm.R a))
  | "__builtin_clzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Pbeqzw(Asm.R ah, lbl1));
     emit (Pclzw(res, Asm.R ah));
     emit (Pj_l lbl2);
     emit (Plabel lbl1);
     emit (Pclzw(res, Asm.R al));
     emit (Paddiw(res, Asm.R res, coqint_of_camlint 32l));
     emit (Plabel lbl2)
  | "__builtin_ctz", [BA(IR a)], BR(IR res) ->
     emit (Pctzw(res, Asm.R a))
  | "__builtin_ctzl", [BA(IR a)], BR(IR res) ->
     if Archi.ptr64 then emit (Pctzd (res, Asm.R a))
     else emit (Pctzw (res, Asm.R a))
  | "__builtin_ctzll", [BA(IR a)], BR(IR res) ->
     emit (Pctzd (res, Asm.R a))
  | "__builtin_ctzll", [BA_splitlong(BA(IR ah), BA(IR al))], BR(IR res) ->
     let lbl1 = new_label() in
     let lbl2 = new_label() in
     emit (Pbeqzw(Asm.R al, lbl1));
     emit (Pctzw(res, Asm.R al));
     emit (Pj_l lbl2);
     emit (Plabel lbl1);
     emit (Pctzw(res, Asm.R ah));
     emit (Paddiw(res, Asm.R res, coqint_of_camlint 32l));
     emit (Plabel lbl2)
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(FR a1)], BR(FR res) ->
     emit (Pfsqrtd(res, a1))
  | "__builtin_fmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmaddd(res, a1, a2, a3))
  | "__builtin_fmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfmsubd(res, a1, a2, a3))
  | "__builtin_fnmadd", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmaddd(res, a1, a2, a3))
  | "__builtin_fnmsub", [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR res) ->
      emit (Pfnmsubd(res, a1, a2, a3))
  | "__builtin_fmin", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmind(res, a1, a2))
  | "__builtin_fmax", [BA(FR a1); BA(FR a2)], BR(FR res) ->
      emit (Pfmaxd(res, a1, a2))
  (* 64-bit integer arithmetic for a 32-bit platform *)
  | "__builtin_negl", [BA_splitlong(BA(IR ah), BA(IR al))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah) rl
			(fun rl ->
                         emit (Psltwu (R1, R0, Asm.R al));
			 emit (Psubw (rl, R0, Asm.R al));
			 emit (Psubw (rh, R0, Asm.R ah));
			 emit (Psubw (rh, Asm.R rh, Asm.R R1)))
  | "__builtin_addl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = bl || rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Paddw (rl, Asm.R al, Asm.R bl));
                         emit (Psltwu (R1, Asm.R rl, Asm.R bl));
			 emit (Paddw (rh, Asm.R ah, Asm.R bh));
			 emit (Paddw (rh, Asm.R rh, Asm.R R1)))
  | "__builtin_subl", [BA_splitlong(BA(IR ah), BA(IR al));
                       BA_splitlong(BA(IR bh), BA(IR bl))],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
                         emit (Psltwu (R1, Asm.R al, Asm.R bl));
			 emit (Psubw (rl, Asm.R al, Asm.R bl));
			 emit (Psubw (rh, Asm.R ah, Asm.R bh));
			 emit (Psubw (rh, Asm.R rh, Asm.R R1)))
  | "__builtin_mull", [BA(IR a); BA(IR b)],
                      BR_splitlong(BR(IR rh), BR(IR rl)) ->
     expand_int64_arith (rl = a || rl = b) rl
                        (fun rl ->
                          emit (Pmulw (rl, Asm.R a, Asm.R b));
                          emit (Pmulhwu (rh, Asm.R a, Asm.R b)))
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

(* Expansion of instructions *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
      let sg = get_current_function_sig() in
      emit (Pmv (R19, R3));
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        let extra_sz = if n >= 8 then 0 else align ((8 - n) * wordsize) 16 in
        let full_sz = Z.add sz (Z.of_uint extra_sz) in
        expand_addptrofs R3 R3 (Ptrofs.repr (Z.neg full_sz));
        expand_storeind_ptr R19 R3 ofs;
        let va_ofs =
          Z.add full_sz (Z.of_sint ((n - 8) * wordsize)) in
        vararg_start_ofs := Some va_ofs;
        save_arguments n va_ofs
      end else begin
        expand_addptrofs R3 R3 (Ptrofs.repr (Z.neg sz));
        expand_storeind_ptr R19 R3 ofs;
        vararg_start_ofs := None
      end
  | Pfreeframe (sz, ofs) ->
     let sg = get_current_function_sig() in
     let extra_sz =
      if (sg.sig_cc.cc_vararg <> None) then begin
        let n = arguments_size sg in
        if n >= 8 then 0 else align ((8 - n) * wordsize) 16
      end else 0 in
     expand_addptrofs R3 R3 (Ptrofs.repr (Z.add sz (Z.of_uint extra_sz)))

  | Pseqw(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = R0 then begin
        emit (Psltuiw(rd, rs1, Int.one))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltuiw(rd, Asm.R rd, Int.one))
      end
  | Psnew(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = R0 then begin
        emit (Psltwu(rd, R0, rs1))
      end else begin
        emit (Pxorw(rd, rs1, rs2)); emit (Psltwu(rd, R0, Asm.R rd))
      end
  | Pseqd(rd, rs1, rs2) ->
      (* emulate based on the fact that x == 0 iff x <u 1 (unsigned cmp) *)
      if rs2 = R0 then begin
        emit (Psltuid(rd, rs1, Int64.one))
      end else begin
        emit (Pxord(rd, rs1, rs2)); emit (Psltuid(rd, Asm.R rd, Int64.one))
      end
  | Psned(rd, rs1, rs2) ->
      (* emulate based on the fact that x != 0 iff 0 <u x (unsigned cmp) *)
      if rs2 = R0 then begin
        emit (Psltdu(rd, R0, rs1))
      end else begin
        emit (Pxord(rd, rs1, rs2)); emit (Psltdu(rd, R0, Asm.R rd))
      end
  | Pcvtl2w(rd, rs) ->
      assert Archi.ptr64;
      emit (Paddiw(rd, rs, Int.zero))  (* 32-bit sign extension *)
  | Pcvtw2l(r) ->
      assert Archi.ptr64
      (* no-operation because the 32-bit integer was kept sign extended already *)

  | Pjal_r(r, sg) ->
      fixup_call sg; emit instr
  | Pjal_s(symb, sg) ->
      fixup_call sg; emit instr
  | Pj_r(r, sg) when r <> R1 ->
      fixup_call sg; emit instr
  | Pj_s(symb, sg) ->
      fixup_call sg; emit instr

  | Pbuiltin (ef,args,res) ->
     begin match ef with
     | EF_builtin (name,sg) ->
        expand_builtin_inline (camlstring_of_coqstring name) args res
     | EF_vload chunk ->
        expand_builtin_vload chunk args res
     | EF_vstore chunk ->
        expand_builtin_vstore chunk args
     | EF_annot_val (kind,txt,targ) ->
        expand_annot_val kind txt targ args res
     | EF_memcpy(sz, al) ->
        expand_builtin_memcpy (Z.to_int sz) (Z.to_int al) args
     | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
        emit instr
     | _ ->
        assert false
     end
  | _ ->
     emit instr

let int_reg_to_dwarf = function
               | R1  -> 1  | R2  -> 2  | R3  -> 3
   | R4  -> 4  | R5  -> 5  | R6  -> 6  | R7  -> 7
   | R8  -> 8  | R9  -> 9  | R10 -> 10 | R11 -> 11
   | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15
   | R16 -> 16 | R17 -> 17 | R18 -> 18 | R19 -> 19
   | R20 -> 20 | R21 -> 21 | R22 -> 22 | R23 -> 23
   | R24 -> 24 | R25 -> 25 | R26 -> 26 | R27 -> 27
   | R28 -> 28 | R29 -> 29 | R30 -> 30 | R31 -> 31

let float_reg_to_dwarf = function
   | F0  -> 32 | F1  -> 33 | F2  -> 34 | F3  -> 35
   | F4  -> 36 | F5  -> 37 | F6  -> 38 | F7  -> 39
   | F8  -> 40 | F9  -> 41 | F10 -> 42 | F11 -> 43
   | F12 -> 44 | F13 -> 45 | F14 -> 46 | F15 -> 47
   | F16 -> 48 | F17 -> 49 | F18 -> 50 | F19 -> 51
   | F20 -> 52 | F21 -> 53 | F22 -> 54 | F23 -> 55
   | F24 -> 56 | F25 -> 57 | F26 -> 58 | F27 -> 59
   | F28 -> 60 | F29 -> 61 | F30 -> 62 | F31 -> 63

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    fixup_function_entry fn.fn_sig;
    expand id (* sp= *) 2 preg_to_dwarf expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
