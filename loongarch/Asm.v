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

(** Abstract syntax and semantics for LoongArch assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** Integer registers. R0 is treated specially because it always reads as zero*)

Inductive ireg: Type :=
  | R1:  ireg | R2:  ireg | R3:  ireg | R4:  ireg | R5:  ireg
  | R6:  ireg | R7:  ireg | R8:  ireg | R9:  ireg | R10: ireg
  | R11: ireg | R12: ireg | R13: ireg | R14: ireg | R15: ireg
  | R16: ireg | R17: ireg | R18: ireg | R19: ireg | R20: ireg
  | R21: ireg | R22: ireg | R23: ireg | R24: ireg | R25: ireg
  | R26: ireg | R27: ireg | R28: ireg | R29: ireg | R30: ireg
  | R31: ireg.

Inductive ireg0: Type :=
  | R0: ireg0 | R: ireg -> ireg0.

Coercion R: ireg >-> ireg0.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg0_eq: forall (x y: ireg0), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

(** Floating-point registers. *)

Inductive freg: Type :=
  | F0: freg  | F1: freg  | F2: freg  | F3: freg
  | F4: freg  | F5: freg  | F6: freg  | F7: freg
  | F8: freg  | F9: freg  | F10: freg | F11: freg
  | F12: freg | F13: freg | F14: freg | F15: freg
  | F16: freg | F17: freg | F18: freg | F19: freg
  | F20: freg | F21: freg | F22: freg | F23: freg
  | F24: freg | F25: freg | F26: freg | F27: freg
  | F28: freg | F29: freg | F30: freg | F31: freg.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Condition Flag Register *)

Inductive cfreg: Type :=
  | FCC0: cfreg
  | FCC1: cfreg
  | FCC2: cfreg
  | FCC3: cfreg
  | FCC4: cfreg
  | FCC5: cfreg
  | FCC6: cfreg
  | FCC7: cfreg.
  
Lemma cfreg_eq: forall (x y: cfreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | CFR: cfreg -> preg                  (**r condition flag registers *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CFR: cfreg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. apply cfreg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Notation "'SP'" := R3 (only parsing) : asm.
Notation "'RA'" := R1 (only parsing) : asm.

(** Offsets for load and store instructions.  An offset is an immediate integer *)

Inductive offset := Ofsimm (ofs: ptrofs).

Definition label := positive.

(**
  For 32- and 64-bit integer arithmetic, the LoongArch instruction set comprises
  generic integer operations such as ADD that operate over the full width
  of an integer register (either 32 or 64 bit), plus specific instructions
  such as ADDW that normalize their results to signed 32-bit integers.
  Other instructions such as AND work equally well over 32- and 64-bit
  integers, with the convention that 32-bit integers are represented
  sign-extended in 64-bit registers.

  This clever design is challenging to formalize in the CompCert value
  model.  As a first step, we follow a more traditional approach,
  also used in the x86 port, whereas we have two sets of (pseudo-)
  instructions, one for 32-bit integer arithmetic, with suffix W,
  the other for 64-bit integer arithmetic, with suffix D.  The mapping
  to actual instructions is done when printing assembly code, as follows:
  - In 32-bit mode:
    ADDW becomes ADDW, ADDD is an error, ANDW becomes AND, ANDL is an error.
  - In 64-bit mode:
    ADDW becomes ADDW, ADDD becomes ADD, ANDW and ANDL both become AND.
*)

Inductive instruction : Type :=
(** Arithmetic Operation Instructions *)
  | Paddw   (rd: ireg) (rj rk: ireg0)              (**r integer addition *)
  | Paddd   (rd: ireg) (rj rk: ireg0)              (**r integer addition *)
  | Psubw   (rd: ireg) (rj rk: ireg0)              (**r integer subtraction *)
  | Psubd   (rd: ireg) (rj rk: ireg0)              (**r integer subtraction *)

  | Paddiw  (rd: ireg) (rj: ireg0) (si12: int)     (**r add immediate *)
  | Paddid  (rd: ireg) (rj: ireg0) (si12: int64)   (**r add immediate *)
  (** addu16i.d*)

  (** alsl.{w[u]/D} *)

  | Plu12iw (rd: ireg)             (si20: int)     (**r load upper-immediate *)
  | Plu12id (rd: ireg)             (si20: int64)   (**r load upper-immediate *)
  | Plu32id (rd: ireg)             (si20: int64)   (**r load upper-immediate *)
  | Plu52id (rd: ireg) (rj: ireg0) (si12: int64)   (**r load upper-immediate *)

  | Psltw   (rd: ireg) (rj rk: ireg0)              (**r set-less-than *)
  | Psltwu  (rd: ireg) (rj rk: ireg0)              (**r set-less-than unsigned *)
  | Psltd   (rd: ireg) (rj rk: ireg0)              (**r set-less-than *)
  | Psltdu  (rd: ireg) (rj rk: ireg0)              (**r set-less-than unsigned *)

  | Psltiw  (rd: ireg) (rj: ireg0) (si12: int)     (**r set-less-than immediate *)
  | Psltuiw (rd: ireg) (rj: ireg0) (si12: int)     (**r set-less-than unsigned immediate *)
  | Psltid  (rd: ireg) (rj: ireg0) (si12: int64)   (**r set-less-than immediate *) 
  | Psltuid (rd: ireg) (rj: ireg0) (si12: int64)   (**r set-less-than unsigned immediate *)

  (**r pcaddi, pcaddu12i pcaddu18i, pcalau12i *)

  | Pandw   (rd: ireg) (rj rk: ireg0)              (**r bitwise and *)
  | Porw    (rd: ireg) (rj rk: ireg0)              (**r bitwise or *)
  | Pnorw   (rd: ireg) (rj rk: ireg0)              (**r bitwise nor *)
  | Pxorw   (rd: ireg) (rj rk: ireg0)              (**r bitwise xor *)
  | Pandnw  (rd: ireg) (rj rk: ireg0)              (**r bitwise andn *)
  | Pornw   (rd: ireg) (rj rk: ireg0)              (**r bitwise orn *)
  | Pandd   (rd: ireg) (rj rk: ireg0)              (**r bitwise and *)
  | Pord    (rd: ireg) (rj rk: ireg0)              (**r bitwise or *)
  | Pnord   (rd: ireg) (rj rk: ireg0)              (**r bitwise nor *)
  | Pxord   (rd: ireg) (rj rk: ireg0)              (**r bitwise xor *)
  | Pandnd  (rd: ireg) (rj rk: ireg0)              (**r bitwise andn *)
  | Pornd   (rd: ireg) (rj rk: ireg0)              (**r bitwise orn *)

  | Pandiw  (rd: ireg) (rj: ireg0) (ui12: int)     (**r and immediate *)
  | Poriw   (rd: ireg) (rj: ireg0) (ui12: int)     (**r or immediate *)
  | Pxoriw  (rd: ireg) (rj: ireg0) (ui12: int)     (**r xor immediate *)
  | Pandid  (rd: ireg) (rj: ireg0) (ui12: int64)   (**r and immediate *)
  | Porid   (rd: ireg) (rj: ireg0) (ui12: int64)   (**r or immediate *)
  | Pxorid  (rd: ireg) (rj: ireg0) (ui12: int64)   (**r xor immediate *)

  | Pnop : instruction                             (**r nop instruction *)

  | Pmulw   (rd: ireg) (rj rk: ireg0)              (**r integer multiply low *)
  | Pmulhw  (rd: ireg) (rj rk: ireg0)              (**r integer multiply high signed *)
  | Pmulhwu (rd: ireg) (rj rk: ireg0)              (**r integer multiply high unsigned *)  
  | Pmuld   (rd: ireg) (rj rk: ireg0)              (**r integer multiply low *)
  | Pmulhd  (rd: ireg) (rj rk: ireg0)              (**r integer multiply high signed *)
  | Pmulhdu (rd: ireg) (rj rk: ireg0)              (**r integer multiply high unsigned *)
  
  (**r mulw.d.w[u] *)

  | Pdivw   (rd: ireg) (rj rk: ireg0)              (**r integer division *)
  | Pmodw   (rd: ireg) (rj rk: ireg0)              (**r integer remainder *)
  | Pdivwu  (rd: ireg) (rj rk: ireg0)              (**r unsigned integer division *)
  | Pmodwu  (rd: ireg) (rj rk: ireg0)              (**r unsigned integer remainder *)
  | Pdivd   (rd: ireg) (rj rk: ireg0)              (**r integer division *)
  | Pmodd   (rd: ireg) (rj rk: ireg0)              (**r integer remainder *)
  | Pdivdu  (rd: ireg) (rj rk: ireg0)              (**r unsigned integer division *)
  | Pmoddu  (rd: ireg) (rj rk: ireg0)              (**r unsigned integer remainder *)

(** Bit-shift Instructions *)  
  | Psllw   (rd: ireg) (rj rk: ireg0)              (**r shift-left-logical *)
  | Psrlw   (rd: ireg) (rj rk: ireg0)              (**r shift-right-logical *)
  | Psraw   (rd: ireg) (rj rk: ireg0)              (**r shift-right-arith *)
  (** rotr.w *)
  | Pslld   (rd: ireg) (rj rk: ireg0)              (**r shift-left-logical *)
  | Psrld   (rd: ireg) (rj rk: ireg0)              (**r shift-right-logical *)
  | Psrad   (rd: ireg) (rj rk: ireg0)              (**r shift-right-arith *)
  (** rotr.d *)

  | Pslliw  (rd: ireg) (rj: ireg0) (ui5: int)      (**r shift-left-logical immediate *)
  | Psrliw  (rd: ireg) (rj: ireg0) (ui5: int)      (**r shift-right-logical immediate *)
  | Psraiw  (rd: ireg) (rj: ireg0) (ui5: int)      (**r shift-right-arith immediate *)
  | Protriw (rd: ireg) (rj: ireg0) (ui5: int)      (**r cyclical shift-right immediate *)
  | Psllid  (rd: ireg) (rj: ireg0) (ui6: int)      (**r shift-left-logical immediate *)
  | Psrlid  (rd: ireg) (rj: ireg0) (ui6: int)      (**r shift-right-logical immediate *)
  | Psraid  (rd: ireg) (rj: ireg0) (ui6: int)      (**r shift-right-arith immediate *)
  (** rotri.d *)

(** Bit-manipulation Instructions *)
  (** ext.w.{b/h} *)

  (** clo.{w/d} *)
  | Pclzw (rd: ireg) (rj: ireg0)                   (**r count leading zeros *)
  | Pclzd (rd: ireg) (rj: ireg0)                   (**r count leading zeros *)
  (** cto.{w/d} *)
  | Pctzw (rd: ireg) (rj: ireg0)                   (**r count tailing zeros *)
  | Pctzd (rd: ireg) (rj: ireg0)                   (**r count tailing zeros *)

  (** bytepick.{w/d} *)

  | Prevb2h (rd: ireg) (rj: ireg0)                 (**r reverse bytes *)
  | Prevb4h (rd: ireg) (rj: ireg0)                 (**r reverse bytes *)
  (** revb.{2w/d} *)

  (** revh.2w *)
  | Prevhd  (rd: ireg) (rj: ireg0)                 (**r reverse bytes *)

  (** bitrev.{4b/8b} *)

  (** bitrev.{w/d} *)

  (** bstrins.{w/d} *)

  | Pbstrpickw (rd: ireg) (rj: ireg0) (m l: int)   (**r extract  *)
  (** bstrpick.d *)

  (** maskeqz, masknez *)

(** Branch Instructions *)
  | Pbeqw   (rj rd: ireg0) (l: label)              (**r branch-if-equal *)
  | Pbnew   (rj rd: ireg0) (l: label)              (**r branch-if-not-equal signed *)
  | Pbltw   (rj rd: ireg0) (l: label)              (**r branch-if-less signed *)  
  | Pbgew   (rj rd: ireg0) (l: label)              (**r branch-if-greater-or-equal signed *)
  | Pbltwu  (rj rd: ireg0) (l: label)              (**r branch-if-less unsigned *)
  | Pbgewu  (rj rd: ireg0) (l: label)              (**r branch-if-greater-or-equal unsigned *)
  | Pbeqd   (rj rd: ireg0) (l: label)              (**r branch-if-equal *)
  | Pbned   (rj rd: ireg0) (l: label)              (**r branch-if-not-equal signed *)
  | Pbltd   (rj rd: ireg0) (l: label)              (**r branch-if-less signed *)
  | Pbged   (rj rd: ireg0) (l: label)              (**r branch-if-greater-or-equal signed *)
  | Pbltdu  (rj rd: ireg0) (l: label)              (**r branch-if-less unsigned *)
  | Pbgedu  (rj rd: ireg0) (l: label)              (**r branch-if-greater-or-equal unsigned *)

  | Pbeqzw  (rj: ireg0) (l: label)                 (**r branch-if-equal zero *)
  | Pbnezw  (rj: ireg0) (l: label)                 (**r branch-if-not-equal zero *)
  | Pbeqzd  (rj: ireg0) (l: label)                 (**r branch-if-equal zero *)
  | Pbnezd  (rj: ireg0) (l: label)                 (**r branch-if-not-equal zero *)

  | Pj_l    (l: label)                             (**r jump to label *)
  | Pj_s    (symb: ident) (sg: signature)          (**r jump to symbol *)
  | Pj_r    (r: ireg)     (sg: signature)          (**r jump register *)
  | Pjal_s  (symb: ident) (sg: signature)          (**r jump-and-link symbol *)
  | Pjal_r  (r: ireg)     (sg: signature)          (**r jump-and-link register *)
(** Common Memory Access Instructions *)
  | Pldb     (rd: ireg) (rj: ireg) (ofs: offset)   (**r load signed int8 *)
  | Pldh     (rd: ireg) (rj: ireg) (ofs: offset)   (**r load signed int16 *)
  | Pldw     (rd: ireg) (rj: ireg) (ofs: offset)   (**r load int32 *)
  | Pldd     (rd: ireg) (rj: ireg) (ofs: offset)   (**r load int64 *)
  | Pldbu    (rd: ireg) (rj: ireg) (ofs: offset)   (**r load unsigned int8 *)
  | Pldhu    (rd: ireg) (rj: ireg) (ofs: offset)   (**r load unsigned int16 *)
  (** ld.wu *)
  | Pldw_a   (rd: ireg) (rj: ireg) (ofs: offset)   (**r load any32 *)
  | Pldd_a   (rd: ireg) (rj: ireg) (ofs: offset)   (**r load any64 *)
  | Pstb     (rd: ireg) (rj: ireg) (ofs: offset)   (**r store int8 *)
  | Psth     (rd: ireg) (rj: ireg) (ofs: offset)   (**r store int16 *)
  | Pstw     (rd: ireg) (rj: ireg) (ofs: offset)   (**r store int32 *)
  | Pstd     (rd: ireg) (rj: ireg) (ofs: offset)   (**r store int64 *)
  | Pstw_a   (rd: ireg) (rj: ireg) (ofs: offset)   (**r store any32 *)
  | Pstd_a   (rd: ireg) (rj: ireg) (ofs: offset)   (**r store any64 *)
  
  (** ldx.{b[u]/h[u]/w[u]/d}, stx.{b/h/w/d} *)

  (** ldptr.{w/d}, stptr.{w/d} *)

  (** preld *)

  (** preldx *)

(** Floating-Point Arithmetic Operation Instructions *)
  | Pfadds   (fd: freg) (fj fk: freg)              (**r addition *)
  | Pfaddd   (fd: freg) (fj fk: freg)              (**r addition *)
  | Pfsubs   (fd: freg) (fj fk: freg)              (**r subtraction *)
  | Pfsubd   (fd: freg) (fj fk: freg)              (**r subtraction *)
  | Pfmuls   (fd: freg) (fj fk: freg)              (**r multiplication *)
  | Pfmuld   (fd: freg) (fj fk: freg)              (**r multiplication *)
  | Pfdivs   (fd: freg) (fj fk: freg)              (**r division *)
  | Pfdivd   (fd: freg) (fj fk: freg)              (**r division *)

  | Pfmadds  (fd: freg) (fj fk fa: freg)           (**r fused multiply-add *)
  | Pfmaddd  (rd: freg) (fj fk fa: freg)           (**r fused multiply-add *)
  | Pfmsubs  (fd: freg) (fj fk fa: freg)           (**r fused multiply-sub *)
  | Pfmsubd  (rd: freg) (fj fk fa: freg)           (**r fused multiply-sub *)
  | Pfnmadds (fd: freg) (fj fk fa: freg)           (**r fused negated multiply-add *)
  | Pfnmaddd (rd: freg) (fj fk fa: freg)           (**r fused negated multiply-add *)
  | Pfnmsubs (fd: freg) (fj fk fa: freg)           (**r fused negated multiply-sub *)
  | Pfnmsubd (rd: freg) (fj fk fa: freg)           (**r fused negated multiply-sub *)

  | Pfmaxs   (fd: freg) (fj fk: freg)              (**r maximum *)
  | Pfmaxd   (fd: freg) (fj fk: freg)              (**r maximum *)
  | Pfmins   (fd: freg) (fj fk: freg)              (**r minimum *)
  | Pfmind   (fd: freg) (fj fk: freg)              (**r minimum *)

  | Pfabss   (fd: freg) (fj: freg)                 (**r absolute value *)
  | Pfabsd   (rd: freg) (rj: freg)                 (**r absolute value *)
  | Pfnegs   (fd: freg) (fj: freg)                 (**r negation *) 
  | Pfnegd   (rd: freg) (rj: freg)                 (**r negation *)
  
  | Pfsqrts  (fd: freg) (fj: freg)                 (**r square-root *)
  | Pfsqrtd  (fd: freg) (fj: freg)                 (**r square-root *)
  (** f{recip/rsqrt}.{s/d} *)

  (** f{scaleb/logb/copysign}.{s/d} *)
  
  (** fclass.{s/d} *)

(** Floating-Point Comparison Instructions *)
  (** fcmp.cond.{s/d} *)
  | Pfeqs    (cc: cfreg) (fj fk: freg)             (**r compare equal *)
  | Pflts    (cc: cfreg) (fj fk: freg)             (**r compare less-than *)
  | Pfles    (cc: cfreg) (fj fk: freg)             (**r compare less-than/equal *)
  | Pfeqd    (cc: cfreg) (fj fk: freg)             (**r compare equal *)
  | Pfltd    (cc: cfreg) (fj fk: freg)             (**r compare less-than *)
  | Pfled    (cc: cfreg) (fj fk: freg)             (**r compare less-than/equal *)
(** Floating-Point Conversion Instructions *)
  | Pfcvtsd  (fd: freg) (fj: freg)                 (**r float   -> float32 *)
  | Pfcvtds  (fd: freg) (fj: freg)                 (**r float32 -> float   *)

  (** ffint, ftint, frint *)
  | Pfcvtws  (rd: ireg) (rs: freg)                 (**r float32 -> int32 conversion *)
  | Pfcvtsw  (rd: freg) (rs: ireg0)                (**r int32 -> float32 conversion *)
  | Pfcvtls  (rd: ireg) (rs: freg)                 (**r float32 -> int64 conversion *)
  | Pfcvtsl  (rd: freg) (rs: ireg0)                (**r int64 -> float32 conversion *)
  | Pfcvtwd  (rd: ireg) (rs: freg)                 (**r float -> int32 conversion *)
  | Pfcvtdw  (rd: freg) (rs: ireg0)                (**r int32 -> float conversion *)
  | Pfcvtld  (rd: ireg) (rs: freg)                 (**r float -> int64 conversion *)
  | Pfcvtdl  (rd: freg) (rs: ireg0)                (**r int64 -> float conversion *)
  | Pfmvxs   (rd: ireg) (rs: freg)                 (**r move FP single to integer register *)
  | Pfmvsx   (rd: freg) (rs: ireg)                 (**r move integer register to FP single *)
  | Pfmvxd   (rd: ireg) (rs: freg)                 (**r move FP double to integer register *)
  | Pfmvdx   (rd: freg) (rs: ireg)                 (**r move integer register to FP double *)
(** Floating-Point Move Instructions *)
  (** fmov.s *)
  (** fmov.d 
      fmov.d preserves single-precision register contents,
      and hence is applicable to both single- and double-precision moves. *)
  | Pfmv     (rd: freg) (rs: freg)                 (**r move *)

  (** fsel *)

  (** mov* *)
  | Pmovcf2gr (rd: ireg) (cj: cfreg)               (**r move CFR to GR's lowest bit*)
(** Floating-Point Branch Instructions *)
  | Pbceqz   (cj: cfreg) (l: label)                (**r branch-if-equal-0 *)
  | Pbcnez   (cj: cfreg) (l: label)                (**r branch-if-not-equal-0 *)
(** Floating-Point Common Memory Access Instructions *)
  | Pflds     (fd: freg) (rj: ireg) (ofs: offset)  (**r load float *)
  | Pfldd     (fd: freg) (rj: ireg) (ofs: offset)  (**r load 64-bit float *)
  | Pfsts     (fd: freg) (rj: ireg) (ofs: offset)  (**r store float *)
  | Pfstd     (fd: freg) (rj: ireg) (ofs: offset)  (**r store 64-bit float *)
  | Pfldd_a   (fd: freg) (rj: ireg) (ofs: offset)  (**r load any64 *)
  | Pfstd_a   (fd: freg) (rj: ireg) (ofs: offset)  (**r store any64 *)

  (** fldx.{s/d}, fstx.{s/d}*)

(** Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)              (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)              (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                           (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident)             (**r load the address of a symbol *)
  | Ploadli (rd: ireg) (i: int64)                  (**r load an immediate int64 *)
  | Ploadfi (rd: freg) (f: float)                  (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)           (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
            -> builtin_res preg -> instruction     (**r built-in function (pseudo) *)

  | Pmv     (rd: ireg) (rs: ireg)                  (**r integer move *)
  | Pseqw   (rd: ireg) (rj rk: ireg0)              (**r [rd <- rj == rk] (pseudo) *)
  | Psnew   (rd: ireg) (rj rk: ireg0)              (**r [rd <- rj != rk] (pseudo) *)
  | Pseqd   (rd: ireg) (rj rk: ireg0)              (**r [rd <- rj == rk] (pseudo) *)
  | Psned   (rd: ireg) (rj rk: ireg0)              (**r [rd <- rj != rk] (pseudo) *)
  | Pcvtl2w (rd: ireg) (rj: ireg0)                 (**r int64->int32 (pseudo) *)
  | Pcvtw2l (r: ireg).                             (**r int32 signed -> int64 (pseudo) *)

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

- [Ploadli rd ival]: load an immediate 64-bit integer into an integerregister rd.

- [Ploadfi rd fval]: load a double FP constant fval into a float register rd.

- [Ploadsi rd fval]: load a single FP constant fval into a float register rd.

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        move    $r19, $sp
        subi    $sp,  $sp, #sz
        st      $r19, $sp, #pos
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is just an increment of [sp]:
<<
        addi    $sp, $sp, #sz
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        la      $r20, table
        add     $r20, $r20, reg
        jr      $r20
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pseq rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        sltiu   rd, rd, 1
>>
  The [xor] is omitted if one of [rs1] and [rs2] is [x0].

- [Psne rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        sltu    rd, r0, rd
>>
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tint] or [Tlong] (in 64 bit mode),
  and float registers to values of type [Tsingle] or [Tfloat]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Definition get0w (rs: regset) (r: ireg0) : val :=
  match r with
  | R0 => Vint Int.zero
  | R r => rs r
  end.

Definition get0l (rs: regset) (r: ireg0) : val :=
  match r with
  | R0 => Vlong Int64.zero
  | R r => rs r
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (get0w a b) (at level 1) : asm.
Notation "a ### b" := (get0l a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: ireg) (ofs: offset) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#d <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: ireg) (ofs: offset) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual LoongArch instructions, the cases are straightforward
    transliterations of the informal descriptions given in the LoongArch
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the LoongArch code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
(** Arithmetic Operation Instructions *)
  | Paddw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m
  | Paddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
  | Psubw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m
  | Psubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
  
  | Paddiw d s i =>
      Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m
  | Paddid d s i =>
      Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m
  

  | Plu12iw d i =>
      Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m
  | Plu12id d i =>
      Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m
  | Plu32id d i =>
      Next (nextinstr (rs#d <- (Val.addl rs###d (Vlong (Int64.sign_ext 52 (Int64.shl i (Int64.repr 32))))))) m
  | Plu52id d s i =>
      Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong (Int64.shl i (Int64.repr 52)))))) m

  | Psltw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m
  | Psltwu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m
  | Psltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m
  | Psltdu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m
  
  | Psltiw d s i =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m
  | Psltuiw d s i =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m
  | Psltid d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m
  | Psltuid d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m
  
  | Pandw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m
  | Porw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m
  | Pnorw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.notint (Val.or rs##s1 rs##s2)))) m
  | Pxorw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m
  | Pandnw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs##s1 (Val.notint (rs##s2))))) m
  | Pornw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs##s1 (Val.notint (rs##s2))))) m
  | Pandd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
  | Pord d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m
  | Pnord d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.notl (Val.orl rs###s1 rs###s2)))) m
  | Pxord d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m
  | Pandnd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.andl rs###s1 (Val.notl (rs###s2))))) m
  | Pornd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.orl rs###s1 (Val.notl (rs###s2))))) m  
  
  | Pandiw d s i =>
      Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m
  | Poriw d s i =>
      Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m
  | Pxoriw d s i =>
      Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m 
  | Pandid d s i =>
      Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m
  | Porid d s i =>
      Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m
  | Pxorid d s i =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m

  | Pmulw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m
  | Pmulhw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m
  | Pmulhwu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m
  | Pmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
  | Pmulhd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m
  | Pmulhdu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m

  | Pdivw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m
  | Pmodw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m
  | Pdivwu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m
  | Pmodwu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m
  | Pdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m
  | Pmodd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m 
  | Pdivdu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m
  | Pmoddu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m
  
  | Psllw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m
  | Psrlw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
  | Psraw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m
  | Pslld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
  | Psrld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
  | Psrad d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m

  | Pslliw d s i =>
      Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m
  | Psrliw d s i =>
      Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m
  | Psraiw d s i =>
      Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m    
  | Psllid d s i =>
      Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m
  | Psrlid d s i =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m
  | Psraid d s i =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m

(** Branch Instructions *)
  | Pbeqw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2)
  | Pbnew s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2)
  | Pbltw s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)
  | Pbgew s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)
  | Pbltwu s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2)
  | Pbgewu s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2)
  | Pbeqd s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2)
  | Pbned s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2)
  | Pbltd s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)
  | Pbged s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)
  | Pbltdu s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2)
  | Pbgedu s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2)

  | Pbeqzw s1 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 (Vint Int.zero))
  | Pbnezw s1 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 (Vint Int.zero))
  | Pbeqzd s1 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs##s1 (Vint Int.zero))
  | Pbnezd s1 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs##s1 (Vint Int.zero))

  | Pj_l l =>
      goto_label f l rs m
  | Pj_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pj_r r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pjal_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
           ) m
  | Pjal_r r sg =>
      Next (rs#PC <- (rs#r)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
           ) m    

(** Common Memory Access Instructions *)
  | Pldb d a ofs =>
      exec_load Mint8signed rs m d a ofs
  | Pldh d a ofs =>
      exec_load Mint16signed rs m d a ofs
      | Pldw d a ofs =>
      exec_load Mint32 rs m d a ofs
      | Pldd d a ofs =>
      exec_load Mint64 rs m d a ofs
  | Pldbu d a ofs =>
      exec_load Mint8unsigned rs m d a ofs 
  | Pldhu d a ofs =>
      exec_load Mint16unsigned rs m d a ofs  
  | Pldw_a d a ofs =>
      exec_load Many32 rs m d a ofs  
  | Pldd_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Pstb s a ofs =>
      exec_store Mint8unsigned rs m s a ofs
  | Psth s a ofs =>
      exec_store Mint16unsigned rs m s a ofs
  | Pstw s a ofs =>
      exec_store Mint32 rs m s a ofs
  | Pstd s a ofs =>
      exec_store Mint64 rs m s a ofs
  | Pstw_a s a ofs =>
      exec_store Many32 rs m s a ofs 
  | Pstd_a s a ofs =>
      exec_store Many64 rs m s a ofs

(** Floating-Point Arithmetic Operation Instructions *)
  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m

  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m
  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m
  | Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfnegd d s =>
      Next (nextinstr (rs#d <- (Val.negf rs#s))) m
  
(** Floating-Point Comparison Instructions *)  
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

(** Floating-Point Conversion Instructions *)
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m
  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtws d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtls d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtsl d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtwd d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtld d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtdl d s =>
      Next (nextinstr (rs#F0 <- Vundef #d <- (Val.maketotal (Val.floatoflong rs###s)))) m

(** Floating-Point Move Instructions *)
  | Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m
  | Pmovcf2gr d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** Floating-Point Branch Instructions *)
  | Pbceqz c l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs#c (Vint (Int.repr 0)))
  | Pbcnez c l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs#c (Vint (Int.repr 0)))

(** Floating-Point Conversion Instructions *)
  | Pflds d a ofs =>
      exec_load Mfloat32 rs m d a ofs
  | Pfldd d a ofs =>
      exec_load Mfloat64 rs m d a ofs
  | Pfsts s a ofs =>
      exec_store Mfloat32 rs m s a ofs
  | Pfstd s a ofs =>
      exec_store Mfloat64 rs m s a ofs
  | Pfldd_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Pfstd_a s a ofs =>
      exec_store Many64 rs m s a ofs
  
(** Pseudo-instructions *)
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #R19 <- (rs SP) #SP <- sp #R20 <- Vundef #R22 <- Vundef)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #R20 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd s =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge s Ptrofs.zero))) m
  | Ploadli rd i =>
      Next (nextinstr (rs#R20 <- Vundef #rd <- (Vlong i))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#R20 <- Vundef #rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#R20 <- Vundef #rd <- (Vsingle f))) m
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#R12 <- Vundef #R20 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  | Pmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m
  | Pseqw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m
  | Psnew d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m 
  | Pseqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m
  | Psned d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m
  | Pcvtl2w d s =>
      Next (nextinstr (rs#d <- (Val.loword rs##s))) m
  | Pcvtw2l r =>
      Next (nextinstr (rs#r <- (Val.longofint rs#r))) m

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pnop
  | Protriw _ _ _

  | Pclzw _ _
  | Pclzd _ _
  | Pctzw _ _
  | Pctzd _ _
  | Prevb2h _ _
  | Prevb4h _ _
  | Prevhd _ _
  | Pbstrpickw _ _ _ _

  | Pfmadds _ _ _ _
  | Pfmaddd _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubs _ _ _ _
  | Pfnmsubd _ _ _ _

  | Pfmaxs _ _ _
  | Pfmaxd _ _ _
  | Pfmins _ _ _
  | Pfmind _ _ _

  | Pfsqrts _ _
  | Pfsqrtd _ _

  | Pfmvxs _ _
  | Pfmvsx _ _
  | Pfmvxd _ _
  | Pfmvdx _ _
    => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the LoongArch view.  Note that no LTL register maps to [R20], [R22],
  which are reserved as temporary, to be used by the generated code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | Machregs.R4  => R4  | Machregs.R5  => R5  | Machregs.R6  => R6  | Machregs.R7  => R7
  | Machregs.R8  => R8  | Machregs.R9  => R9  | Machregs.R10 => R10 | Machregs.R11 => R11
  | Machregs.R12 => R12 | Machregs.R13 => R13 | Machregs.R14 => R14 | Machregs.R15 => R15
  | Machregs.R16 => R16 | Machregs.R17 => R17 | Machregs.R18 => R18 | Machregs.R19 => R19
  | Machregs.R23 => R23
  | Machregs.R24 => R24 | Machregs.R25 => R25 | Machregs.R26 => R26 | Machregs.R27 => R27
  | Machregs.R28 => R28 | Machregs.R29 => R29 | Machregs.R30 => R30 | Machregs.R31 => R31

  | Machregs.F0  => F0  | Machregs.F1  => F1  | Machregs.F2  => F2  | Machregs.F3  => F3
  | Machregs.F4  => F4  | Machregs.F5  => F5  | Machregs.F6  => F6  | Machregs.F7  => F7
  | Machregs.F8  => F8  | Machregs.F9  => F9  | Machregs.F10 => F10 | Machregs.F11 => F11
  | Machregs.F12 => F12 | Machregs.F13 => F13 | Machregs.F14 => F14 | Machregs.F15 => F15
  | Machregs.F16 => F16 | Machregs.F17 => F17 | Machregs.F18 => F18 | Machregs.F19 => F19
  | Machregs.F20 => F20 | Machregs.F21 => F21 | Machregs.F22 => F22 | Machregs.F23 => F23
  | Machregs.F24 => F24 | Machregs.F25 => F25 | Machregs.F26 => F26 | Machregs.F27 => F27
  | Machregs.F28 => F28 | Machregs.F29 => F29 | Machregs.F30 => F30 | Machregs.F31 => F31
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use LoongArch registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (Locations.R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs #R1 <- Vundef #R20 <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs R4 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR R20 => false
  | IR R21 => false
  | IR R22 => false
  | IR _   => true
  | FR _   => true
  | CFR _ => false
  | PC     => false
  end.
