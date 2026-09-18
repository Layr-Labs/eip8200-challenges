import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P15
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `R1B` guard of the appended Montgomery path

`R1B` occupies instruction indices 1895..1907 (pc 2674..3015).  It is entered
at pc 2674 with stack `[px, ret]`, exactly the calling convention of
`DOUBLE256`, and it dispatches:

* when the modulus's most significant bit is clear it jumps straight to
  `DOUBLE256` (pc 2038) with the stack and memory untouched, so that path is
  literally the old one;
* otherwise it stores `1` at `TN = 0x2020` and jumps to `CSUB` (pc 2432) with
  the same `[px, ret]` frame.

The second branch is the point.  `CSUB` computes `t[n] * radix ^ n + t_low`
reduced against `m`, and at this point in the setup the `t` block at
`TS = 0x2040` is still zero, so with `t[n] = 1` it computes `radix ^ n mod m`
— which is `R mod m`, the value the 256 modular doublings of `DOUBLE256`
produce.  Its side condition `t[n] * radix ^ n + t_low < 2 * m` is exactly the
top-bit guard: a modulus with its most significant bit set satisfies
`radix ^ n < 2 * m`, strictly because `m` is odd and `radix ^ n / 2` is not.

This module depends on `Fast.Csub` only through the value contract
`Csub.csub_correct`; the trace itself is spliced in by the caller.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R1

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## The guard -/

/-- The modulus's most significant limb has its top bit set.  This is the
decidable test the block performs with `MLOAD 0; PUSH1 255; SHR`. -/
def TopBitSet (mem : ByteArray) : Prop :=
  2 ^ 255 ≤ (MachineState.readWord mem 0).toNat

instance (mem : ByteArray) : Decidable (TopBitSet mem) := by
  unfold TopBitSet; infer_instance

/-- **The guard is exactly `CSUB`'s side condition.**  If the most significant
limb of an `n`-limb modulus has its top bit set then `radix ^ n < 2 * mm`.
The inequality is strict because `mm` is odd while `radix ^ n / 2` is a power
of two above one. -/
theorem radix_pow_lt_two_mul {mem : ByteArray} {n mm : Nat} (hn : 1 ≤ n)
    (hodd : mm % 2 = 1) (hmod : Model.FastRepresents mem 0 n mm)
    (htop : TopBitSet mem) :
    Limbs.radix ^ n < 2 * mm := by
  have htop' : 2 ^ 255 ≤ (MachineState.readWord mem 0).toNat := htop
  have hlimb : (MachineState.readWord mem 0).toNat =
      mm / Limbs.radix ^ (n - 1) % Limbs.radix := by
    simpa using Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  -- the modulus's top limb bounds `mm` from below, `% radix` only shrinks it
  have hge : 2 ^ 255 ≤ mm / Limbs.radix ^ (n - 1) :=
    le_trans (hlimb ▸ htop') (Nat.mod_le _ _)
  have hmul : 2 ^ 255 * Limbs.radix ^ (n - 1) ≤ mm :=
    le_trans (Nat.mul_le_mul_right _ hge) (Nat.div_mul_le_self _ _)
  have h2 : (2 : Nat) * 2 ^ 255 = Limbs.radix := by norm_num [Limbs.radix]
  have hhalf : 2 * (2 ^ 255 * Limbs.radix ^ (n - 1)) = Limbs.radix ^ n := by
    rw [← mul_assoc, h2, ← pow_succ']
    congr 1
    omega
  -- `radix ^ n / 2` is even and `mm` is odd, so the bound cannot be tight
  have heven : 2 ^ 255 * Limbs.radix ^ (n - 1) =
      2 * (2 ^ 254 * Limbs.radix ^ (n - 1)) := by
    rw [← mul_assoc]
    congr 1
  omega

/-- `t[n] := 1` at `TN = 0x2020`, the only memory the guard block writes. -/
def tnMem (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 1 32) 2080

/-! ## States at the block boundaries -/

/-- Subroutine entry, pc 2674, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1278
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The fall-back target, pc 2038: `DOUBLE256`'s own entry, reached with the
stack and memory exactly as they arrived. -/
def dblState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1069
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Between the test and the store, pc 2688. -/
def fastState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1289
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The `CSUB` entry, pc 2432, stack `[px, ret]`, with `t[n] = 1` stored.
`TN = 0x2020` lies below the `296` words the caller already holds, so the
store does not grow memory. -/
def csubState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4086
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := tnMem mem }

/-! ## Traces -/

