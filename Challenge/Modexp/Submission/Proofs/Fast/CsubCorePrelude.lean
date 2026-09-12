import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P11
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P12
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P13
import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixed
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `ADDMOD` and `CSUB` subroutines of the appended Montgomery path

`ADDMOD` starts at PC 2137 and falls through into `CSUB` at PC 2220.
`CSUB` dispatches at PC 4975 to the generic loop at PC 2225 or the fixed
eight/four-limb paths. The fixed paths share the suffix beginning at PC 5133.

`ADDMOD` is entered with stack `[pa, pb, pd, ret]`.  It adds the `n`-limb
big-endian blocks at `pa` and `pb` limb by limb from the least significant
limb upwards into the CIOS `t` area, stores the carry-out at `TN = 0x2020`
and falls into `CSUB`.

`CSUB` is entered with stack `[pd, ret]` and the value
`t = t[n] * radix ^ n + t_low` held as `t[n]` at `TN` and `t_low` in the
`n`-limb block at `TS = 0x2040`.  It computes `t - m` with borrow
propagation into `SUBB = 0x1C00`, selects `SUBB` when `t ≥ m` and `TS`
otherwise without branching, `MCOPY`s `32 * n` bytes to `pd`, and jumps to
`ret`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume

/-! ## Pointer arithmetic

Every loop pointer walks downwards by one limb per iteration.  The EVM adds
the wrapped constant `2 ^ 256 - 32`, so the `j`-th pointer of a walk starting
at `base` is `UInt256.ofNat (ptrAt base j)`; `ptrAt` needs no side condition
because `UInt256.ofNat` already reduces modulo `2 ^ 256`. -/
def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

/-- One downward step, in the shape the `PUSH32 (2 ^ 256 - 32); ADD` pair
produces. -/
theorem ptrAt_succ (base j : Nat) :
    115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        ptrAt base j = ptrAt base (j + 1) := by
  simp only [ptrAt, Nat.succ_mul]
  omega

/-- The address a downward pointer walk has reached, as long as it has not
yet stepped below the base of the block. -/
theorem ptrAt_toNat (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    (UInt256.ofNat (ptrAt base j)).toNat = base - 32 * j := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, ptrAt]
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      Nat) = 2 ^ 256 - 32 := by norm_num
  have hmul : j * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = j * 2 ^ 256 - 32 * j := by
    rw [hlit, Nat.mul_sub, Nat.mul_comm j 32]
  rw [hmul]
  have hrewrite : base + (j * 2 ^ 256 - 32 * j) = (base - 32 * j) + j * 2 ^ 256 := by
    have : 32 * j ≤ j * 2 ^ 256 := by
      have := Nat.mul_le_mul_right j (show 32 ≤ 2 ^ 256 by norm_num)
      omega
    omega
  rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Basic blocks -/





/-! ## Memory progression of the `ADDMOD` limb loop -/

/-- The memory and the carry (resp. borrow) flag after some number of limb
steps of one of the two loops. -/
structure LimbState where
  memory : ByteArray
  flag : UInt256

/-- The state of memory and carry after `j` limb steps of `ADDMOD`, counted
from the least significant limb.  Step `j` reads limb `j` of the blocks at
`pa` and `pb` and writes limb `j` of the `t` block at `TS = 0x2040`. -/
def amStep (memory : ByteArray) (pa pb n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := amStep memory pa pb n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let y := MachineState.readWord prev.memory (pb + 32 * (n - 1 - j))
      let sum := x + y
      let total := prev.flag + sum
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded total.toNat 32) (2112 + 32 * (n - 1 - j))
        flag := UInt256.lor (UInt256.lt total prev.flag) (UInt256.lt sum x) }

/-! ## Active words

Every address this subroutine touches lies below `0x2500`, so once the setup
block has made `0x2500` bytes active no access here extends the high-water
mark. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2912) (hcurr : 91 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2912) (hact : 91 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ## States at the `ADDMOD` block boundaries -/

/-- Subroutine entry (pc 2137) with stack `[pa, pb, pd, ret]`. -/
def amEntryState (s : State) (memory : ByteArray) (pa pb : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pd, ret] ++ rest
           memory := memory }

/-- The `ADDMOD` loop head (pc 2168) after `j` limb steps. -/
def amLoopState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1970
           stack := [UInt256.ofNat (ptrAt (2080 + 32 * n) j),
                     UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) j),
                     (amStep memory pa pb n j).flag, pd, ret] ++ rest
           memory := (amStep memory pa pb n j).memory }


end Challenge.Modexp.Submission.Proofs.Fast.Csub
