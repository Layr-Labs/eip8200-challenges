import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Pure `ADDMOD`/`CSUB` models and shared state definitions

Artifact-independent core factored out of `Fast.Csub` so the affine
one-pointer modules (`CsubAffineStep`, `CsubAffineRun`,
`CsubAffineLocations`) can build on the exact same pure model without
importing the concrete three-pointer execution proofs: the import graph is
`CsubModel ← CsubAffineStep ← CsubAffineRun`, `CsubModel ← Csub`, and
(later) `Csub ← CsubAffineLocations`, which is acyclic.

Everything here keeps its `Csub`-qualified name, so callers are unaffected.
`ADDMOD`/`CSUB` concrete traces, invariants, functional correctness, and
the `gasSteps_csub` assembly stay in `Fast.Csub`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

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
          (Data.Bytes.natToBytesPadded total.toNat 32) (8256 + 32 * (n - 1 - j))
        flag := UInt256.lor (UInt256.lt total prev.flag) (UInt256.lt sum x) }

/-! ## Active words

Every address this subroutine touches lies below `0x2500`, so once the setup
block has made `0x2500` bytes active no access here extends the high-water
mark. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-- Entry of `CSUB` (pc 2304) with stack `[pd, ret]`. -/
def csEntryState (s : State) (memory : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2304
           stack := [pdst, ret] ++ rest
           memory := memory }

/-- The state of memory and borrow after `j` limb steps of `CSUB`, counted from
the least significant limb.  Step `j` reads limb `j` of `t_low` at `TS` and of
the modulus at `0`, and writes limb `j` of the candidate at `SUBB`. -/
def csStep (memory : ByteArray) (n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := csStep memory n j
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let d1 := t - md
      let d2 := d1 - prev.flag
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (n - 1 - j))
        flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) }

/-- `use = t[n] ∨ ¬borrow`: nonzero exactly when `t ≥ m`. -/
def csUse (memory : ByteArray) (n j : Nat) : UInt256 :=
  UInt256.lor (MachineState.readWord (csStep memory n j).memory 8224)
    (UInt256.isZero (csStep memory n j).flag)

/-- The `MCOPY` source: `TS` when `use = 0`, `SUBB` when `use = 1`. -/
def csSrc (memory : ByteArray) (n j : Nat) : UInt256 :=
  (8256 : UInt256) +
    (115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) *
      csUse memory n j

/-- Back at the caller (pc `ret`) with the result block copied to `pd`. -/
def csReturnedState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := MachineState.writeBytes (csStep memory n j).memory
             (MachineState.readPadded (csStep memory n j).memory
               (csSrc memory n j).toNat (32 * n)) pdst.toNat }

theorem or_of_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b = max a b := by
  interval_cases a <;> interval_cases b <;> decide

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem csUse_le_one (memory : ByteArray) (n j : Nat)
    (htn : (MachineState.readWord (csStep memory n j).memory 8224).toNat ≤ 1) :
    (csUse memory n j).toNat ≤ 1 := by
  rw [csUse, Challenge.EvmProof.Word.word_toNat_lor]
  have hz : (UInt256.isZero (csStep memory n j).flag).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [or_of_le_one htn hz]
  omega

theorem csUse_toNat (memory : ByteArray) (n j : Nat)
    (htn : (MachineState.readWord (csStep memory n j).memory 8224).toNat ≤ 1) :
    (csUse memory n j).toNat =
      max (MachineState.readWord (csStep memory n j).memory 8224).toNat
        (if (csStep memory n j).flag.toNat = 0 then 1 else 0) := by
  have hz : (UInt256.isZero (csStep memory n j).flag).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [csUse, Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one htn hz,
    Challenge.EvmProof.Word.word_toNat_isZero]

theorem csSrc_toNat (memory : ByteArray) (n j : Nat)
    (huse : (csUse memory n j).toNat ≤ 1) :
    (csSrc memory n j).toNat =
      if (csUse memory n j).toNat = 0 then 8256 else 7168 := by
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hL : (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
    decide
  rw [csSrc, Challenge.EvmProof.Word.word_toNat_add, word_toNat_mul, h8256, hL]
  rcases Nat.lt_or_ge (csUse memory n j).toNat 1 with h | h
  · rw [show (csUse memory n j).toNat = 0 from by omega, if_pos rfl]
    norm_num
  · rw [show (csUse memory n j).toNat = 1 from by omega, if_neg (by norm_num)]
    norm_num

end Challenge.Modexp.Submission.Proofs.Fast.Csub
