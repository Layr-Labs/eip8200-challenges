import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P16
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P18
import Challenge.Modexp.Submission.Proofs.Fast.Setup
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `LZ` head of the exponent-byte loop

`LZ` occupies instruction indices 1908..1942 (pc 2695..3189).  It is entered
at pc 2695 with the byte index `i` on top of the driver frame, loads exponent
byte `i` exactly as the code it replaces did, and then chooses the mask the
inner bit loop starts from:

* for `i ≠ 0` it is `0x80`, as before;
* for `i = 0` it is the highest set bit of the byte, so the bit loop starts at
  the exponent's leading one instead of at bit 7.

Both arms rejoin the bit loop at pc 1916.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Lz

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## Memory-expansion bookkeeping

`Fast.Exp` carries the same two lemmas, but it imports this module, so they are
restated here for the `V_EOFF` load. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2848) (hcurr : 89 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  exact Nat.max_eq_left (by omega)

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2848) (hact : 89 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ## The mask -/

/-- The three smear steps, in the operand order the `OR`s produce them:
`OR` pops the shifted copy first. -/
def sm1 (w : Nat) : Nat := (w >>> 1) ||| w
def sm2 (w : Nat) : Nat := (sm1 w >>> 2) ||| sm1 w
def sm3 (w : Nat) : Nat := (sm2 w >>> 4) ||| sm2 w

/-- The smear halved and incremented: the highest set bit of a byte, and `1`
for a zero byte. -/
def topBit (w : Nat) : Nat := (sm3 w >>> 1) + 1

/-- Its exponent. -/
def topExp (w : Nat) : Nat :=
  if 128 ≤ w then 7 else if 64 ≤ w then 6 else if 32 ≤ w then 5 else
  if 16 ≤ w then 4 else if 8 ≤ w then 3 else if 4 ≤ w then 2 else
  if 2 ≤ w then 1 else 0

/-- **The mask is a power of two that dominates the byte.**  Everything the
skipped iterations of the bit loop would have tested is zero. -/
theorem topBit_spec (w : Nat) (hw : w < 256) :
    topBit w = 2 ^ topExp w ∧ topExp w ≤ 7 ∧ w < 2 ^ (topExp w + 1) := by
  interval_cases w <;> exact ⟨by decide, by decide, by decide⟩

/-- A nonzero byte has its `topExp` bit set. -/
theorem topExp_le (w : Nat) (hw : w < 256) (hne : w ≠ 0) : 2 ^ topExp w ≤ w := by
  interval_cases w
  · exact absurd rfl hne
  all_goals decide

/-! ## States at the block boundaries -/

/-- The `LZ` entry, pc 2695.  The driver frame below the byte index is left
abstract so that this module does not depend on `Fast.Exp`. -/
def lzEntry (s : State) (mem : ByteArray) (i : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1299
           stack := UInt256.ofNat i :: rest
           memory := mem }

/-- pc 2711, the arm every byte after the first takes. -/
def lzOther (s : State) (mem : ByteArray) (i w : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1315
           stack := UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-- pc 2720, the arm byte `0` takes. -/
def lzFirst (s : State) (mem : ByteArray) (i w : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1321
           stack := UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-- The bit-loop head both arms rejoin, pc 1916. -/
def lzJoin (s : State) (mem : ByteArray) (i w mask : Nat)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 962
           stack := UInt256.ofNat mask :: UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-- The state handed to the relocated leading-bit shortcut at pc3865. -/
def lzBase (s : State) (mem : ByteArray) (i w mask : Nat)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2160
           stack := UInt256.ofNat mask :: UInt256.ofNat w :: UInt256.ofNat i :: rest
           memory := mem }

/-! ## Traces

The byte the block loads is left abstract, as `hbyte`, so that this module
does not need `Fast.Exp`'s `expByte`. -/

theorem shr_ofNat' (v k : Nat) (hv : v < 2 ^ 256) (hk : k < 256) :
    UInt256.shiftRight (UInt256.ofNat v) (UInt256.ofNat k) =
      UInt256.ofNat (v >>> k) := by
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hv hk]

theorem lor_ofNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.lor (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a ||| b) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem sm_lt (w : Nat) (hw : w < 256) :
    sm1 w < 256 ∧ sm2 w < 256 ∧ sm3 w < 256 := by
  interval_cases w <;> exact ⟨by decide, by decide, by decide⟩

/-! ## The two rejoining arms -/

