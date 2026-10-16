import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Fast-entry inputs (64, 128 or 192 bytes). -/
def Aligned (input : ByteArray) : Prop := input.size % 64 = 0 ∧ input.size < 256

instance (input : ByteArray) : Decidable (Aligned input) := by
  unfold Aligned; infer_instance

/-- Block `i` is the pad-only block of a fast-entry input. -/
def Pad (input : ByteArray) (i : Nat) : Prop := input.size = i * 64 ∧ input.size < 256

instance (input : ByteArray) (i : Nat) : Decidable (Pad input i) := by
  unfold Pad; infer_instance

/-- The continuation in slot 12 while block `i` runs.  A fast-entry input carries the PC of its
next phase: `size - 64 i` for a message block (192 and 128 are stubs that step it down, 64 is the
pad-only block), and the pad-only block itself is entered with 64.  Every other input carries the
last-block test 48. -/
def contNat (input : ByteArray) (i : Nat) : Nat :=
  if input.size % 64 = 0 ∧ input.size < 256 then
    (if input.size = i * 64 then 64 else input.size - 64 * i)
  else 48

def cont (input : ByteArray) (i : Nat) : UInt256 := UInt256.ofNat (contNat input i)

/-- Message blocks enter the loop-head `JUMPDEST` at 461; the pad-only block's frame is complete at
74, after the target at 64 has run the previous block's tail copy. -/
def blockPC (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (if input.size = i * 64 ∧ input.size < 256 then 74 else 461)

/-- The shared lower-half path has its own JUMPDEST; its table body starts at 498.
It is not the ordinary loop-head entry, which must reverse both message halves. -/
def sharedTailPC : UInt256 := UInt256.ofNat 497

/-- The offset index in slot 11 while block `i` runs: the pad-only block keeps the last message
block's offset, since it is entered by the dispatch without an advance. -/
def offIndex (input : ByteArray) (i : Nat) : Nat :=
  if input.size = i * 64 ∧ input.size < 256 then i - 1 else i

theorem cont_cold (input : ByteArray) (hz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) (i : Nat) :
    cont input i = UInt256.ofNat 48 := by
  simp only [cont, contNat, if_neg hz]

theorem cont_aligned (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) (i : Nat)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) :
    cont input i = UInt256.ofNat (input.size - 64 * i) := by
  have hne : input.size ≠ i * 64 := fun h => hp ⟨h, hz.2⟩
  simp only [cont, contNat, if_pos hz, if_neg hne]

theorem cont_pad (input : ByteArray) (i : Nat) (hp : input.size = i * 64 ∧ input.size < 256) :
    cont input i = UInt256.ofNat 64 := by
  have hz : input.size % 64 = 0 ∧ input.size < 256 := ⟨by omega, hp.2⟩
  simp only [cont, contNat, if_pos hz, if_pos hp.1]

/-- The pad-only block is always the last block. -/
theorem pad_last (input : ByteArray) (i : Nat)
    (hh : input.size = i * 64 ∧ input.size < 256) : i + 1 = DriverTrace.blockCount input := by
  unfold DriverTrace.blockCount Padding.paddedLength
  omega

/-- On the fast entry the last block is the pad-only block. -/
theorem aligned_last (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) (i : Nat)
    (hi : i + 1 = DriverTrace.blockCount input) : input.size = i * 64 ∧ input.size < 256 := by
  unfold DriverTrace.blockCount Padding.paddedLength at hi
  omega

/-- No cold input ever reaches the pad-only block. -/
theorem cold_not_pad (input : ByteArray) (hz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) (i : Nat) :
    ¬ (input.size = i * 64 ∧ input.size < 256) := by
  intro h
  exact hz ⟨by omega, h.2⟩

/-- The continuation a fast-entry message block dispatches to is 192, 128 or 64; 64 exactly when
the next block is the pad-only block. -/
theorem aligned_cases (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) (i : Nat)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) (hi : i < DriverTrace.blockCount input) :
    (input.size - 64 * i = 192 ∧ ¬ (input.size = (i + 1) * 64 ∧ input.size < 256)) ∨
    (input.size - 64 * i = 128 ∧ ¬ (input.size = (i + 1) * 64 ∧ input.size < 256)) ∨
    (input.size - 64 * i = 64 ∧ (input.size = (i + 1) * 64 ∧ input.size < 256)) := by
  unfold DriverTrace.blockCount Padding.paddedLength at hi
  have hne : input.size ≠ i * 64 := fun h => hp ⟨h, hz.2⟩
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
