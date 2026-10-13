import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Fast-entry inputs (64, 128 or 192 bytes). -/
def Aligned (input : ByteArray) : Prop := input.size % 64 = 0 ∧ input.size < 256

instance (input : ByteArray) : Decidable (Aligned input) := by
  unfold Aligned; infer_instance

/-- The block-exit continuation in slot 12.  Fast-entry inputs continue at the pad-test chain
4768 (the pad-only block then installs the output entry); every other input continues at the
last-block test 4757. -/
def contNat (input : ByteArray) : Nat :=
  if input.size % 64 = 0 ∧ input.size < 256 then 4768 else 4757

def cont (input : ByteArray) : UInt256 := UInt256.ofNat (contNat input)

def blockPC (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (if input.size = i * 64 ∧ input.size < 256 then 129 else 458)

theorem cont_aligned (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) :
    cont input = UInt256.ofNat 4768 := by
  simp only [cont, contNat, if_pos hz]

theorem cont_cold (input : ByteArray) (hz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    cont input = UInt256.ofNat 4757 := by
  simp only [cont, contNat, if_neg hz]

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
