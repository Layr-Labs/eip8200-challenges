import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMemoryOperands
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOperandFold
open EvmSemantics PackedStepCorrected PackedCompression

/-- A prefix only observes operands below its length. -/
theorem rounds_congr (X Y K L : Nat → UInt256) (n : Nat)
    (hx : ∀ i, i < n → X i = Y i)
    (hk : ∀ i, i < n → K i = L i) (g : Regs) :
    packedRounds X K n g = packedRounds Y L n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => hx i (by omega)) (fun i hi => hk i (by omega))
    simp only [packedRounds, packedStep, hp, hx n (by omega), hk n (by omega)]

def machineWords (memory : ByteArray) (i : Nat) : UInt256 :=
  PackedMemoryOperands.reader memory (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
    PackedMemoryOperands.reader memory (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8))

theorem machine_fold (memory : ByteArray) (words : Nat → UInt256)
    (n : Nat) (hn : n ≤ 80) (g : Regs) :
    packedRounds (machineWords (PackedGapInvariant.spreadWords words 16 memory))
      (fun i => PackedEmit.packedK (i / 16)) n g =
    packedRounds (PackedSpreadSchedule.messageWords memory words)
      (fun i => PackedSpreadSchedule.groupConstant (i / 16)) n g := by
  apply rounds_congr
  · intro i hi
    exact PackedMemoryOperands.spread_reader memory words i (by omega)
  · intro i _
    rfl

#print axioms rounds_congr
#print axioms machine_fold
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOperandFold
