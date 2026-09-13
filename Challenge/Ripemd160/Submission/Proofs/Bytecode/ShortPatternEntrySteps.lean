import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem stepS_iszero (input : ByteArray) (pc : Nat) (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Stepper.runInstr (.op .ISZERO) (stS input pc (a :: rest)) =
      some (stS input (pc + 1) (UInt256.isZero a :: rest)) := by
  unfold Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Word.succ_ofNat hpc]
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
