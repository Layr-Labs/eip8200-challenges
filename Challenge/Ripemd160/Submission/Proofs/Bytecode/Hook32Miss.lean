import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32

set_option warningAsError true
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Miss

open Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

theorem gas_at {pc pc' : Nat} (s : State) (instruction : Instr) (i : Nat)
    (stk stk' : List UInt256)
    (hget : submissionInstructions[i]? = some instruction)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (hpc : submissionArtifact.instructionPC i = pc)
    (hres : runInstr instruction (atState s pc stk) = some (atState s pc' stk')) :
    GasSteps (atState s pc stk) (atState s pc' stk') := by
  apply sound_step (atState s pc stk) (atState s pc' stk') ⟨i, instruction, hget, by decide⟩
  · simp [atState, hcode]
  · simp [atState, hpc, Word.word_toNat_ofNat]
  · simp [atState, hrun]
  · exact hres

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Miss
