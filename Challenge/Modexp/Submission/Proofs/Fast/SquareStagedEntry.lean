import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached

/-- Rebase the square's B pointer onto the already staged operand. -/
def program : List Instr :=
  [.op .JUMPDEST, .push 2 4436, .op (.Swap ⟨1, by decide⟩), .op .POP,
   .push 2 2336, .op (.Swap ⟨2, by decide⟩), .op .POP,
   .push 2 1856, .op .ADD]

def block : Block Artifact.submissionArtifact .Osaka 4770 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3590 9 4770 program
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 4770).toNat = true :=
  Artifact.isValidJumpDest_index 3590 (by rfl)

theorem run_entry (s : State) (mem : ByteArray) (n : Nat)
    (ent inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1012)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions program
      (outState s mem 512 n 0 (UInt256.ofNat 4770) ent inv m0 rest) =
    some { outState s mem 2368 n 0 (UInt256.ofNat 4436) ent inv m0 rest with
      pc := UInt256.ofNat 4785 } := by
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have hp : UInt256.ofNat 1856 + UInt256.ofNat (512 + 32 * n - 32) =
      UInt256.ofNat (2368 + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  simp [program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    outState, ptrAt_zero, hp, h9, h10, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (mem : ByteArray) (n : Nat)
    (ent inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1012)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outState s mem 512 n 0 (UInt256.ofNat 4770) ent inv m0 rest)
      { outState s mem 2368 n 0 (UInt256.ofNat 4436) ent inv m0 rest with
        pc := UInt256.ofNat 4785 } :=
  block.steps (SquareRow.environment _ hcode hfork hrun hnp) rfl
    (run_entry s mem n ent inv m0 rest hcap hcode)

end Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry
