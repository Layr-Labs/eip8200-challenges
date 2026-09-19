import Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding

def program : List Instr := GenericReturnAdapter.terminalReturnProgram
def block : Block TnM128CandidateArtifact.submissionArtifact .Osaka
    GenericReturnAdapter.terminalReturnPC program :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 4410 5
    GenericReturnAdapter.terminalReturnPC program
    (by decide) (by rfl) (by rfl) (by decide)

theorem run (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1021) :
    runInstructions program (GenericReturnAdapter.terminalInput s mem rest) =
      some (GenericReturnAdapter.terminalOutput s mem rest) := by
  simpa [program] using GenericReturnAdapter.run_terminalReturn s mem rest hcap

def gasSteps (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1021)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (GenericReturnAdapter.terminalInput s mem rest)
      (GenericReturnAdapter.terminalOutput s mem rest) :=
  block.steps ⟨by
      change TnM128Candidate.bytecode.size < 2^256
      rw [TnM128Candidate.bytecode_size]
      decide,
    hcode, hfork, hrun, hnp⟩ rfl (run s mem rest hcap)

end Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
