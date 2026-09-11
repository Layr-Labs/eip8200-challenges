import Challenge.Modexp.Submission.Proofs.Fast.SquareInit

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareInit
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The exact 141 bytes of the submitted candidate's doubling initializer. -/
def initBlock : Block Artifact.submissionArtifact .Osaka 5045 initProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3823 95 5045 initProgram
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_init (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 91 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5045 rest)
      (stateAt s (initMemory mem) 5186 rest) :=
  initBlock.steps
    (EarlyCsub.environment (stateAt s mem 5045 rest) hcode hfork hrun hnp) rfl
    (run_init s mem rest hcap hact)

#print axioms gasSteps_init
end Challenge.Modexp.Submission.Proofs.Fast.SquareInit
