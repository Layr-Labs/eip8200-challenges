import Challenge.Modexp.Submission.Proofs.Fast.SquareInit

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareInit
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The exact 141 bytes of the submitted candidate's doubling initializer. -/
def initBlock : Block Artifact.submissionArtifact .Osaka 5052 initProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3833 94 5052 initProgram
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_init (s : State) (mem : ByteArray)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 aEnd : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1004)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcache : MachineState.readWord mem 9184 = aEnd)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (stateAt s mem 5052
        ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, aEnd] ++ rest))
      (stateAt s (initMemory mem) 5190
        ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, aEnd] ++ rest)) :=
  initBlock.steps
    (EarlyCsub.environment
      (stateAt s mem 5052
        ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, aEnd] ++ rest))
      hcode hfork hrun hnp) rfl
    (run_init s mem x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 aEnd
      rest hcap hact hcache)

#print axioms gasSteps_init
end Challenge.Modexp.Submission.Proofs.Fast.SquareInit
