import Challenge.Modexp.Submission.Proofs.Fast.TnCacheR8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8RowZero
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel

def block : Block TnCandidateArtifact.submissionArtifact .Osaka 4441 TnCacheR8RowZero.program :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3360 28 4441 TnCacheR8RowZero.program
    (by decide) (by rfl) (by rfl) (by decide)

noncomputable def prologue_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (tn : UInt256)
    (inv m0 tl m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord mem 2336 = UInt256.ofNat 0)
    (hj : Decode.isValidJumpDest TnCandidate.bytecode 3740 = true) :
    GasSteps
      { TnCandidateSquareSteps.outState tn s mem 2368 8 0 (UInt256.ofNat 4471) (UInt256.ofNat 3740)
          inv m0 (tl :: m96 :: m64 :: m32 :: aprev :: rest) with pc := UInt256.ofNat 4441 }
      (TnCandidateSquareSteps.l1Q tn 3740 s (sqPro mem 8 0 (UInt256.ofNat 0))
        (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 8 0
        (UInt256.ofNat 4471) (UInt256.ofNat 3777) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: rest)) := by
  have hr := TnCacheR8RowZero.run_rowZero s mem tn (UInt256.ofNat 4441) 3740
    inv m0 tl m96 m64 m32 aprev rest hcap hact hzero
    (by rw [env.code]; exact hj) (by decide) (by decide)
  exact TnCandidateSquareSteps.stepsOf block hr rfl env.code env.forkEq env.running env.noPrecompile

#print axioms prologue_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8RowZero
