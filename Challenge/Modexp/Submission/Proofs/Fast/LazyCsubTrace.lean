import Challenge.Modexp.Submission.Proofs.Fast.LazyGateTrace
import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyCsub
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def gateBlock : Block Artifact.submissionArtifact .Osaka 4447 LazyGate.program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3526 5 4447 LazyGate.program
    (by decide) (by rfl) (by rfl) (by decide)

def copyBlock : Block Artifact.submissionArtifact .Osaka 4456 LazyGate.copyProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3531 7 4456 LazyGate.copyProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestGate : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4447 = true :=
  Artifact.isValidJumpDest_index 3526 (by rfl)

theorem jumpDestCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4456 = true :=
  Artifact.isValidJumpDest_index 3531 (by rfl)

def gasSteps_csub_lazy (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord memory 2752 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord memory 2784 = UInt256.ofNat (2080+32*n))
    (hs32 : MachineState.readWord (Csub.csStep memory n n).memory 2688 = UInt256.ofNat (32*n))
    (hdstFit : pdst.toNat+32*n ≤ 2816)
    (htn : (MachineState.readWord (Csub.csStep memory n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (LazyGate.atState s memory 4447 pdst ret rest)
      (LazyGate.returnedState s (resultMemory memory n pdst.toNat) ret rest) := by
  have env : Environment Artifact.submissionArtifact .Osaka s :=
    ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
        rw [Challenge.Modexp.submissionBytecode_size]; decide,
      hcode,hfork,hrun,hnp⟩
  have hs : MachineState.readWord memory 2688 = UInt256.ofNat (32*n) := by
    rw [Csub.csStep_readWord_disjoint memory n 2688 (by omega) (by omega) n le_rfl] at hs32
    exact hs32
  have subTrace := Csub.gasSteps_csub_sub s memory n pdst ret rest hcap hcode hfork hrun hnp
    hact hn hn32 hjump hml htl hs32 hdstFit htn hfast
  exact LazyGate.gasSteps_lazy gateBlock copyBlock s memory n pdst ret rest env
    hcap hact hn hn32 hs hdstFit (by simpa only [hcode] using hjump)
    (by simpa only [hcode] using jumpDestSub) subTrace

#print axioms gasSteps_csub_lazy
end Challenge.Modexp.Submission.Proofs.Fast.LazyCsub
