import Challenge.Modexp.Submission.Proofs.Fast.LazyGateRun
import Challenge.Modexp.Submission.Proofs.Fast.LazyCsubMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyGate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-! This composition uses actual exact-location Block certificates and the
    existing subtraction trace as explicit premises. The e570 binding module
    supplies these once the shared artifact's mechanical proof passes. -/
def gasSteps_lazy {artifact : Challenge.EvmProof.ProgramArtifact}
    (gateBlock : Block artifact .Osaka 4447 program)
    (copyBlock : Block artifact .Osaka 4456 copyProgram)
    (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256)
    (rest : List UInt256)
    (env : Environment artifact .Osaka s)
    (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hdstFit : dst.toNat+32*n ≤ 2816)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hsubJump : Decode.isValidJumpDest s.executionEnv.code 4244 = true)
    (subTrace : Challenge.EvmProof.GasSteps (atState s mem 4244 dst ret rest)
      (returnedState s (Csub.subResultMemory mem n dst.toNat) ret rest)) :
    Challenge.EvmProof.GasSteps (atState s mem 4447 dst ret rest)
      (returnedState s (LazyCsub.resultMemory mem n dst.toNat) ret rest) := by
  have hc := gateBlock.steps (env.transfer (t := atState s mem 4447 dst ret rest) rfl rfl) rfl
    (run_gate s mem dst ret rest hcap hact hsubJump)
  by_cases hz : (MachineState.readWord mem 2080).toNat = 0
  · rw [if_pos hz] at hc
    have hk := copyBlock.steps (env.transfer (t := atState s mem 4456 dst ret rest) rfl rfl) rfl
      (run_copy s mem n dst ret rest hcap hact hn hn32 hs32 hdstFit hjump)
    simpa only [LazyCsub.resultMemory,if_pos hz] using hc.trans hk
  · rw [if_neg hz] at hc
    simpa only [LazyCsub.resultMemory,if_neg hz] using hc.trans subTrace

#print axioms gasSteps_lazy
end Challenge.Modexp.Submission.Proofs.Fast.LazyGate
