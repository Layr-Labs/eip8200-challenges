import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace CycleSubmission.Global.Fast.FusedFinish
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding

def program : List Instr := [.op .JUMPDEST, .op .POP]
def block : Block CycleSubmission.Artifact.artifact .Osaka 690 program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 486 2 690 program
    (by decide) (by rfl) (by rfl) (by decide)

theorem run (s : State) (mem : ByteArray) (count : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) :
    runInstructions program (Exp.retTo s mem (UInt256.ofNat 690) (count::rest)) =
      some (Exp.retTo s mem (UInt256.ofNat 692) rest) := by
  have hlen : rest.length+1 < 1024 := by omega
  simp [program, runInstructions, Challenge.EvmProof.Stepper.runInstr, Exp.retTo, hlen,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat]

def gasSteps (s : State) (mem : ByteArray) (count : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Exp.retTo s mem (UInt256.ofNat 690) (count::rest))
      (Exp.retTo s mem (UInt256.ofNat 692) rest) :=
  block.steps ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide,
    hcode, hfork, hrun, hnp⟩ rfl (run s mem count rest hcap)

end CycleSubmission.Global.Fast.FusedFinish
