import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding

def program : List Instr := [.op .JUMPDEST, .op .POP]
def block : Block Artifact.submissionArtifact .Osaka 1150 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 777 2 1150 program
    (by decide) (by rfl) (by rfl) (by decide)

theorem run (s : State) (mem : ByteArray) (count : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) :
    runInstructions program (Exp.retTo s mem (UInt256.ofNat 1150) (count::rest)) =
      some (Exp.retTo s mem (UInt256.ofNat 1152) rest) := by
  have hlen : rest.length+1 < 1024 := by omega
  simp [program, runInstructions, Challenge.EvmProof.Stepper.runInstr, Exp.retTo, hlen,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat]

def gasSteps (s : State) (mem : ByteArray) (count : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Exp.retTo s mem (UInt256.ofNat 1150) (count::rest))
      (Exp.retTo s mem (UInt256.ofNat 1152) rest) :=
  block.steps ⟨by change submissionBytecode.size < 2^256; rw [submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩ rfl (run s mem count rest hcap)

end Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
