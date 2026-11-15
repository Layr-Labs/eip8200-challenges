import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.HotMaxMaskTrade
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "N" => UInt256.ofNat
def literal : List Instr := [.push 32 (N (2^256-1))]
def mask : List Instr := [.push 0 0,.op .NOT,.push 1 16,.op .SHR]
def state (s : State) (pc : Nat) (stack : List UInt256) : State := {s with pc:=N pc,stack:=stack}
theorem run_literal (s : State) (pc : Nat) (rest : List UInt256) (hc : rest.length<1024) :
 runInstructions literal (state s pc rest) =
 some (state s (pc+33) (Monpro.maxWord::rest)) := by
 simp [literal,state,runInstructions,Stepper.runInstr,hc,Word.literal_eq_ofNat,
 Word.succ_ofNat_mod,Word.ofNat_add_mod,Monpro.maxWord]
theorem run_mask (s : State) (pc : Nat) (rest : List UInt256) (hc : rest.length≤1021) :
 runInstructions mask (state s pc rest) =
 some (state s (pc+5) (N (2^240-1)::rest)) := by
 have h1 : rest.length<1024 := by omega
 have h2 : rest.length+1<1024 := by omega
 have h3 : rest.length+1+1<1024 := by omega
 have hn : UInt256.lnot (N 0) = Monpro.maxWord := by decide
 have hm : UInt256.shiftRight Monpro.maxWord (N 16) = N (2^240-1) := by decide
 simp (disch := omega) [mask,state,runInstructions,Stepper.runInstr,h1,h2,h3,hn,hm,Exp.push0_word,
 Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
end CycleSubmission.HotMaxMaskTrade
