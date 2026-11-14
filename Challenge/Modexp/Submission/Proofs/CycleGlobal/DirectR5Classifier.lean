import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.DirectR5Classifier
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
def program : List Instr :=
 [
  .op .JUMPDEST,
   .op (.Dup ⟨1,by decide⟩),
   .push 1 128,
   .op .XOR,
   .push 2 3288,
   .op .JUMPI]
theorem run4 (s : State) (count : Nat) (hpos : 1 ≤ count) (hle : count ≤ 16) (rest : List UInt256) (hcap : rest.length ≤ 1000) :
 runInstructions program {s with pc := UInt256.ofNat 8636,stack := [UInt256.ofNat (count-1),UInt256.ofNat 128]++rest} =
 some {s with pc := UInt256.ofNat 8645,stack := [UInt256.ofNat (count-1),UInt256.ofNat 128]++rest} := by
 have hc2 : rest.length+2 < 1024 := by omega
 have hc3 : rest.length+3 < 1024 := by omega
 have hc4 : rest.length+4 < 1024 := by omega
 have hx : UInt256.xor (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 := by decide
 simp [program,runInstructions,Stepper.runInstr,hc2,hc3,hc4,Nat.add_assoc,Challenge.Modexp.Submission.Proofs.Fast.Exp.push0_word,hx,UInt256.isTrue,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem run8 (s : State) (count : Nat) (hpos : 1 ≤ count) (hle : count ≤ 16) (rest : List UInt256) (hcap : rest.length ≤ 1000)
 (hd : Decode.isValidJumpDest s.executionEnv.code 3288 = true) :
 runInstructions program {s with pc := UInt256.ofNat 8636,stack := [UInt256.ofNat (count-1),UInt256.ofNat 256]++rest} =
 some {s with pc := UInt256.ofNat 3288,stack := [UInt256.ofNat (count-1),UInt256.ofNat 256]++rest} := by
 have hc2 : rest.length+2 < 1024 := by omega
 have hc3 : rest.length+3 < 1024 := by omega
 have hc4 : rest.length+4 < 1024 := by omega
 have hx : UInt256.xor (UInt256.ofNat 128) (UInt256.ofNat 256) = UInt256.ofNat 384 := by decide
 simp [program,runInstructions,Stepper.runInstr,hc2,hc3,hc4,Nat.add_assoc,Challenge.Modexp.Submission.Proofs.Fast.Exp.push0_word,hx,hd,UInt256.isTrue,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
#print axioms run4
#print axioms run8
end CycleSubmission.Global.DirectR5Classifier
