import Challenge.Modexp.Submission.Proofs.Cycle.Return
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace OverlapFinalReturn
def program9 : List Instr := [.push 2 256,.push 1 16,.op .RETURN]
def result9 (s : State) (stack : List UInt256) : State :=
 {s with pc := UInt256.ofNat 8581,stack := stack,halt := .Returned,hReturn := MachineState.readPadded s.memory 16 256}
theorem run9 (s : State) (stack : List UInt256) (hcap : stack.length ≤ 1021) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions program9 {s with pc := UInt256.ofNat 8576,stack := stack} = some (result9 s stack) := by
 have h0 : stack.length < 1024 := by omega
 have h1 : stack.length+1 < 1024 := by omega
 have h2 : stack.length+1+1 < 1024 := by omega
 have hf := Monpro.activeWords_fix s 16 256 (by decide) (by norm_num) hact
 simp [program9,result9,runInstructions,runInstr,succ_ofNat_mod,ofNat_add_mod,literal_eq_ofNat,h0,h1,h2,
  State.activeWordsAfterUInt256,hf]
#print axioms run9
def program5 : List Instr := [.push 1 128,.push 1 24,.op .RETURN]
def result5 (s : State) (stack : List UInt256) : State :=
 {s with pc := UInt256.ofNat 10186,stack := stack,halt := .Returned,hReturn := MachineState.readPadded s.memory 24 128}
theorem run5 (s : State) (stack : List UInt256) (hcap : stack.length ≤ 1021) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions program5 {s with pc := UInt256.ofNat 10182,stack := stack} = some (result5 s stack) := by
 have h0 : stack.length < 1024 := by omega
 have h1 : stack.length+1 < 1024 := by omega
 have h2 : stack.length+1+1 < 1024 := by omega
 have hf := Monpro.activeWords_fix s 24 128 (by decide) (by norm_num) hact
 simp [program5,result5,runInstructions,runInstr,succ_ofNat_mod,ofNat_add_mod,literal_eq_ofNat,h0,h1,h2,
  State.activeWordsAfterUInt256,hf]
#print axioms run5
end OverlapFinalReturn
