import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Complete
import Challenge.Modexp.Submission.Proofs.Cycle.LimbMemory
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace CycleSubmission.CachedInverse
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
def publicCounter (s : State) : UInt256 := s.stack.getD 14 (UInt256.ofNat 0)
def installPrefix : List Instr :=
 [
  .push 1 96,
   .op .MLOAD,
   .op (.Swap ⟨10,by decide⟩),
   .op (.Swap ⟨13,by decide⟩),
   .op (.Swap ⟨14,by decide⟩),
   .op (.Swap ⟨15,by decide⟩),
   .op .POP]
theorem run_installPrefix (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (h96 : MachineState.readWord s.memory 96 = a 5) :
 runInstructions installPrefix
 {s with pc := UInt256.ofNat 3484,stack := SquareMeaning.frame0 inv a b n (count::inv::rest)} =
 some {s with pc := UInt256.ofNat 3492,stack := R9InvConsumeComplete.initialFrame inv a b n (count::rest)} := by
 have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
 have hf := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
 simp [hz,installPrefix,R9InvConsumeComplete.initialFrame,SquareMeaning.frame0,List.set,
  runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf,h96,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,capacity,Nat.add_assoc]
def persistentProgram : List Instr := [.op .JUMPDEST]++R9InvConsumeComplete.program
def persistentInitial (s : State) (inv count : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 3492,stack := R9InvConsumeComplete.initialFrame inv a b n (count::rest)}
theorem run_persistent (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : LimbMemory.Holds s.memory inv a b n) (ha : ∀ i < 8,(a i).toNat < 2^240) :
 runInstructions persistentProgram (persistentInitial s inv count a b n rest) =
 some {s with pc := UInt256.ofNat 5570,memory := R9InvConsumeComplete.historyMemory s.memory inv a b n,stack := R9InvConsumeComplete.persistentFrame15 inv a b n (count::rest)} := by
 have hc : (count::rest).length ≤ 960 := by simp; omega
 have hh := R9InvConsumeComplete.run s inv a b n (count::rest) hc hact hmem ha
 have hlen : (R9InvConsumeComplete.initialFrame inv a b n (count::rest)).length < 1024 := by
  simp [R9InvConsumeComplete.initialFrame,SquareMeaning.frame0,List.set]
  omega
 have hp : runInstructions [.op .JUMPDEST] (persistentInitial s inv count a b n rest) =
  some {s with pc := UInt256.ofNat 3493,stack := R9InvConsumeComplete.initialFrame inv a b n (count::rest)} := by
  simp [persistentInitial,runInstructions,Stepper.runInstr,Word.succ_ofNat_mod,hlen]
 exact runInstructions_append_some _ _ _ _ _ hp hh
def restoreMaskProgram : List Instr :=
 [
  .push 2 2720,
   .op .MLOAD,
   .op (.Swap ⟨15,by decide⟩),
   .op (.Swap ⟨14,by decide⟩),
   .op (.Swap ⟨13,by decide⟩),
   .op (.Swap ⟨10,by decide⟩),
   .push 3 96,
   .op .MSTORE]
theorem run_restoreMask (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (hinv : MachineState.readWord s.memory 2720 = inv) :
 runInstructions restoreMaskProgram
 {s with pc := UInt256.ofNat 5610,stack := R9InvConsumeComplete.initialFrame inv a b n (count::rest)} =
 some {s with pc := UInt256.ofNat 5623,memory := LimbMemory.store s.memory 96 (a 5),stack := SquareMeaning.frame0 inv a b n (count::inv::rest)} := by
 have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
 have hf := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have hfi := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
 have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
 simp [hz,restoreMaskProgram,R9InvConsumeComplete.initialFrame,SquareMeaning.frame0,List.set,LimbMemory.store,
  runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf,hfi,
  CycleSubmission.Prepared.Arithmetic.read_disjoint,hinv,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,capacity,Nat.add_assoc]
#print axioms run_installPrefix
#print axioms run_persistent
#print axioms run_restoreMask
end CycleSubmission.CachedInverse
