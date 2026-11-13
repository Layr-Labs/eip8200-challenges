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

/-- Retain limb5 and save the displaced mask once. The inverse remains at2720. -/
def installPrefix : List Instr :=
 [.push 1 96,.op .MLOAD,.op (.Swap ⟨10,by decide⟩),.push 2 1664,.op .MSTORE]

theorem run_installPrefix (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (h96 : MachineState.readWord s.memory 96 = a 5) :
 runInstructions installPrefix
  {s with pc := UInt256.ofNat 5387,stack := SquareMeaning.frame0 inv a b n (count::inv::rest)} =
 some {s with pc := UInt256.ofNat 5395,memory := LimbMemory.store s.memory 1664 LimbMemory.mask,stack := (SquareMeaning.frame0 inv a b n (count::inv::rest)).set 10 (a 5)} := by
 have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have hf1664 := Monpro.activeWords_fix s 1664 32 (by decide) (by norm_num) hact
 have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
 simp [installPrefix,SquareMeaning.frame0,List.set,LimbMemory.store,LimbMemory.mask,
  runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf96,hf1664,h96,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,capacity,Nat.add_assoc]

def persistentProgram : List Instr := [.op .JUMPDEST] ++ R9InvConsumeComplete.program
def persistentInitial (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 5395,stack := (SquareMeaning.frame0 inv a b n (count::inv::rest)).set 10 (a 5)}

theorem run_persistent (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : LimbMemory.Holds s.memory inv a b n) (ha : ∀ i < 8, (a i).toNat < 2^240) :
 runInstructions persistentProgram (persistentInitial s inv count a b n rest) =
 some {s with pc := UInt256.ofNat 7659,memory := R9InvConsumeComplete.historyMemory s.memory inv a b n,stack := R9InvConsumeComplete.persistentFrame15 inv a b n (count::inv::rest)} := by
 have hc : (count::inv::rest).length ≤ 960 := by simp; omega
 have hh := R9InvConsumeComplete.run s inv a b n (count::inv::rest) hc hact hmem ha
 have hlen : (SquareMeaning.frame0 inv a b n (count::inv::rest)).length < 1024 := by
  simp [SquareMeaning.frame0]
  omega
 have hp : runInstructions [.op .JUMPDEST] (persistentInitial s inv count a b n rest) =
  some {s with pc := UInt256.ofNat 5396,stack := (SquareMeaning.frame0 inv a b n (count::inv::rest)).set 10 (a 5)} := by
  simp [persistentInitial,runInstructions,Stepper.runInstr,Word.succ_ofNat_mod,hlen]
 exact runInstructions_append_some _ _ _ _ _ hp hh

def restoreMaskProgram : List Instr :=
 [.op (.Dup ⟨10,by decide⟩),.push 1 96,.op .MSTORE,
  .push 2 1664,.op .MLOAD,.op (.Swap ⟨10,by decide⟩),.op .POP]

theorem run_restoreMask (s : State) (inv : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
 (hmask : MachineState.readWord s.memory 1664 = LimbMemory.mask) :
 runInstructions restoreMaskProgram
  {s with pc := UInt256.ofNat 7668,stack := (SquareMeaning.frame0 inv a b n rest).set 10 (a 5)} =
 some {s with pc := UInt256.ofNat 7678,memory := LimbMemory.store s.memory 96 (a 5),stack := SquareMeaning.frame0 inv a b n rest} := by
 have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
 have hf := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have hf1664 := Monpro.activeWords_fix s 1664 32 (by decide) (by norm_num) hact
 have hm : MachineState.readWord (LimbMemory.store s.memory 96 (a 5)) 1664 = LimbMemory.mask := by
  simpa (disch := decide) only [LimbMemory.store,CycleSubmission.Prepared.Arithmetic.read_disjoint] using hmask
 have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
 simp [hz,restoreMaskProgram,LimbMemory.mask,hm,SquareMeaning.frame0,List.set,LimbMemory.store,CycleSubmission.Prepared.Arithmetic.read_disjoint,hmask,
  runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf,hf1664,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,capacity,Nat.add_assoc]

#print axioms run_installPrefix
#print axioms run_persistent
#print axioms run_restoreMask
end CycleSubmission.CachedInverse
