import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosAccumulatorMemory CiosCarryMemory CiosReadonly

def middleStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 8224, .op .MLOAD, .op .ADD,
   .op (.Swap ⟨6, by decide⟩), .op .POP, .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP]

def tailStore : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .POP, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 8256, .op .MSTORE, .op .LT, .op .ADD, .push 2 8224, .op .MSTORE]

def testProgram : List Instr :=
  [.push 32 negative32, .op .ADD, .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .push 2 4252, .op .JUMPI]

def tailLoopProgram : List Instr := tailStore ++ testProgram

theorem run_middleStore (s : State) (c bi pbi pa pb flag slot : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions middleStore
      (framed s (UInt256.ofNat 4537) ([c,bi,pbi,pa,pb,flag,slot] ++ rest)) =
    some (framed s (UInt256.ofNat 4549)
      ([midCarry s.memory c,pbi,pa,pb,flag,MachineState.readWord s.memory 8224+c] ++ rest)) := by
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have ha : (8224 : UInt256).toNat = 8224 := by decide
  have hA := activeWords_fix s 8224 32 (by decide) (by omega) hact
  simp [middleStore,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,
    hc6,hc7,hc8,hc9,hc10,Nat.add_assoc,List.exchange,midCarry,
    ha,hA,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tailStore (s : State) (c mu bit pbi pa pb flag t : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions tailStore
      (framed s (UInt256.ofNat 4828) ([c,mu,bit,pbi,pa,pb,flag,t] ++ rest)) =
    some (framed {s with memory := tailWithTN s.memory c bit t} (UInt256.ofNat 4844)
      ([pbi,pa,pb,flag,t] ++ rest)) := by
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have ha : (8224 : UInt256).toNat = 8224 := by decide
  have hb : (8256 : UInt256).toNat = 8256 := by decide
  have hA := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hB := activeWords_fix s 8256 32 (by decide) (by omega) hact
  simp [tailStore,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,
    hc5,hc6,hc7,hc8,hc9,hc10,Nat.add_assoc,List.exchange,tailWithTN,writeWord,
    ha,hb,hA,hB,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  simp only [Nat.add_comm]

theorem run_test (s : State) (pbi pa pb flag bit : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4252 = true) :
    runInstructions testProgram
      (framed s (UInt256.ofNat 4844) ([pbi,pa,pb,flag,bit] ++ rest)) =
    some (framed s
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then UInt256.ofNat 4252
        else UInt256.ofNat 4885)
      ([negative32+pbi,pa,pb,flag,bit] ++ rest)) := by
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt (negative32+pbi) pb) <;>
    simp [testProgram,framed,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      hc5,hc6,hc7,hc8,Nat.add_assoc,ht,htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]


theorem run_tail (s : State) (c mu bit pbi pa pb flag t : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) (hact : 296 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4252 = true) :
    runInstructions tailLoopProgram
      (framed s (UInt256.ofNat 4828) ([c,mu,bit,pbi,pa,pb,flag,t] ++ rest)) =
    some (framed {s with memory := tailWithTN s.memory c bit t}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then UInt256.ofNat 4252
        else UInt256.ofNat 4885)
      ([negative32+pbi,pa,pb,flag,t] ++ rest)) :=
  runInstructions_append_some _ _ _ _ _
    (run_tailStore s c mu bit pbi pa pb flag t rest hcap hact)
    (run_test {s with memory := tailWithTN s.memory c bit t} pbi pa pb flag t rest hcap htarget)

theorem run_exit (s : State) (pbi paEnd pbEnd flag slot target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4993 = true) :
    runInstructions fullExitProgram
      (framed s (UInt256.ofNat 4885)
        ([pbi,paEnd,pbEnd,flag,slot,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4993) ([dst,ret] ++ rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hc15 : rest.length+15 < 1024 := by omega
  have hc16 : rest.length+16 < 1024 := by omega
  simp [fullExitProgram, dropCache, CiosCached.tailProgram, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14,hc15,hc16,
    htarget, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

#print axioms run_middleStore
#print axioms run_tail
#print axioms run_exit
end Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorTrace
