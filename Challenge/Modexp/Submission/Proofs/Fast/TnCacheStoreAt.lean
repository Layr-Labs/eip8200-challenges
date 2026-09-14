import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheStoreAt
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open CiosCachedMacCore CiosCached Monpro

/-- Replace the top carry's middle memory store by a frame-slot update. -/
def middle : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨7, by decide⟩), .op .POP,
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP]

/-- The low output is still written; the final top carry stays in the frame. -/
def tail : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .POP]

theorem run_middle (pc0 : Nat) (s : State) (c bi pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions middle
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,bi,pbi,hd,pb,ent,tn,allOnes,target,inv] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0 + 9))
      ([UInt256.lt (tn+c) c,pbi,hd,pb,ent,tn+c,allOnes,target,inv] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have h13 : rest.length + 13 < 1024 := by omega
  simp (config := {maxSteps := 100000})
    [middle, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
     h8,h9,h10,h11,h12,h13, List.exchange, Nat.add_assoc,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tail (pc0 : Nat) (s : State) (c f pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions tail
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,f,pbi,hd,pb,ent,tn,allOnes,target,inv] ++ rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (tn+c).toNat 32) 2112)} (UInt256.ofNat (pc0 + 12))
      ([pbi,hd,pb,ent,UInt256.lt (tn+c) c+f,allOnes,target,inv] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have h13 : rest.length + 13 < 1024 := by omega
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000})
    [tail, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
     h8,h9,h10,h11,h12,h13, List.exchange, Nat.add_assoc, ht, hactT,
     State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_middle
#print axioms run_tail
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheStoreAt
