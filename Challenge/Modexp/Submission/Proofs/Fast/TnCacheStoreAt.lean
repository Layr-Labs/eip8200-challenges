import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheStoreAt
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open CiosCachedMacCore CiosCached Monpro

def middle : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨6, by decide⟩), .op .GT,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem carry_gt (a b : UInt256) :
    UInt256.gt a (a+b) = UInt256.lt (a+b) b := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  have he : (a+b).toNat < a.toNat ↔ (a+b).toNat < b.toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_add]
    omega
  simp only [UInt256.gt, UInt256.lt, he]

def tail : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .POP]

theorem run_middle (pc0 : Nat) (s : State) (c bi pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions middle
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,bi,pbi,hd,pb,ent,tn,allOnes,target,inv] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0 + 7))
      ([UInt256.lt (tn+c) c,pbi,hd,pb,ent,tn+c,allOnes,target,inv] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have h13 : rest.length + 13 < 1024 := by omega
  simp (config := {maxSteps := 100000})
    [middle, carry_gt, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
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

def middle15 : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨14, by decide⟩), .op .GT,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

def tail16 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨15, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op .LT, .op .ADD, .op (.Swap ⟨12, by decide⟩), .op .POP]

theorem run_middle15 (pc0 : Nat) (s : State)
    (c bi pbi hd pb ent w7 target w10 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) :
    runInstructions middle15
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,bi,pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,tn] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0 + 7))
      ([UInt256.lt (tn+c) c,pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,tn+c] ++ rest)) := by
  have h13 : rest.length + 13 < 1024 := by omega
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp (config := {maxSteps := 100000})
    [middle15, carry_gt, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
     h13,h14,h15,h16,h17,h18, List.exchange, Nat.add_assoc,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

def middle14 : List Instr :=
  [.op (.Dup ⟨13, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨13, by decide⟩), .op .GT]

theorem run_middle14 (pc0 : Nat) (s : State)
    (c pbi hd pb ent w7 target w10 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) :
    runInstructions middle14
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,tn] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0 + 5))
      ([UInt256.lt (tn+c) c,pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,tn+c] ++ rest)) := by
  have h13 : rest.length + 13 < 1024 := by omega
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  simp (config := {maxSteps := 100000})
    [middle14, carry_gt, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
     h13,h14,h15,h16,h17, List.exchange, Nat.add_assoc,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tail16 (pc0 : Nat) (s : State)
    (c f pbi hd pb ent w7 target w10 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions tail16
      (framed s (UInt256.ofNat (pc0 + 0))
        ([c,f,pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,tn] ++ rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (tn+c).toNat 32) 2112)} (UInt256.ofNat (pc0 + 12))
      ([pbi,hd,pb,ent,w7,allOnes,target,w10,r0,r1,r2,r3,UInt256.lt (tn+c) c+f] ++ rest)) := by
  have h13 : rest.length + 13 < 1024 := by omega
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000})
    [tail16, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
     h13,h14,h15,h16,h17,h18, List.exchange, Nat.add_assoc, ht, hactT,
     State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.TnCacheStoreAt
