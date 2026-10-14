import Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def frame (pbi hd pb ent tn target inv : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi,hd,pb,ent,tn,allOnes,target,inv] ++ rest

def reset : List Instr := [.push 0 0, .op (.Swap ⟨4, by decide⟩), .op .POP]

def flush : List Instr := [.op (.Dup ⟨4, by decide⟩), .push 2 2080, .op .MSTORE]

def advanceShort : List Instr :=
  [.push 1 31, .op .NOT, .op .ADD, .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Dup ⟨2, by decide⟩), .op .JUMPI]

/-- zneg2: the row pointer counts up to zero through negatives (`PUSH1 20 ADD DUP1 DUP3 JUMPI`):
the next row while it is nonzero. -/
def advance : List Instr :=
  [.push 1 32, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .JUMPI]

theorem run_reset (pc0 : Nat) (s : State) (pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions reset (framed s (UInt256.ofNat pc0) (frame pbi hd pb ent tn target inv rest)) =
    some (framed s (UInt256.ofNat (pc0+3)) (frame pbi hd pb ent 0 target inv rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  simp [reset, frame, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc8, hc9, Nat.add_assoc, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_flush (pc0 : Nat) (s : State) (pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions flush (framed s (UInt256.ofNat pc0) (frame pbi hd pb ent tn target inv rest)) =
    some (framed {s with memory := TnCacheMemory.lift s.memory tn}
      (UInt256.ofNat (pc0+5)) (frame pbi hd pb ent tn target inv rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have haw := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp [flush, frame, runInstructions, framed, TnCacheMemory.lift,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, Nat.add_assoc, haw, haddr,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_advance (pc0 : Nat) (s : State) (pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions advance (framed s (UInt256.ofNat pc0) (frame pbi hd pb ent tn target inv rest)) =
    some (framed s
      (if UInt256.isTrue (UInt256.ofNat 32+pbi) then hd else UInt256.ofNat (pc0+6))
      (frame (UInt256.ofNat 32+pbi) hd pb ent tn target inv rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.ofNat 32+pbi) <;>
    simp [advance, frame, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
      hc8, hc9, hc10, Nat.add_assoc, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_advanceShort (pc0 : Nat) (s : State) (pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions advanceShort (framed s (UInt256.ofNat pc0) (frame pbi hd pb ent tn target inv rest)) =
    some (framed s
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd else UInt256.ofNat (pc0+9))
      (frame (negative32+pbi) hd pb ent tn target inv rest)) := by
  have hnegative : UInt256.lnot (UInt256.ofNat 31) = negative32 := by decide
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt (negative32+pbi) pb) <;>
    simp [advanceShort, hnegative, frame, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
      hc8, hc9, hc10, Nat.add_assoc, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- P1: the carry cache rides in the thirteenth frame word; `PUSH0; SWAP13; POP` clears it. -/
def reset13 : List Instr := [.push 0 0, .op (.Swap ⟨12, by decide⟩), .op .POP]

/-- P1: `DUP13; PUSH2 2080; MSTORE` flushes the carry cache from the thirteenth frame word. -/
def flush13 : List Instr := [.op (.Dup ⟨12, by decide⟩), .push 2 2080, .op .MSTORE]

theorem run_reset13 (pc0 : Nat) (s : State) (pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) :
    runInstructions reset13 (framed s (UInt256.ofNat pc0)
      (frame pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: tn :: rest))) =
    some (framed s (UInt256.ofNat (pc0+3))
      (frame pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: 0 :: rest))) := by
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  simp [reset13, frame, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc12, hc13, hc14, Nat.add_assoc, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_flush13 (pc0 : Nat) (s : State) (pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions flush13 (framed s (UInt256.ofNat pc0)
      (frame pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: tn :: rest))) =
    some (framed {s with memory := TnCacheMemory.lift s.memory tn}
      (UInt256.ofNat (pc0+5)) (frame pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: tn :: rest))) := by
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hc15 : rest.length+15 < 1024 := by omega
  have haw := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp [flush13, frame, runInstructions, framed, TnCacheMemory.lift,
    Challenge.EvmProof.Stepper.runInstr, hc12, hc13, hc14, hc15, Nat.add_assoc, haw, haddr,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_reset
#print axioms run_flush
#print axioms run_advance
#print axioms run_advanceShort
#print axioms run_reset13
#print axioms run_flush13
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps
