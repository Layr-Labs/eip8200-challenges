import Challenge.Modexp.Submission.Proofs.Fast.SquareTop
import Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit

def base (pbi pa pb delta dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi,pa,pb,delta,negative32,allOnes,dst,ret] ++ rest

def headProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD]

def prepProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def borrowProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op .SUB]

def loadProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 8256,
   .op .ADD,
   .op .MLOAD,
   .op .ADD]

def storeProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 2 8256,
   .op .ADD,
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB]

theorem run_head (s : State) (pbi pa pb tag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hpbi : pbi.toNat+32 ≤ 9472) :
    runInstructions headProgram (framed s (UInt256.ofNat 5190) (base pbi pa pb tag dst ret rest)) =
      some (framed s (UInt256.ofNat 5198)
        (MachineState.readWord s.memory pbi.toNat :: base pbi pa pb (pbi-pa) dst ret rest)) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s pbi.toNat 32 (by decide) hpbi hact
  simp [headProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base,
    hc8, hc9, hc10, ha, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prep (s : State) (ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) :
    runInstructions prepProgram
      (framed s (UInt256.ofNat 5198) (ai :: base pbi pa pb delta dst ret rest)) =
      some (framed s (UInt256.ofNat 5200) ([maxWord,ai,ai] ++ base pbi pa pb delta dst ret rest)) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  simp [prepProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base,
    hc9, hc10, allOnes_value, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_borrow (s : State) (hi lo ai : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017) :
    runInstructions borrowProgram (framed s (UInt256.ofNat 5206) ([hi,lo,ai] ++ rest)) =
      some (framed s (UInt256.ofNat 5210) ([UInt256.gt lo hi-hi,lo,ai] ++ rest)) := by
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  simp [borrowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    hc3, hc4, hc5, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_load (s : State) (part lo ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8256+delta).toNat 32) = s.activeWords) :
    runInstructions loadProgram
      (framed s (UInt256.ofNat 5210) ([part,lo,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed s (UInt256.ofNat 5218)
        ([MachineState.readWord s.memory (UInt256.ofNat 8256+delta).toNat+lo,part,lo,ai] ++
          base pbi pa pb delta dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
  have haddr : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  simp [loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base,
    hc11, hc12, hc13, hc14, haddr, ha, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_store (s : State) (v part lo ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8256+delta).toNat 32) = s.activeWords) :
    runInstructions storeProgram
      (framed s (UInt256.ofNat 5218) ([v,part,lo,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := storeWord s.memory (UInt256.ofNat 8256+delta).toNat v}
        (UInt256.ofNat 5229)
        ([(UInt256.gt lo v-part)-lo,ai] ++ base pbi pa pb delta dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hc15 : rest.length+15 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
  have haddr : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  simp [storeProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base, storeWord,
    hc10, hc11, hc12, hc13, hc14, hc15, haddr, ha, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem diag_carry (ai t : UInt256) :
    (UInt256.gt (ai*ai) (t+ai*ai) -
      (UInt256.gt (ai*ai) (UInt256.mulMod ai ai maxWord)-UInt256.mulMod ai ai maxWord)) - ai*ai =
      macCarry ai ai t (UInt256.ofNat 0) := by
  have h := carry_eq ai ai t (UInt256.ofNat 0)
  have hz : UInt256.gt (UInt256.ofNat 0) (ai*ai) = UInt256.ofNat 0 := by
    simp [UInt256.gt, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [SquareTop.add_zero, partialCarry, SquareTop.add_zero, hz] at h
  rw [← h]
  let u := UInt256.gt (ai*ai) (t+ai*ai)
  let v := UInt256.gt (ai*ai) (UInt256.mulMod ai ai maxWord)-UInt256.mulMod ai ai maxWord
  let w := ai*ai
  change UInt256.mk ((u.val-v.val)-w.val) = UInt256.mk (u.val+((0-v.val)-w.val))
  congr 1
  simp only [sub_eq_add_neg, _root_.zero_add, add_assoc]

def diagProgram : List Instr :=
  (((prepProgram ++ CiosNoDummyCarry.multiplyProgram) ++ borrowProgram) ++ loadProgram) ++ storeProgram

theorem run_diag (s : State) (ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8256+delta).toNat 32) = s.activeWords) :
    runInstructions diagProgram
      (framed s (UInt256.ofNat 5198) (ai :: base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := (storeWord s.memory (UInt256.ofNat 8256+delta).toNat
          (macSum ai ai (MachineState.readWord s.memory (UInt256.ofNat 8256+delta).toNat) (UInt256.ofNat 0)))}
        (UInt256.ofNat 5229)
        ([macCarry ai ai (MachineState.readWord s.memory (UInt256.ofNat 8256+delta).toNat) (UInt256.ofNat 0),ai] ++
          base pbi pa pb delta dst ret rest)) := by
  let lo := ai*ai
  let mm := UInt256.mulMod ai ai maxWord
  let part := UInt256.gt lo mm-mm
  let t := MachineState.readWord s.memory (UInt256.ofNat 8256+delta).toNat
  have hp := run_prep s ai pbi pa pb delta dst ret rest hcap
  have hm := CiosNoDummyCarry.run_multiply s (UInt256.ofNat 5200) ai ai
    (base pbi pa pb delta dst ret rest) (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega)
  have hb := run_borrow s mm lo ai (base pbi pa pb delta dst ret rest)
    (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega)
  have hl := run_load s part lo ai pbi pa pb delta dst ret rest hcap ha
  have hs := run_store s (t+lo) part lo ai pbi pa pb delta dst ret rest hcap ha
  have h1 := runInstructions_append_some _ _ _ _ _ hp hm
  have h2 := runInstructions_append_some _ _ _ _ _ h1 hb
  have h3 := runInstructions_append_some _ _ _ _ _ h2 hl
  have h4 := runInstructions_append_some _ _ _ _ _ h3 hs
  simpa only [diagProgram, part, lo, mm, t, diag_carry, macSum, SquareTop.zero_add] using h4

end Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal
