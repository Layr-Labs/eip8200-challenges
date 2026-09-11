import Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareCross
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def xword (mem : ByteArray) (delta : UInt256) : UInt256 :=
  SquareWords.clearBit (MachineState.readWord mem (UInt256.ofNat 8928+delta).toNat)

def loadProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .push 2 8928,
   .op .ADD,
   .op .MLOAD,
   .push 1 1,
   .op .NOT,
   .op .AND,
   .op (.Dup ⟨8, by decide⟩)]

def finishLoadProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 8224,
   .op .ADD,
   .op .MLOAD,
   .op .ADD]

def finishStoreProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 2 8224,
   .op .ADD,
   .op .MSTORE,
   .op .LT,
   .op .ADD]

theorem land_comm (x y : UInt256) : UInt256.land x y = UInt256.land y x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Nat.and_comm]

theorem run_load (s : State) (c ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8928+delta).toNat 32) = s.activeWords) :
    runInstructions loadProgram
      (framed s (UInt256.ofNat 5235) ([c,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed s (UInt256.ofNat 5246)
        ([maxWord,xword s.memory delta,c,ai] ++ base pbi pa pb delta dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
  have haddr : (8928 : UInt256) = UInt256.ofNat 8928 := by decide
  simp [loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base,
    xword, SquareWords.clearBit, hc10, hc11, hc12, haddr, ha, allOnes_value,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  exact land_comm _ _

theorem run_finish_load (s : State) (part sum ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8224+delta).toNat 32) = s.activeWords) :
    runInstructions finishLoadProgram
      (framed s (UInt256.ofNat 5264) ([part,sum,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed s (UInt256.ofNat 5273)
        ([MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat+sum,sum,part,ai] ++
          base pbi pa pb delta dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
  have haddr : (8224 : UInt256) = UInt256.ofNat 8224 := by decide
  simp [finishLoadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base,
    hc11, hc12, hc13, hc14, haddr, ha, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_finish_store (s : State) (v sum part ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8224+delta).toNat 32) = s.activeWords) :
    runInstructions finishStoreProgram
      (framed s (UInt256.ofNat 5273) ([v,sum,part,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := storeWord s.memory (UInt256.ofNat 8224+delta).toNat v}
        (UInt256.ofNat 5282)
        ([UInt256.lt v sum+part,ai] ++ base pbi pa pb delta dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hc15 : rest.length+15 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] at ha
  have haddr : (8224 : UInt256) = UInt256.ofNat 8224 := by decide
  simp [finishStoreProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, base, storeWord,
    hc10, hc11, hc12, hc13, hc14, hc15, haddr, ha, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def finishProgram : List Instr := finishLoadProgram ++ finishStoreProgram

theorem run_finish (s : State) (x c ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8224+delta).toNat 32) = s.activeWords) :
    runInstructions finishProgram
      (framed s (UInt256.ofNat 5264) ([partialCarry x ai c,x*ai+c,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := (storeWord s.memory (UInt256.ofNat 8224+delta).toNat
          (macSum x ai (MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat) c))}
        (UInt256.ofNat 5282)
        ([macCarry x ai (MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat) c,ai] ++
          base pbi pa pb delta dst ret rest)) := by
  let t := MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat
  have hl := run_finish_load s (partialCarry x ai c) (x*ai+c) ai pbi pa pb delta dst ret rest hcap ha
  have hs := run_finish_store s (t+(x*ai+c)) (x*ai+c) (partialCarry x ai c) ai pbi pa pb delta dst ret rest hcap ha
  have h := runInstructions_append_some _ _ _ _ _ hl hs
  have hc : UInt256.lt (t+(x*ai+c)) (x*ai+c)+partialCarry x ai c = macCarry x ai t c := carry_eq x ai t c
  rw [hc, sum_eq] at h
  exact h

def crossProgram : List Instr := (loadProgram ++ L2.productProgram) ++ finishProgram

theorem run_cross (s : State) (c ai pbi pa pb delta dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8928+delta).toNat 32) = s.activeWords)
    (ht : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (UInt256.ofNat 8224+delta).toNat 32) = s.activeWords) :
    runInstructions crossProgram
      (framed s (UInt256.ofNat 5235) ([c,ai] ++ base pbi pa pb delta dst ret rest)) =
      some (framed {s with memory := (storeWord s.memory (UInt256.ofNat 8224+delta).toNat
          (macSum (xword s.memory delta) ai (MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat) c))}
        (UInt256.ofNat 5282)
        ([macCarry (xword s.memory delta) ai (MachineState.readWord s.memory (UInt256.ofNat 8224+delta).toNat) c,ai] ++
          base pbi pa pb delta dst ret rest)) := by
  have hl := run_load s c ai pbi pa pb delta dst ret rest hcap ha
  have hp := L2.run_product s (UInt256.ofNat 5246) (xword s.memory delta) ai c
    (base pbi pa pb delta dst ret rest)
    (by simp only [base, List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := run_finish s (xword s.memory delta) c ai pbi pa pb delta dst ret rest hcap ht
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hl hp) hf

end Challenge.Modexp.Submission.Proofs.Fast.SquareCross
