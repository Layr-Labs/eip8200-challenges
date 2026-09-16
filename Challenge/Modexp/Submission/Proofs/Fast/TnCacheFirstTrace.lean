import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheFirstTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore CiosReadonly

def tail (pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [pbi,pa,pb,flag,tn,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

theorem run_load (s : State) (pc bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat aEnd.toNat 32) = s.activeWords) :
    runInstructions commonFirstLoad
      (framed s pc ([bi] ++ tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (advancePC 3 pc)
      ([maxWord,MachineState.readWord s.memory aEnd.toNat,bi] ++
        tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  simp [commonFirstLoad,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc17,hc18,hc19,State.activeWordsAfterUInt256,hactive,advancePC,allOnes_value]

theorem run_fusedLoad (s : State)
    (pc mm lo bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFusedLoad
      (framed s pc ([mm,lo,bi] ++ tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (pc+UInt256.ofNat 8)
      ([MachineState.readWord s.memory tl.toNat+lo,UInt256.lt mm lo-mm,lo,bi] ++
        tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hc21 : rest.length+21 < 1024 := by omega
  simp [commonFusedLoad,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc19,hc20,hc21,State.activeWordsAfterUInt256,hactive,
    succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_fusedStore (s : State)
    (pc value d lo bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFusedStore
      (framed s pc ([value,d,lo,bi] ++ tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) tl.toNat)} (pc+UInt256.ofNat 7)
      ([(UInt256.gt lo value-d)-lo,bi] ++ tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hc21 : rest.length+21 < 1024 := by omega
  have hc22 : rest.length+22 < 1024 := by omega
  simp [commonFusedStore,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc18,hc19,hc20,hc21,hc22,State.activeWordsAfterUInt256,hactive,
    succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]

private theorem mul_add_zero (x y : UInt256) : x*y + UInt256.ofNat 0 = x*y := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,Nat.zero_mod,Nat.add_zero]
  exact Nat.mod_eq_of_lt (x*y).val.isLt

/-- The fused carry is `carry_eq` at carry-in `0`, reassociated. -/
theorem fused_carry (x y t : UInt256) :
    (UInt256.gt (x*y) (t+x*y) -
      (UInt256.lt (UInt256.mulMod y x maxWord) (x*y) - UInt256.mulMod y x maxWord)) - x*y =
    macCarry x y t (UInt256.ofNat 0) := by
  have h := carry_eq x y t (UInt256.ofNat 0)
  have h0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have hg : UInt256.gt (UInt256.ofNat 0) (x*y) = UInt256.ofNat 0 := by
    simp only [UInt256.gt, h0, gt_iff_lt, Nat.not_lt_zero, if_false]
  rw [partialCarry, mul_add_zero, hg] at h
  rw [← h]
  have hv : (UInt256.ofNat 0).val = 0 := by decide
  change UInt256.mk ((_ - _) - (x*y).val) = UInt256.mk (_ + (((UInt256.ofNat 0).val - _) - (x*y).val))
  congr 1
  rw [hv]
  simp only [sub_eq_add_neg, zero_add, add_assoc]

theorem fused_sum (x y t : UInt256) : t + x*y = macSum x y t (UInt256.ofNat 0) := by
  rw [← sum_eq, mul_add_zero]

theorem run_fused (s : State)
    (pc x bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions (commonFusedLoad ++ commonFusedStore)
      (framed s pc ([UInt256.mulMod bi x maxWord,x*bi,bi] ++
        tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (macSum x bi (MachineState.readWord s.memory tl.toNat) (UInt256.ofNat 0)).toNat 32) tl.toNat)}
      (pc+UInt256.ofNat 15)
      ([macCarry x bi (MachineState.readWord s.memory tl.toNat) (UInt256.ofNat 0),bi] ++
        tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hl := run_fusedLoad s pc (UInt256.mulMod bi x maxWord) (x*bi) bi
    pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hactive
  have hs := run_fusedStore s (pc+UInt256.ofNat 8)
    (MachineState.readWord s.memory tl.toNat+x*bi)
    (UInt256.lt (UInt256.mulMod bi x maxWord) (x*bi) - UInt256.mulMod bi x maxWord) (x*bi) bi
    pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hactive
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  rw [fused_carry,fused_sum] at both
  simpa only [pc_add_add] using both

/-- The full first-limb program preserves any cached high carry in its frame. -/
theorem run_first (pc0 : Nat) (s : State)
    (bi pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat aEnd.toNat 32) = s.activeWords)
    (hT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFirstProgram
      (framed s (UInt256.ofNat pc0)
        ([bi] ++ tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (macSum (MachineState.readWord s.memory aEnd.toNat) bi
            (MachineState.readWord s.memory tl.toNat) (UInt256.ofNat 0)).toNat 32) tl.toNat)}
      (UInt256.ofNat (pc0 + 24))
      ([macCarry (MachineState.readWord s.memory aEnd.toNat) bi
        (MachineState.readWord s.memory tl.toNat) (UInt256.ofNat 0), bi] ++
        tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  let frame := tail pbi pa pb flag tn target2 tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hl := run_load s (UInt256.ofNat pc0) bi pbi pa pb flag tn target2
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hA
  have hm := CiosNoDummyCarry.run_multiply s (advancePC 3 (UInt256.ofNat pc0))
    (MachineState.readWord s.memory aEnd.toNat) bi frame
    (by simp only [frame, tail, List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := run_fused s (advancePC 6 (advancePC 3 (UInt256.ofNat pc0)))
    (MachineState.readWord s.memory aEnd.toNat) bi pbi pa pb flag tn target2
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hT
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 6 (advancePC 3 (UInt256.ofNat pc0)) + UInt256.ofNat 15 =
      UInt256.ofNat (pc0 + 24) := by
    simp [advancePC, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [commonFirstProgram, frame, hpc] using hall

#print axioms run_first
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheFirstTrace
