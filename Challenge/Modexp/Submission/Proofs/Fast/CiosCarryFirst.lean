import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirst

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore CiosReadonly

variable {carrySlot : UInt256}

def tail (pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [pbi,pa,pb,flag,carrySlot,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

theorem run_load (s : State) (pc bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    :
    runInstructions commonFirstLoad
      (framed s pc ([bi] ++ tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (advancePC 2 pc)
      ([maxWord,aEnd,bi] ++
        tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  simp [commonFirstLoad,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc17,hc18,hc19,State.activeWordsAfterUInt256,advancePC,allOnes_value]

theorem sub_flip (a b c d : UInt256) :
    (a-(b-c))-d = a+((c-b)-d) := by
  apply Challenge.EvmProof.Word.word_ext
  have ha : a.toNat < 2^256 := a.val.isLt
  have hb : b.toNat < 2^256 := b.val.isLt
  have hc : c.toNat < 2^256 := c.val.isLt
  have hd : d.toNat < 2^256 := d.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add]
  omega

theorem run_suffix (s : State)
    (pc hi lo bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFusedFinish
      (framed s pc ([hi,lo,bi] ++ tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded (MachineState.readWord s.memory tl.toNat+lo).toNat 32) tl.toNat)}
      (advancePC 15 pc)
      ([UInt256.lt (MachineState.readWord s.memory tl.toNat+lo) lo + ((hi-UInt256.lt hi lo)-lo),bi] ++
        tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hc21 : rest.length+21 < 1024 := by omega
  have hc22 : rest.length+22 < 1024 := by omega
  simp [commonFusedFinish,runInstructions,Challenge.EvmProof.Stepper.runInstr,framed,tail,
    hc18,hc19,hc20,hc21,hc22,hactive,State.activeWordsAfterUInt256,
    advancePC,sub_flip,UInt256.gt,UInt256.lt]


theorem run_finish (s : State)
    (pc x bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFusedFinish
      (framed s pc ([UInt256.mulMod bi x maxWord,x*bi,bi] ++ tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (macSum x bi (MachineState.readWord s.memory tl.toNat) 0).toNat 32) tl.toNat)}
      (advancePC 15 pc)
      ([macCarry x bi (MachineState.readWord s.memory tl.toNat) 0,bi] ++
        tail (carrySlot := carrySlot) pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hs := run_suffix (carrySlot := carrySlot) s pc (UInt256.mulMod bi x maxWord) (x*bi) bi
    pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hactive
  rw [CiosNoDummyCarry.high_eq] at hs
  have hz : x*bi + (0 : UInt256) = x*bi := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      show (0 : UInt256) = UInt256.ofNat 0 from by decide,
      Challenge.EvmProof.Word.word_toNat_ofNat,Nat.zero_mod,Nat.add_zero]
    exact Nat.mod_eq_of_lt (x*bi).val.isLt
  have hc := carry_eq x bi (MachineState.readWord s.memory tl.toNat) 0
  have hv := sum_eq x bi (MachineState.readWord s.memory tl.toNat) 0
  rw [hz] at hc hv
  simp only [UInt256.gt, UInt256.lt,
    show (0 : UInt256) = UInt256.ofNat 0 from by decide] at hc hs hv ⊢
  rw [hc,hv] at hs
  exact hs

#print axioms run_finish

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirst
