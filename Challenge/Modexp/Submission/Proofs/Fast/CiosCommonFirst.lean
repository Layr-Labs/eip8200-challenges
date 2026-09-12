import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCommonFirst

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore CiosReadonly

def tail (pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [pbi,pa,pb,flag,negative32,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

theorem run_load (s : State) (pc bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat aEnd.toNat 32) = s.activeWords) :
    runInstructions commonFirstLoad
      (framed s pc ([bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (advancePC 3 pc)
      ([maxWord,MachineState.readWord s.memory aEnd.toNat,bi] ++
        tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  simp [commonFirstLoad,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc17,hc18,hc19,State.activeWordsAfterUInt256,hactive,advancePC,allOnes_value]

theorem run_finishLoad (s : State)
    (pc part sum bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFinishLoad
      (framed s pc ([part,sum,bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (pc+UInt256.ofNat 5)
      ([MachineState.readWord s.memory tl.toNat+sum,sum,part,bi] ++
        tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hc21 : rest.length+21 < 1024 := by omega
  simp [commonFinishLoad,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc19,hc20,hc21,State.activeWordsAfterUInt256,hactive,List.exchange,
    succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_finishStore (s : State)
    (pc value sum part bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFinishStore
      (framed s pc ([value,sum,part,bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) tl.toNat)} (pc+UInt256.ofNat 5)
      ([UInt256.lt value sum+part,bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hc21 : rest.length+21 < 1024 := by omega
  have hc22 : rest.length+22 < 1024 := by omega
  simp [commonFinishStore,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,tail,hc18,hc19,hc20,hc21,hc22,State.activeWordsAfterUInt256,hactive,
    succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_finish (s : State)
    (pc x bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions (commonFinishLoad ++ commonFinishStore)
      (framed s pc ([partialCarry x bi 0,x*bi+0,bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (macSum x bi (MachineState.readWord s.memory tl.toNat) 0).toNat 32) tl.toNat)}
      (pc+UInt256.ofNat 10)
      ([macCarry x bi (MachineState.readWord s.memory tl.toNat) 0,bi] ++
        tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hl := run_finishLoad s pc (partialCarry x bi 0) (x*bi+0) bi
    pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hactive
  have hs := run_finishStore s (pc+UInt256.ofNat 5)
    (MachineState.readWord s.memory tl.toNat+(x*bi+0)) (x*bi+0) (partialCarry x bi 0) bi
    pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hactive
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have hcarry : UInt256.lt (MachineState.readWord s.memory tl.toNat+(x*bi+0)) (x*bi+0) +
      partialCarry x bi 0 = macCarry x bi (MachineState.readWord s.memory tl.toNat) 0 :=
    carry_eq x bi (MachineState.readWord s.memory tl.toNat) 0
  rw [hcarry,sum_eq] at both
  simpa only [pc_add_add] using both

/-- Both admitted widths have zero carry at the first limb of each row. -/
theorem run_commonFirst (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 9472)
    (htl : tl = UInt256.ofNat (8224+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) :
    runInstructions commonFirstProgram
      (firstAt 4032 s mem bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (l1At 4058 s mem bi pa pb n i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have ha : aEnd.toNat = pa+32*(n-1) := by
    rw [hAend,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have ht : tl.toNat = 8256+32*(n-1) := by
    rw [htl,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  let st : State := {s with memory := mem}
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat aEnd.toNat 32) = st.activeWords := by
    rw [ha]
    exact activeWords_fix st _ 32 (by decide) (by omega) hact
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) = st.activeWords := by
    rw [ht]
    exact activeWords_fix st _ 32 (by decide) (by omega) hact
  let pbi := UInt256.ofNat (ptrAt (pb+32*n-32) i)
  let frame := tail pbi hd (UInt256.ofNat (pb-32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hl := run_load st (UInt256.ofNat 4020) bi pbi hd (UInt256.ofNat (pb-32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hA
  have hp := CiosNoDummyCarry.run_product st (advancePC 3 (UInt256.ofNat 4020))
    (MachineState.readWord mem aEnd.toNat) bi frame
    (by simp only [frame,tail,List.length_append,List.length_cons,List.length_nil]; omega)
  have hf := run_finish st (advancePC 13 (advancePC 3 (UInt256.ofNat 4020)))
    (MachineState.readWord mem aEnd.toNat) bi pbi hd (UInt256.ofNat (pb-32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hT
  have hz : MachineState.readWord mem aEnd.toNat * bi + UInt256.ofNat 0 =
      MachineState.readWord mem aEnd.toNat * bi := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat,Nat.zero_mod,Nat.add_zero]
    exact Nat.mod_eq_of_lt (MachineState.readWord mem aEnd.toNat * bi).val.isLt
  simp only [show (0 : UInt256) = UInt256.ofNat 0 from by decide] at hf
  rw [hz] at hf
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 13 (advancePC 3 (UInt256.ofNat 4020))+UInt256.ofNat 10 = UInt256.ofNat 4046 := by decide
  simpa only [commonFirstProgram,L2.multiplyProgram,L2.zeroCarryProgram,
    macZeroProductProgram,show (0 : UInt256) = UInt256.ofNat 0 from by decide,st,frame,pbi,tail,firstAt,l1At,l1Q,l1Step,
    framed,ha,ht,hpc,Nat.sub_zero,List.cons_append,List.nil_append] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosCommonFirst
