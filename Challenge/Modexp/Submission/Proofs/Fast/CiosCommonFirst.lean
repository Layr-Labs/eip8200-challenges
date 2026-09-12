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

private theorem fusedSub (carry borrow a lo : UInt256) :
    (carry - (borrow - a)) - lo = carry + ((a - borrow) - lo) := by
  apply Challenge.EvmProof.Word.word_ext
  have hc : carry.toNat < 2 ^ 256 := carry.val.isLt
  have hb : borrow.toNat < 2 ^ 256 := borrow.val.isLt
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hl : lo.toNat < 2 ^ 256 := lo.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add]
  omega

private theorem fusedCarry (x y t : UInt256) :
    ((UInt256.gt (x * y) (x * y + t) -
      (UInt256.gt (x * y) (UInt256.mulMod y x maxWord) - UInt256.mulMod y x maxWord)) -
      x * y) = macCarry x y t (UInt256.ofNat 0) := by
  have hhi := CiosNoDummyCarry.high_eq x y
  have hc := carry_eq x y t (UInt256.ofNat 0)
  have hz : x * y + UInt256.ofNat 0 = x * y := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    exact Nat.mod_eq_of_lt (x * y).val.isLt
  rw [hz] at hc
  rw [Challenge.EvmProof.Word.word_add_comm (x * y) t]
  rw [fusedSub]
  have hgt : UInt256.gt (x * y) (UInt256.mulMod y x maxWord) =
      UInt256.lt (UInt256.mulMod y x maxWord) (x * y) := by rfl
  rw [hgt, hhi]
  exact hc

theorem run_fusedPost (s : State)
    (pc mm lo bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords) :
    runInstructions commonFusedPost
      (framed s pc ([mm, lo, bi] ++ tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed {s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tl.toNat).toNat 32) tl.toNat)}
      (advancePC 15 pc)
      ([((UInt256.gt lo (lo + MachineState.readWord s.memory tl.toNat) -
          (UInt256.gt lo mm - mm)) - lo), bi] ++
        tail pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  simp [commonFusedPost, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, tail, hc18, hc19, hc20, hc21, hc22, State.activeWordsAfterUInt256,
    hactive, List.exchange, advancePC, Challenge.EvmProof.Word.word_add_comm]

theorem run_padding (s : State) (pc : UInt256) (stack : List UInt256)
    (hcap : stack.length < 1024) :
    runInstructions commonPadding (framed s pc stack) =
      some (framed s (advancePC 2 pc) stack) := by
  simp [commonPadding, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, advancePC,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hcap]

/-- Both admitted widths have zero carry at the first limb of each row. -/
theorem run_commonFirst (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 91 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 2912)
    (htl : tl = UInt256.ofNat (2080+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) :
    runInstructions commonFirstActiveProgram
      (firstAt 4040 s mem bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (l1At 4066 s mem bi pa pb n i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have ha : aEnd.toNat = pa+32*(n-1) := by
    rw [hAend,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have ht : tl.toNat = 2112+32*(n-1) := by
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
  have hl := run_load st (UInt256.ofNat 4040) bi pbi hd (UInt256.ofNat (pb-32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hA
  have hm := CiosNoDummyCarry.run_multiply st (advancePC 3 (UInt256.ofNat 4040))
    (MachineState.readWord mem aEnd.toNat) bi frame
    (by simp only [frame, tail, List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := run_fusedPost st
    (advancePC 6 (advancePC 3 (UInt256.ofNat 4040)))
    (UInt256.mulMod bi (MachineState.readWord mem aEnd.toNat) maxWord)
    (MachineState.readWord mem aEnd.toNat * bi) bi pbi hd (UInt256.ofNat (pb - 32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hT
  rw [fusedCarry (MachineState.readWord mem aEnd.toNat) bi
    (MachineState.readWord mem tl.toNat)] at hf
  let stored : State := {st with memory := (MachineState.writeBytes st.memory
    (Data.Bytes.natToBytesPadded
      (MachineState.readWord mem aEnd.toNat * bi + MachineState.readWord mem tl.toNat).toNat 32)
    tl.toNat)}
  have hpad := run_padding stored
    (advancePC 15 (advancePC 6 (advancePC 3 (UInt256.ofNat 4040))))
    ([macCarry (MachineState.readWord mem aEnd.toNat) bi
        (MachineState.readWord mem tl.toNat) (UInt256.ofNat 0), bi] ++ frame)
    (by simp only [frame, tail, List.length_append, List.length_cons, List.length_nil]; omega)
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have body := runInstructions_append_some _ _ _ _ _ both hf
  have hall := runInstructions_append_some _ _ _ _ _ body hpad
  have hzero : MachineState.readWord mem aEnd.toNat * bi + UInt256.ofNat 0 =
      MachineState.readWord mem aEnd.toNat * bi := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    exact Nat.mod_eq_of_lt (MachineState.readWord mem aEnd.toNat * bi).val.isLt
  have hsum := sum_eq (MachineState.readWord mem aEnd.toNat) bi
    (MachineState.readWord mem tl.toNat) (UInt256.ofNat 0)
  rw [hzero] at hsum
  have hsum' : MachineState.readWord mem aEnd.toNat * bi +
      MachineState.readWord mem tl.toNat =
      macSum (MachineState.readWord mem aEnd.toNat) bi
        (MachineState.readWord mem tl.toNat) (UInt256.ofNat 0) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hsum
  have hsumFinal := hsum'
  rw [ha, ht] at hsumFinal
  have hpc : advancePC 2 (advancePC 15
      (advancePC 6 (advancePC 3 (UInt256.ofNat 4040)))) = UInt256.ofNat 4066 := by decide
  simpa only [commonFirstActiveProgram, L2.multiplyProgram, commonPadding,
    show (0 : UInt256) = UInt256.ofNat 0 from by decide, st, stored, frame, pbi, tail,
    firstAt, l1At, l1Q, l1Step, framed, ha, ht, hpc, hsumFinal, Nat.sub_zero,
    List.cons_append, List.nil_append] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosCommonFirst
