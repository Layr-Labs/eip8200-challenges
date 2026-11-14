import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroHeadBranchPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroHeadBranchMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftTailPCs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftPrefix
import Challenge.Modexp.Submission.Proofs.CycleGlobal.DifferenceBranch
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RetainedTEntry
noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
/-!
# Block reductions of the shift-reduce base conversion,part 3

The middle block,the two repair loops,the `CSUB` call and the loop exits.
-/
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open CycleSubmission.Global.ShiftPCs
theorem run_e5 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hesize : UInt256.ofNat esize ≠ UInt256.ofNat 1)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (cacheBlock mem)
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 2544) s mem
        n bsize esize msize n) := by
  have hne1 : ¬ (1 = esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) := by
    intro h
    apply hesize
    have hone : (1 : Nat) % 2 ^ 256 = 1 := Nat.mod_eq_of_lt (by norm_num)
    exact Challenge.EvmProof.Word.word_ext (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,hone]
      exact h.symm)
  have he0 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat]
    by_cases h : esize % 2 ^ 256 = 1 % 2 ^ 256
    · exact absurd (Challenge.EvmProof.Word.word_ext (by
          rw [Challenge.EvmProof.Word.word_toNat_ofNat,
            Challenge.EvmProof.Word.word_toNat_ofNat,h])) hesize
    · rw [if_neg h]
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw32 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2901 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2785 := by decide
  have hw4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 10692 := by decide
  have hw8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2660 := by decide
  have hslot1698 : ∀ (v a : Nat),a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hz1 : (if 1 = esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 then
        UInt256.ofNat 1 else UInt256.ofNat 0) = UInt256.ofNat 0 := by
    rw [if_neg hne1]
  have hinitial : initialPhase s mem esize = UInt256.ofNat 0 := by
    have he0r : UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat esize) = UInt256.ofNat 0 := by
      calc
        _ = UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) := by
          simp only [UInt256.eq,eq_comm]
        _ = _ := he0
    unfold initialPhase
    rw [he0r]
    simp [UInt256.land,UInt256.ofNat,UInt256.size,Fin.ofNat,Fin.land,Nat.and_zero]
  rcases hfast with h | h <;> subst h
  all_goals by_cases hshift : (MachineState.readWord mem 1536).toNat = 0
  all_goals simp (config := { maxSteps := 3000000 })
    [cacheBlock,blkCacheChoose,blkCacheNormal,blkCacheZero,hshift,opAt,pushAt,wfOp,he0,hz1,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState,initialContinuation,hinitial,slotState,slotKState,shiftLoopState,rideSlots,entrySlots,aprevSlot,hdSlot,shiftEntry,Exp.storeWord,outer,Exp.outer,hcode,hrun,CycleSubmission.Global.ZeroShiftMath.shr_zero,headWord,loopPC,
      CycleSubmission.Global.ZeroShiftMath.head,CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,UInt256.isZero,
      CycleSubmission.Global.ZeroShiftMath.branch_normal4,CycleSubmission.Global.ZeroShiftMath.branch_normal8,
      CycleSubmission.Global.ZeroShiftMath.branch_zero4,CycleSubmission.Global.ZeroShiftMath.branch_zero8,
      jumpDestCacheNormal,jumpDestLoop2684,jumpDestLoop10692,jumpDestLoop3711,jumpDestLoop3879,
      UInt256.eq,UInt256.isTrue,
      haw1698,haw2816,haw32,hv4,hv8,hw4,hw8,hslot1698,Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]
  all_goals (try simp only [State.activeWordsAfterUInt256,haw1698,haw2816,haw32,
      hslot1698,hv4,hv8,hw4,hw8,hv8,
      Fin.land,Nat.and_zero,Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat,UInt256.size,Fin.ofNat,Fin.land,
      Nat.and_zero,Nat.zero_and,UInt256.toNat])
  all_goals (first | rfl | decide)
/-- An initialized exponent-three cache enters the half-length first loop. -/
theorem run_e5_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyte3 : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) =
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (cacheBlock mem)
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 10213) s mem
        n bsize esize msize (n / 2)) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw32 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod : esize % 2 ^ 256 = 1 % 2 ^ 256 := by
    have h := congrArg UInt256.toNat hsize1
    rwa [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] at h
  have hmodif : (if 1 = esize % 2 ^ 256 then UInt256.ofNat 1 else UInt256.ofNat 0) =
      UInt256.ofNat 1 := by
    rw [if_pos (by rw [hmod]; simp)]
  have he1 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [if_pos hmod]
  have hb3 : UInt256.eq (UInt256.ofNat 3)
      (UInt256.byteAt (UInt256.ofNat 0)
        (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat)) =
      UInt256.ofNat 1 := by
    rw [hbyte3]
    unfold UInt256.eq
    simp
  have hb3t : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) =
      UInt256.ofNat 3 :=
    hbyte3
  have hb3m : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).val.val) =
      UInt256.ofNat 3 :=
    hbyte3
  have hmodl : esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
        Nat) = 2 ^ 256 from rfl,hmod]
    rfl
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2901 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2785 := by decide
  have hw4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 10692 := by decide
  have hw8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2660 := by decide
  have hslot1698 : ∀ (v a : Nat),a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hhi1698 : ∀ (v a : Nat),1698 + 32 ≤ a →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hinitial : initialPhase s mem esize = UInt256.ofNat 1 := by
    unfold initialPhase
    rw [hbyte3,hsize1]
    decide
  rcases hfast with h | h <;> subst h
  all_goals by_cases hshift : (MachineState.readWord mem 1536).toNat = 0
  all_goals simp (config := { maxSteps := 3000000 })
    [cacheBlock,blkCacheChoose,blkCacheNormal,blkCacheZero,hshift,opAt,pushAt,wfOp,he1,hb3,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState,initialContinuation,hinitial,slotState,slotKState,shiftLoopState,rideSlots,entrySlots,aprevSlot,hdSlot,shiftEntry,Exp.storeWord,outer,Exp.outer,hcode,hrun,CycleSubmission.Global.ZeroShiftMath.shr_zero,headWord,loopPC,
      CycleSubmission.Global.ZeroShiftMath.head,CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,UInt256.isZero,
      CycleSubmission.Global.ZeroShiftMath.branch_normal4,CycleSubmission.Global.ZeroShiftMath.branch_normal8,
      CycleSubmission.Global.ZeroShiftMath.branch_zero4,CycleSubmission.Global.ZeroShiftMath.branch_zero8,
      jumpDestCacheNormal,jumpDestLoop2684,jumpDestLoop10692,jumpDestLoop3711,jumpDestLoop3879,
      UInt256.eq,UInt256.isTrue,
      haw1698,haw2816,haw32,hv4,hv8,hw4,hw8,hslot1698,hhi1698,hmodif,hb3t,hb3m,hmodl,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]
  all_goals (try simp only [State.activeWordsAfterUInt256,haw1698,haw2816,haw32,
      hslot1698,hhi1698,hv4,hv8,hw4,hw8,hmodif,hmodl,hb3m,
      Fin.land,Nat.and_zero,Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat,UInt256.size,Fin.ofNat,Fin.land,
      Nat.and_zero,Nat.zero_and,UInt256.toNat,hmodif,hmodl,hb3m])
  all_goals (first | rfl | decide)
/-- Other single-byte exponents enter the ordinary loop with continuation 2310. -/
theorem run_e5_slowexp (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hfast : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyteNe : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) ≠
      UInt256.ofNat 3)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (cacheBlock mem)
      (cacheSetupState s mem n bsize esize msize) =
      some (shiftLoopState (UInt256.ofNat 2544) s mem
        n bsize esize msize n) := by
  have haw1698 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1698 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2816 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw32 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Exp.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod : esize % 2 ^ 256 = 1 % 2 ^ 256 := by
    have h := congrArg UInt256.toNat hsize1
    rwa [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat] at h
  have hmodl : esize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1 := by
    rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936:
        Nat) = 2 ^ 256 from rfl,hmod]
    rfl
  have hmodif : (if 1 = esize % 2 ^ 256 then UInt256.ofNat 1 else UInt256.ofNat 0) =
      UInt256.ofNat 1 := by
    rw [if_pos (by rw [hmod]; simp)]
  have he1 : UInt256.eq (UInt256.ofNat esize) (UInt256.ofNat 1) =
      UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [if_pos hmod]
  have hb3tne : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat) ≠
      UInt256.ofNat 3 := hbyteNe
  have hb3mne : UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).val.val) ≠
      UInt256.ofNat 3 := hbyteNe
  have hthree256 : (3 : Nat) % 2 ^ 256 = 3 := Nat.mod_eq_of_lt (by norm_num)
  have hbnT : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).toNat)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,hthree256]
    exact h.symm
  have hbn : ¬ (3 = (UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).val.val)).toNat) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,hthree256]
    exact h.symm
  have hbn2 : ¬ (3 = ((UInt256.byteAt ⟨(0 : Fin UInt256.size)⟩
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord mem 2656).val.val)).val).val) := by
    intro h
    apply hbyteNe
    refine Challenge.EvmProof.Word.word_ext ?_
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,hthree256]
    exact h.symm
  have hv4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2901 := by decide
  have hv8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 3017 -
      (UInt256.ofNat 29 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2785 := by decide
  have hw4 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 4).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 10692 := by decide
  have hw8 : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + 18724 -
      (UInt256.ofNat 2008 * UInt256.ofNat 8).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2660 := by decide
  have hslot1698 : ∀ (v a : Nat),a + 32 ≤ 1698 →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hhi1698 : ∀ (v a : Nat),1698 + 32 ≤ a →
      MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 1698) a =
        MachineState.readWord mem a := by
    intro v a ha
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ a 1698
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
  have hinitial : initialPhase s mem esize = UInt256.ofNat 0 := by
    have hb : UInt256.eq (UInt256.ofNat 3)
        (UInt256.byteAt (UInt256.ofNat 0)
          (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat)) = UInt256.ofNat 0 := by
      unfold UInt256.eq
      apply if_neg
      intro h
      exact hbyteNe (Challenge.EvmProof.Word.word_ext h.symm)
    unfold initialPhase
    rw [hb]
    simp [UInt256.land,UInt256.ofNat,UInt256.size,Fin.ofNat,Fin.land,Nat.zero_and]
  rcases hfast with h | h <;> subst h
  all_goals by_cases hshift : (MachineState.readWord mem 1536).toNat = 0
  all_goals simp (config := { maxSteps := 3000000 })
    [cacheBlock,blkCacheChoose,blkCacheNormal,blkCacheZero,hshift,opAt,pushAt,wfOp,he1,hb3tne,hb3mne,hbnT,hbn,hbn2,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      cacheSetupState,initialContinuation,hinitial,slotState,slotKState,shiftLoopState,rideSlots,entrySlots,aprevSlot,hdSlot,shiftEntry,Exp.storeWord,outer,Exp.outer,hcode,hrun,CycleSubmission.Global.ZeroShiftMath.shr_zero,headWord,loopPC,
      CycleSubmission.Global.ZeroShiftMath.head,CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,UInt256.isZero,
      CycleSubmission.Global.ZeroShiftMath.branch_normal4,CycleSubmission.Global.ZeroShiftMath.branch_normal8,
      CycleSubmission.Global.ZeroShiftMath.branch_zero4,CycleSubmission.Global.ZeroShiftMath.branch_zero8,
      jumpDestCacheNormal,jumpDestLoop2684,jumpDestLoop10692,jumpDestLoop3711,jumpDestLoop3879,
      UInt256.eq,UInt256.isTrue,
      haw1698,haw2816,haw32,hv4,hv8,hw4,hw8,hslot1698,hhi1698,hmodif,hmodl,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,Nat.mod_eq_of_lt,List.exchange]
  all_goals (try simp only [State.activeWordsAfterUInt256,haw1698,haw2816,haw32,
      hslot1698,hhi1698,hv4,hv8,hw4,hw8,hmodif,hmodl,hbn,hbn2,
      Fin.land,Nat.and_zero,Nat.zero_and])
  all_goals (first | rfl | simp [UInt256.ofNat,UInt256.size,Fin.ofNat,Fin.land,
      Nat.and_zero,Nat.zero_and,UInt256.toNat,hmodif,hmodl,hbn,hbn2,
      hb3mne])
  all_goals (first | rfl | decide)
end CycleSubmission.Global.Fast.Shift
