import Challenge.Ripemd160.Submission.H39Memo.DispatchPaths
import Challenge.Ripemd160.Submission.H39Memo.Logic
import Challenge.Ripemd160.Submission.H39Memo.Step
import Challenge.Ripemd160.Submission.H39Memo.TerminalPaths
import Challenge.Ripemd160.Submission.H39Memo.TerminalPathsSites

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.DispatchTrace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

abbrev Artifact :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceArtifact

theorem isTrue_iff_ne_zero (w : UInt256) : UInt256.isTrue w ↔ w ≠ 0 := by
  constructor
  · intro ht he
    apply ht
    rw [he]
    rfl
  · intro hn ht
    apply hn
    apply Challenge.EvmProof.Word.word_ext
    exact ht

theorem xor_isTrue_iff_ne (a b : UInt256) :
    UInt256.isTrue (UInt256.xor a b) ↔ a ≠ b := by
  simp only [isTrue_iff_ne_zero, ne_eq, Logic.wordXor_eq_zero_iff]

theorem eq_isTrue_iff (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.isTrue (UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b)) ↔ a = b := by
  unfold UInt256.eq
  rw [Logic.toNat_ofNat_self ha, Logic.toNat_ofNat_self hb]
  by_cases h : a = b
  · rw [if_pos h]
    exact iff_of_true (by decide) h
  · rw [if_neg h]
    exact iff_of_false (by decide) h

theorem run_initial_to_guard (s : State)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.initialPath s =
      some (DispatchState.guardEntry s) := by
  have hpc0 : Artifact.referenceArtifact.instructionPC 0 = 0 := by decide
  have hpc1 : Artifact.referenceArtifact.instructionPC 1 = 3 := by decide
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 1671 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 831 (by rfl)
    simpa [hpc831] using h
  simp [DispatchPaths.initialPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.guardEntry, DispatchState.guardPC, DispatchState.atPC,
    hpc, hstack, hrun, hdest, hpc0, hpc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_fallback_jumpdest (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock DispatchPaths.fallbackJumpDestPath
      (DispatchState.fallbackJumpDestEntry s) =
      some (DispatchState.fallbackEntry s) := by
  have hpc682 : Artifact.referenceArtifact.instructionPC 682 = 1006 := by decide
  simp [DispatchPaths.fallbackJumpDestPath, DispatchPaths.opAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.fallbackJumpDestEntry, DispatchState.fallbackEntry,
    DispatchState.atPC, DispatchState.fallbackPC,
    DispatchState.fallbackAfterJumpPC, hrun, hpc682,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_empty_head (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock DispatchPaths.emptyHeadPath
      (DispatchState.emptyEntry s) =
      some (DispatchState.outputEntry s 3266) := by
  have hpc1158 : Artifact.referenceArtifact.instructionPC 1158 = 3264 := by decide
  have hpc1159 : Artifact.referenceArtifact.instructionPC 1159 = 3265 := by decide
  simp [DispatchPaths.emptyHeadPath, DispatchPaths.opAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.emptyEntry, DispatchState.outputEntry,
    DispatchState.afterSizeCheck, DispatchState.emptyPC,
    DispatchState.outputEntry, DispatchState.atPC, hrun,
    hpc1158, hpc1159,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_guard_empty (s : State)
    (hsize : s.executionEnv.calldata.size = 0)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.guardPath
      (DispatchState.guardEntry s) =
      some (DispatchState.emptyEntry s) := by
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hpc832 : Artifact.referenceArtifact.instructionPC 832 = 1672 := by decide
  have hpc833 : Artifact.referenceArtifact.instructionPC 833 = 1673 := by decide
  have hpc834 : Artifact.referenceArtifact.instructionPC 834 = 1674 := by decide
  have hpc835 : Artifact.referenceArtifact.instructionPC 835 = 1675 := by decide
  have hpc836 : Artifact.referenceArtifact.instructionPC 836 = 1678 := by decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 3264 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 1158 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 1158 = 3264 := by decide
    simpa [hpc] using h
  simp [DispatchPaths.guardPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.guardEntry, DispatchState.emptyEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.guardPC,
    DispatchState.emptyPC,
    hsize, hrun, hdest, hpc831, hpc832, hpc833, hpc834, hpc835, hpc836,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero,
    UInt256.eq]

theorem run_guard_abc (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.guardAbcPath
      (DispatchState.guardEntry s) =
      some (DispatchState.abcEntry s) := by
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hpc832 : Artifact.referenceArtifact.instructionPC 832 = 1672 := by decide
  have hpc833 : Artifact.referenceArtifact.instructionPC 833 = 1673 := by decide
  have hpc834 : Artifact.referenceArtifact.instructionPC 834 = 1674 := by decide
  have hpc835 : Artifact.referenceArtifact.instructionPC 835 = 1675 := by decide
  have hpc836 : Artifact.referenceArtifact.instructionPC 836 = 1678 := by decide
  have hpc837 : Artifact.referenceArtifact.instructionPC 837 = 1679 := by decide
  have hpc838 : Artifact.referenceArtifact.instructionPC 838 = 1680 := by decide
  have hpc839 : Artifact.referenceArtifact.instructionPC 839 = 1682 := by decide
  have hpc840 : Artifact.referenceArtifact.instructionPC 840 = 1683 := by decide
  have hpc841 : Artifact.referenceArtifact.instructionPC 841 = 1686 := by decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 3293 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 1166 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 1166 = 3293 := by decide
    simpa [hpc] using h
  simp [DispatchPaths.guardAbcPath, DispatchPaths.guardPath,
    DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.guardEntry, DispatchState.abcEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.guardPC,
    DispatchState.abcPC,
    hsize, hrun, hdest,
    hpc831, hpc832, hpc833, hpc834, hpc835, hpc836, hpc837, hpc838, hpc839,
    hpc840, hpc841, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero,
    UInt256.eq]

theorem run_guard_pattern1 (s : State)
    (hsize : s.executionEnv.calldata.size = 1)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.guardToPattern1Path
      (DispatchState.guardEntry s) =
      some (DispatchState.patternEntry s 3362 1) := by
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hpc832 : Artifact.referenceArtifact.instructionPC 832 = 1672 := by decide
  have hpc833 : Artifact.referenceArtifact.instructionPC 833 = 1673 := by decide
  have hpc834 : Artifact.referenceArtifact.instructionPC 834 = 1674 := by decide
  have hpc835 : Artifact.referenceArtifact.instructionPC 835 = 1675 := by decide
  have hpc836 : Artifact.referenceArtifact.instructionPC 836 = 1678 := by decide
  have hpc837 : Artifact.referenceArtifact.instructionPC 837 = 1679 := by decide
  have hpc838 : Artifact.referenceArtifact.instructionPC 838 = 1680 := by decide
  have hpc839 : Artifact.referenceArtifact.instructionPC 839 = 1682 := by decide
  have hpc840 : Artifact.referenceArtifact.instructionPC 840 = 1683 := by decide
  have hpc841 : Artifact.referenceArtifact.instructionPC 841 = 1686 := by decide
  have hpc842 : Artifact.referenceArtifact.instructionPC 842 = 1687 := by decide
  have hpc843 : Artifact.referenceArtifact.instructionPC 843 = 1688 := by decide
  have hpc844 : Artifact.referenceArtifact.instructionPC 844 = 1691 := by decide
  have hpc845 : Artifact.referenceArtifact.instructionPC 845 = 1692 := by decide
  have hpc846 : Artifact.referenceArtifact.instructionPC 846 = 1695 := by decide
  have hpc847 : Artifact.referenceArtifact.instructionPC 847 = 1696 := by decide
  have hpc848 : Artifact.referenceArtifact.instructionPC 848 = 1697 := by decide
  have hpc849 : Artifact.referenceArtifact.instructionPC 849 = 1698 := by decide
  have hpc850 : Artifact.referenceArtifact.instructionPC 850 = 1700 := by decide
  have hpc851 : Artifact.referenceArtifact.instructionPC 851 = 1701 := by decide
  have hpc852 : Artifact.referenceArtifact.instructionPC 852 = 1704 := by decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 3362 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 1180 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 1180 = 3362 := by decide
    simpa [hpc] using h
  simp [DispatchPaths.guardToPattern1Path, DispatchPaths.guardAbcPath,
    DispatchPaths.guardPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.guardEntry, DispatchState.patternEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.guardPC,
    hsize, hrun, hdest,
    hpc831, hpc832, hpc833, hpc834, hpc835, hpc836, hpc837, hpc838, hpc839,
    hpc840, hpc841, hpc842, hpc843, hpc844, hpc845, hpc846, hpc847, hpc848,
    hpc849, hpc850, hpc851, hpc852,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero,
    UInt256.eq]

theorem run_guard_a1000 (s : State)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.guardToA1000Path
      (DispatchState.guardEntry s) =
      some (DispatchState.patternEntry s 3115 1000) := by
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hpc832 : Artifact.referenceArtifact.instructionPC 832 = 1672 := by decide
  have hpc833 : Artifact.referenceArtifact.instructionPC 833 = 1673 := by decide
  have hpc834 : Artifact.referenceArtifact.instructionPC 834 = 1674 := by decide
  have hpc835 : Artifact.referenceArtifact.instructionPC 835 = 1675 := by decide
  have hpc836 : Artifact.referenceArtifact.instructionPC 836 = 1678 := by decide
  have hpc837 : Artifact.referenceArtifact.instructionPC 837 = 1679 := by decide
  have hpc838 : Artifact.referenceArtifact.instructionPC 838 = 1680 := by decide
  have hpc839 : Artifact.referenceArtifact.instructionPC 839 = 1682 := by decide
  have hpc840 : Artifact.referenceArtifact.instructionPC 840 = 1683 := by decide
  have hpc841 : Artifact.referenceArtifact.instructionPC 841 = 1686 := by decide
  have hpc842 : Artifact.referenceArtifact.instructionPC 842 = 1687 := by decide
  have hpc843 : Artifact.referenceArtifact.instructionPC 843 = 1688 := by decide
  have hpc844 : Artifact.referenceArtifact.instructionPC 844 = 1691 := by decide
  have hpc845 : Artifact.referenceArtifact.instructionPC 845 = 1692 := by decide
  have hpc846 : Artifact.referenceArtifact.instructionPC 846 = 1695 := by decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 3115 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 1110 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 1110 = 3115 := by decide
    simpa [hpc] using h
  simp [DispatchPaths.guardToA1000Path, DispatchPaths.guardAbcPath,
    DispatchPaths.guardPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.guardEntry, DispatchState.patternEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.guardPC,
    hsize, hrun, hdest, hpc831, hpc832, hpc833, hpc834, hpc835, hpc836,
    hpc837, hpc838, hpc839, hpc840, hpc841, hpc842, hpc843, hpc844, hpc845,
    hpc846, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero,
    UInt256.eq]

theorem run_guard_pattern_root (s : State)
    (hsize0 : s.executionEnv.calldata.size ≠ 0)
    (hsize3 : s.executionEnv.calldata.size ≠ 3)
    (hsize1000 : s.executionEnv.calldata.size ≠ 1000)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.guardToPatternRootPath
      (DispatchState.guardEntry s) =
      some (DispatchState.patternEntry s 1696 s.executionEnv.calldata.size) := by
  have hpc831 : Artifact.referenceArtifact.instructionPC 831 = 1671 := by decide
  have hpc832 : Artifact.referenceArtifact.instructionPC 832 = 1672 := by decide
  have hpc833 : Artifact.referenceArtifact.instructionPC 833 = 1673 := by decide
  have hpc834 : Artifact.referenceArtifact.instructionPC 834 = 1674 := by decide
  have hpc835 : Artifact.referenceArtifact.instructionPC 835 = 1675 := by decide
  have hpc836 : Artifact.referenceArtifact.instructionPC 836 = 1678 := by decide
  have hpc837 : Artifact.referenceArtifact.instructionPC 837 = 1679 := by decide
  have hpc838 : Artifact.referenceArtifact.instructionPC 838 = 1680 := by decide
  have hpc839 : Artifact.referenceArtifact.instructionPC 839 = 1682 := by decide
  have hpc840 : Artifact.referenceArtifact.instructionPC 840 = 1683 := by decide
  have hpc841 : Artifact.referenceArtifact.instructionPC 841 = 1686 := by decide
  have hpc842 : Artifact.referenceArtifact.instructionPC 842 = 1687 := by decide
  have hpc843 : Artifact.referenceArtifact.instructionPC 843 = 1688 := by decide
  have hpc844 : Artifact.referenceArtifact.instructionPC 844 = 1691 := by decide
  have hpc845 : Artifact.referenceArtifact.instructionPC 845 = 1692 := by decide
  have hpc846 : Artifact.referenceArtifact.instructionPC 846 = 1695 := by decide
  have hpc847 : Artifact.referenceArtifact.instructionPC 847 = 1696 := by decide
  have hzero : ¬ UInt256.isTrue
      (UInt256.isZero (UInt256.ofNat s.executionEnv.calldata.size)) := by
    rw [UInt256.isTrue]
    simp [UInt256.isZero, Logic.toNat_ofNat_self hfit, hsize0]
  have hzeroVal : UInt256.isZero
      (UInt256.ofNat s.executionEnv.calldata.size) = 0 := by
    rw [UInt256.isZero, Logic.toNat_ofNat_self hfit, if_neg hsize0]
    decide
  have hnot3 : ¬ UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 3)
        (UInt256.ofNat s.executionEnv.calldata.size)) := by
    rw [eq_isTrue_iff 3 s.executionEnv.calldata.size (by decide) hfit]
    exact Ne.symm hsize3
  have hnot1000 : ¬ UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 1000)
        (UInt256.ofNat s.executionEnv.calldata.size)) := by
    rw [eq_isTrue_iff 1000 s.executionEnv.calldata.size (by decide) hfit]
    exact Ne.symm hsize1000
  have hnot3mod : (3 : Nat) ≠
      s.executionEnv.calldata.size % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hfit]
    exact Ne.symm hsize3
  have hnot1000mod : (1000 : Nat) ≠
      s.executionEnv.calldata.size % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hfit]
    exact Ne.symm hsize1000
  have heq3zero : UInt256.eq (UInt256.ofNat 3)
      (UInt256.ofNat s.executionEnv.calldata.size) = 0 := by
    unfold UInt256.eq
    rw [Logic.toNat_ofNat_self (by decide),
      Logic.toNat_ofNat_self hfit, if_neg (Ne.symm hsize3)]
    decide
  have heq1000zero : UInt256.eq (UInt256.ofNat 1000)
      (UInt256.ofNat s.executionEnv.calldata.size) = 0 := by
    unfold UInt256.eq
    rw [Logic.toNat_ofNat_self (by decide),
      Logic.toNat_ofNat_self hfit, if_neg (Ne.symm hsize1000)]
    decide
  have hdest : Decode.isValidJumpDest s.executionEnv.code 1696 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 847 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 847 = 1696 := by decide
    simpa [hpc] using h
  simp [DispatchPaths.guardToPatternRootPath, DispatchPaths.guardToA1000Path,
    DispatchPaths.guardAbcPath, DispatchPaths.guardPath, DispatchPaths.opAt,
    DispatchPaths.pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, DispatchState.guardEntry, DispatchState.patternEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.guardPC,
    hrun, hzero, hzeroVal, hnot3, hnot1000, hnot3mod, hnot1000mod, hdest,
    hpc831, hpc832, hpc833, hpc834,
    hpc835, hpc836, hpc837, hpc838, hpc839, hpc840, hpc841, hpc842, hpc843,
    hpc844, hpc845, hpc846, hpc847, heq3zero, heq1000zero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue]

theorem run_abc_match (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 0 = DispatchPaths.abcWord)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock DispatchPaths.abcCheckPath
      (DispatchState.abcEntry s) =
      some (DispatchState.outputEntry s 3335) := by
  have hpc1166 : Artifact.referenceArtifact.instructionPC 1166 = 3293 := by decide
  have hpc1167 : Artifact.referenceArtifact.instructionPC 1167 = 3294 := by decide
  have hpc1168 : Artifact.referenceArtifact.instructionPC 1168 = 3295 := by decide
  have hpc1169 : Artifact.referenceArtifact.instructionPC 1169 = 3296 := by decide
  have hpc1170 : Artifact.referenceArtifact.instructionPC 1170 = 3297 := by decide
  have hpc1171 : Artifact.referenceArtifact.instructionPC 1171 = 3330 := by decide
  have hpc1172 : Artifact.referenceArtifact.instructionPC 1172 = 3331 := by decide
  have hpc1173 : Artifact.referenceArtifact.instructionPC 1173 = 3334 := by decide
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hxor : UInt256.xor DispatchPaths.abcWord DispatchPaths.abcWord = 0 :=
    (Logic.wordXor_eq_zero_iff _ _).2 rfl
  simp [DispatchPaths.abcCheckPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.abcEntry, DispatchState.outputEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.abcPC,
    hword, hrun, hpc1166, hpc1167, hpc1168, hpc1169, hpc1170, hpc1171,
    hpc1172, hpc1173, hzero, hxor, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_abc_miss (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 0 ≠ DispatchPaths.abcWord)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.abcCheckPath
      (DispatchState.abcEntry s) =
      some (DispatchState.fallbackJumpDestEntry s) := by
  have hpc1166 : Artifact.referenceArtifact.instructionPC 1166 = 3293 := by decide
  have hpc1167 : Artifact.referenceArtifact.instructionPC 1167 = 3294 := by decide
  have hpc1168 : Artifact.referenceArtifact.instructionPC 1168 = 3295 := by decide
  have hpc1169 : Artifact.referenceArtifact.instructionPC 1169 = 3296 := by decide
  have hpc1170 : Artifact.referenceArtifact.instructionPC 1170 = 3297 := by decide
  have hpc1171 : Artifact.referenceArtifact.instructionPC 1171 = 3330 := by decide
  have hpc1172 : Artifact.referenceArtifact.instructionPC 1172 = 3331 := by decide
  have hpc1173 : Artifact.referenceArtifact.instructionPC 1173 = 3334 := by decide
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hdest : Decode.isValidJumpDest s.executionEnv.code 1006 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 682 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 682 = 1006 := by decide
    simpa [hpc] using h
  have htrue : UInt256.isTrue
      (UInt256.xor DispatchPaths.abcWord
        (MachineState.readWord s.executionEnv.calldata 0)) := by
    rw [xor_isTrue_iff_ne]
    exact Ne.symm hword
  simp [DispatchPaths.abcCheckPath, DispatchPaths.opAt, DispatchPaths.pushAt,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    DispatchState.abcEntry, DispatchState.fallbackJumpDestEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, DispatchState.abcPC,
    DispatchState.fallbackPC, hword, htrue, hrun, hdest,
    hpc1166, hpc1167, hpc1168, hpc1169, hpc1170, hpc1171, hpc1172, hpc1173,
    hzero,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_pattern1000_match (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 =
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock DispatchPaths.pattern1000Path
      (DispatchState.patternEntry s 4107 1000) =
      some (DispatchState.outputEntry s 4151) := by
  have hpc1338 : Artifact.referenceArtifact.instructionPC 1338 = 4107 := by decide
  have hpc1339 : Artifact.referenceArtifact.instructionPC 1339 = 4108 := by decide
  have hpc1340 : Artifact.referenceArtifact.instructionPC 1340 = 4109 := by decide
  have hpc1341 : Artifact.referenceArtifact.instructionPC 1341 = 4112 := by decide
  have hpc1342 : Artifact.referenceArtifact.instructionPC 1342 = 4113 := by decide
  have hpc1343 : Artifact.referenceArtifact.instructionPC 1343 = 4146 := by decide
  have hpc1344 : Artifact.referenceArtifact.instructionPC 1344 = 4147 := by decide
  have hpc1345 : Artifact.referenceArtifact.instructionPC 1345 = 4150 := by decide
  have hoffset : (DispatchPaths.pushValue 1340).toNat = 992 := by decide
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hxor : UInt256.xor (DispatchPaths.pushValue 1342)
      (MachineState.readWord s.executionEnv.calldata 992) = 0 :=
    (Logic.wordXor_eq_zero_iff _ _).2 hword.symm
  have hxorSelf : UInt256.xor (DispatchPaths.pushValue 1342)
      (DispatchPaths.pushValue 1342) = 0 :=
    (Logic.wordXor_eq_zero_iff _ _).2 rfl
  simp [DispatchPaths.pattern1000Path, DispatchPaths.opAt,
    DispatchPaths.pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, DispatchState.patternEntry, DispatchState.outputEntry,
    DispatchState.afterSizeCheck, DispatchState.atPC, hrun, hpc1338, hpc1339,
    hpc1340, hpc1341, hpc1342, hpc1343, hpc1344, hpc1345, hoffset, hword,
    hzero, hxor, hxorSelf,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_pattern1000_miss (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 ≠
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock DispatchPaths.pattern1000Path
      (DispatchState.patternEntry s 4107 1000) =
      some (DispatchState.fallbackJumpDestEntry s) := by
  have hpc1338 : Artifact.referenceArtifact.instructionPC 1338 = 4107 := by decide
  have hpc1339 : Artifact.referenceArtifact.instructionPC 1339 = 4108 := by decide
  have hpc1340 : Artifact.referenceArtifact.instructionPC 1340 = 4109 := by decide
  have hpc1341 : Artifact.referenceArtifact.instructionPC 1341 = 4112 := by decide
  have hpc1342 : Artifact.referenceArtifact.instructionPC 1342 = 4113 := by decide
  have hpc1343 : Artifact.referenceArtifact.instructionPC 1343 = 4146 := by decide
  have hpc1344 : Artifact.referenceArtifact.instructionPC 1344 = 4147 := by decide
  have hpc1345 : Artifact.referenceArtifact.instructionPC 1345 = 4150 := by decide
  have hoffset : (DispatchPaths.pushValue 1340).toNat = 992 := by decide
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hdest : Decode.isValidJumpDest s.executionEnv.code 1006 = true := by
    rw [hcode]
    have h := Artifact.isValidJumpDest_index 682 (by rfl)
    have hpc : Artifact.referenceArtifact.instructionPC 682 = 1006 := by decide
    simpa [hpc] using h
  have htrue : UInt256.isTrue
      (UInt256.xor (DispatchPaths.pushValue 1342)
        (MachineState.readWord s.executionEnv.calldata 992)) := by
    rw [xor_isTrue_iff_ne]
    exact Ne.symm hword
  simp [DispatchPaths.pattern1000Path, DispatchPaths.opAt,
    DispatchPaths.pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, DispatchState.patternEntry,
    DispatchState.fallbackJumpDestEntry, DispatchState.afterSizeCheck,
    DispatchState.atPC, DispatchState.fallbackPC, hrun, hdest, hpc1338,
    hpc1339, hpc1340, hpc1341, hpc1342, hpc1343, hpc1344, hpc1345, hoffset, hword,
    hzero, htrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_initial_to_guard (s : State)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (DispatchState.guardEntry s) :=
  Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.initialPath
    hcode hfork (run_initial_to_guard s hpc hstack hrun hcode) hrun hnp

def gasSteps_fallback_jumpdest (s : State)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.fallbackJumpDestEntry s)
      (DispatchState.fallbackEntry s) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.fallbackJumpDestPath
  · simpa [DispatchState.fallbackJumpDestEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.fallbackJumpDestEntry, DispatchState.atPC] using hfork
  · exact run_fallback_jumpdest s hrun
  · simpa [DispatchState.fallbackJumpDestEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.fallbackJumpDestEntry, DispatchState.atPC] using hnp

def gasSteps_empty_head (s : State)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.emptyEntry s) (DispatchState.outputEntry s 3266) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.emptyHeadPath
  · simpa [DispatchState.emptyEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hcode
  · simpa [DispatchState.emptyEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hfork
  · exact run_empty_head s hrun
  · simpa [DispatchState.emptyEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun
  · simpa [DispatchState.emptyEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hnp

def gasSteps_guard_empty (s : State)
    (hsize : s.executionEnv.calldata.size = 0)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.guardEntry s) (DispatchState.emptyEntry s) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.guardPath
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hfork
  · exact run_guard_empty s hsize hrun hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hnp

def gasSteps_guard_abc (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.guardEntry s) (DispatchState.abcEntry s) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.guardAbcPath
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hfork
  · exact run_guard_abc s hsize hrun hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hnp

def gasSteps_guard_pattern1 (s : State)
    (hsize : s.executionEnv.calldata.size = 1)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.guardEntry s)
      (DispatchState.patternEntry s 3362 1) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.guardToPattern1Path
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hfork
  · exact run_guard_pattern1 s hsize hrun hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hnp

def gasSteps_guard_a1000 (s : State)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.guardEntry s)
      (DispatchState.patternEntry s 3115 1000) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.guardToA1000Path
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hfork
  · exact run_guard_a1000 s hsize hrun hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hnp

def gasSteps_guard_pattern_root (s : State)
    (hsize0 : s.executionEnv.calldata.size ≠ 0)
    (hsize3 : s.executionEnv.calldata.size ≠ 3)
    (hsize1000 : s.executionEnv.calldata.size ≠ 1000)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.guardEntry s)
      (DispatchState.patternEntry s 1696 s.executionEnv.calldata.size) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.guardToPatternRootPath
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hfork
  · exact run_guard_pattern_root s hsize0 hsize3 hsize1000 hfit hrun hcode
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hrun
  · simpa [DispatchState.guardEntry, DispatchState.atPC] using hnp

def gasSteps_pattern1000_match (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 =
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.patternEntry s 4107 1000)
      (DispatchState.outputEntry s 4151) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.pattern1000Path
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hcode
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hfork
  · exact run_pattern1000_match s hword hrun
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hnp

def gasSteps_pattern1000_miss (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 ≠
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.patternEntry s 4107 1000)
      (DispatchState.fallbackJumpDestEntry s) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka
    DispatchPaths.pattern1000Path
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hcode
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hfork
  · exact run_pattern1000_miss s hword hrun hcode
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun
  · simpa [DispatchState.patternEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hnp

def gasSteps_pattern1000_miss_to_fallback (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 ≠
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.patternEntry s 4107 1000)
      (DispatchState.fallbackEntry s) :=
  (gasSteps_pattern1000_miss s hword hrun hcode hfork hnp).trans
    (gasSteps_fallback_jumpdest s hrun hcode hfork hnp)

def gasSteps_abc_match (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 0 = DispatchPaths.abcWord)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.abcEntry s) (DispatchState.outputEntry s 3335) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.abcCheckPath
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hcode
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hfork
  · exact run_abc_match s hword hrun
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hnp

def gasSteps_abc_miss (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 0 ≠ DispatchPaths.abcWord)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.abcEntry s)
      (DispatchState.fallbackJumpDestEntry s) := by
  apply Stepper.runLocatedBlock_sound Artifact .Osaka DispatchPaths.abcCheckPath
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hcode
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hfork
  · exact run_abc_miss s hword hrun hcode
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun
  · simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hnp

theorem run_empty_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 0)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code) :
    Stepper.runLocatedBlock
        (DispatchPaths.initialPath ++ DispatchPaths.guardPath ++
          DispatchPaths.emptyHeadPath) s =
      some (DispatchState.outputEntry s 3266) := by
  have h₁ := run_initial_to_guard s hpc hstack hrun hcode
  have h₂ := run_guard_empty s hsize hrun hcode
  have h₃ := run_empty_head s hrun
  have h₂₃ := Stepper.runLocatedBlock_append
    DispatchPaths.guardPath DispatchPaths.emptyHeadPath
    (DispatchState.guardEntry s) (DispatchState.emptyEntry s)
    (DispatchState.outputEntry s 3266) h₂
    (by simpa [DispatchState.emptyEntry, DispatchState.afterSizeCheck] using hrun)
    h₃
  have h₁₂₃ := Stepper.runLocatedBlock_append
    DispatchPaths.initialPath
    (DispatchPaths.guardPath ++ DispatchPaths.emptyHeadPath)
    s (DispatchState.guardEntry s) (DispatchState.outputEntry s 3266)
    h₁ hrun h₂₃
  simpa [List.append_assoc] using h₁₂₃

def gasSteps_empty_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 0)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (DispatchState.outputEntry s 3266) :=
  (gasSteps_initial_to_guard s hpc hstack hrun hcode hfork hnp).trans
    ((gasSteps_guard_empty s hsize hrun hcode hfork hnp).trans
      (gasSteps_empty_head s hrun hcode hfork hnp))

theorem run_abc_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hword : MachineState.readWord s.executionEnv.calldata 0 =
      DispatchPaths.abcWord) :
    Stepper.runLocatedBlock
        (DispatchPaths.initialPath ++ DispatchPaths.guardAbcPath ++
          DispatchPaths.abcCheckPath) s =
      some (DispatchState.outputEntry s 3335) := by
  have h₁ := run_initial_to_guard s hpc hstack hrun hcode
  have h₂ := run_guard_abc s hsize hrun hcode
  have h₃ := run_abc_match s hword hrun
  have h₂₃ := Stepper.runLocatedBlock_append
    DispatchPaths.guardAbcPath DispatchPaths.abcCheckPath
    (DispatchState.guardEntry s) (DispatchState.abcEntry s)
    (DispatchState.outputEntry s 3335) h₂
    (by simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun)
    h₃
  have h₁₂₃ := Stepper.runLocatedBlock_append
    DispatchPaths.initialPath
    (DispatchPaths.guardAbcPath ++ DispatchPaths.abcCheckPath)
    s (DispatchState.guardEntry s) (DispatchState.outputEntry s 3335)
    h₁ hrun h₂₃
  simpa [List.append_assoc] using h₁₂₃

theorem run_abc_miss_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hword : MachineState.readWord s.executionEnv.calldata 0 ≠
      DispatchPaths.abcWord) :
    Stepper.runLocatedBlock
        (DispatchPaths.initialPath ++ DispatchPaths.guardAbcPath ++
          DispatchPaths.abcCheckPath ++
          DispatchPaths.fallbackJumpDestPath) s =
      some (DispatchState.fallbackEntry s) := by
  have h₁ := run_initial_to_guard s hpc hstack hrun hcode
  have h₂ := run_guard_abc s hsize hrun hcode
  have h₃ := run_abc_miss s hword hrun hcode
  have h₄ := run_fallback_jumpdest s hrun
  have h₂₃ := Stepper.runLocatedBlock_append
    DispatchPaths.guardAbcPath DispatchPaths.abcCheckPath
    (DispatchState.guardEntry s) (DispatchState.abcEntry s)
    (DispatchState.fallbackJumpDestEntry s) h₂
    (by simpa [DispatchState.abcEntry, DispatchState.afterSizeCheck,
      DispatchState.atPC] using hrun)
    h₃
  have h₂₃₄ := Stepper.runLocatedBlock_append
    (DispatchPaths.guardAbcPath ++ DispatchPaths.abcCheckPath)
    DispatchPaths.fallbackJumpDestPath
    (DispatchState.guardEntry s) (DispatchState.fallbackJumpDestEntry s)
    (DispatchState.fallbackEntry s) h₂₃
    (by simpa [DispatchState.fallbackJumpDestEntry, DispatchState.atPC]
      using hrun)
    h₄
  have h₁₂₃₄ := Stepper.runLocatedBlock_append
    DispatchPaths.initialPath
    (DispatchPaths.guardAbcPath ++ DispatchPaths.abcCheckPath ++
      DispatchPaths.fallbackJumpDestPath)
    s (DispatchState.guardEntry s) (DispatchState.fallbackEntry s)
    h₁ hrun h₂₃₄
  simpa [List.append_assoc] using h₁₂₃₄

def gasSteps_abc_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hword : MachineState.readWord s.executionEnv.calldata 0 =
      DispatchPaths.abcWord) :
    GasSteps s (DispatchState.outputEntry s 3335) :=
  (gasSteps_initial_to_guard s hpc hstack hrun hcode hfork hnp).trans
    ((gasSteps_guard_abc s hsize hrun hcode hfork hnp).trans
      (gasSteps_abc_match s hword hrun hcode hfork hnp))

def gasSteps_abc_miss_prefix (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hword : MachineState.readWord s.executionEnv.calldata 0 ≠
      DispatchPaths.abcWord) :
    GasSteps s (DispatchState.fallbackEntry s) :=
  (gasSteps_initial_to_guard s hpc hstack hrun hcode hfork hnp).trans
    ((gasSteps_guard_abc s hsize hrun hcode hfork hnp).trans
      ((gasSteps_abc_miss s hword hrun hcode hfork hnp).trans
        (gasSteps_fallback_jumpdest s hrun hcode hfork hnp)))

def gasSteps_to_return {s t : State} (hprefix : GasSteps s t)
    {pc : Nat} {digest : UInt256}
    (c : TerminalPaths.Certificate pc digest)
    (hpc : t.pc = UInt256.ofNat pc) (hstack : t.stack = [])
    (hrun : t.halt = .Running)
    (hcode : t.executionEnv.code = Artifact.code)
    (hfork : t.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig
      t.executionEnv.fork t.executionEnv.codeAddr = false) :
    GasSteps s (DispatchState.returned t (pc + 26) digest) :=
  hprefix.trans (TerminalPaths.gasSteps_output c t hpc hstack hrun
    hcode hfork hnp)

def gasSteps_empty_return (s : State)
    (hsize : s.executionEnv.calldata.size = 0)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s
      (DispatchState.returned (DispatchState.outputEntry s 3266)
        (3266 + 26) 0x9c1185a5c5e9fc54612808977ee8f548b2258d31) :=
  gasSteps_to_return
    (gasSteps_empty_prefix s hsize hpc hstack hrun hcode hfork hnp)
    TerminalPathsSites.certEmpty rfl rfl
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hrun)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hcode)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hfork)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hnp)

def gasSteps_abc_return (s : State)
    (hsize : s.executionEnv.calldata.size = 3)
    (hpc : s.pc = 0) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hword : MachineState.readWord s.executionEnv.calldata 0 =
      DispatchPaths.abcWord) :
    GasSteps s
      (DispatchState.returned (DispatchState.outputEntry s 3335)
        (3335 + 26) 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc) :=
  gasSteps_to_return
    (gasSteps_abc_prefix s hsize hpc hstack hrun hcode hfork hnp hword)
    TerminalPathsSites.certAbc rfl rfl
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hrun)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hcode)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hfork)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hnp)

def gasSteps_pattern1000_return (s : State)
    (hword : MachineState.readWord s.executionEnv.calldata 992 =
      DispatchPaths.pushValue 1342)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DispatchState.patternEntry s 4107 1000)
      (DispatchState.returned (DispatchState.outputEntry s 4151)
        (4151 + 26) 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4) :=
  gasSteps_to_return
    (gasSteps_pattern1000_match s hword hrun hcode hfork hnp)
    TerminalPathsSites.certP1000 rfl rfl
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hrun)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hcode)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hfork)
    (by simpa [DispatchState.outputEntry, DispatchState.atPC] using hnp)

end Challenge.Ripemd160.Submission.H39Memo.DispatchTrace
