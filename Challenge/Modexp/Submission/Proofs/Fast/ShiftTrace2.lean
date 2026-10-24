import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace1

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Block reductions of the shift-reduce base conversion, part 2

The shift loop: `u` construction, the quotient estimate, the limb pass, the
middle block, the repair rounds, the `CSUB` call and the exits.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

@[simp] private theorem followupPC2764 : Artifact.submissionArtifact.instructionPC 2331 = 2983 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2765 : Artifact.submissionArtifact.instructionPC 2332 = 2984 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2325 = 2975 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2326 = 2976 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2327 = 2977 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl


@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2333 = 2985 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2334 = 2986 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2334 = 2986 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2334 = 2986 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl



@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2337 = 2991 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2338 = 2992 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2339 = 2993 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2340 = 2994 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2341 = 2995 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2342 = 2996 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2343 = 2997 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2344 = 2998 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2345 = 3001 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2346 = 3002 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2347 = 3003 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2348 = 3004 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2349 = 3005 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2350 = 3006 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2351 = 3007 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2352 = 3008 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2353 = 3009 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2354 = 3010 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2355 = 3011 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2356 = 3012 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2357 = 3013 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2358 = 3014 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2359 = 3015 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2360 = 3016 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2361 = 3019 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2362 = 3020 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2363 = 3021 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2364 = 3022 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2365 = 3023 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2366 = 3026 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2367 = 3027 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2368 = 3028 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_shiftHead_go (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState z s mem n bsize esize msize k) =
      some (shiftBodyState z s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcShiftLoop, pcShiftBody,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

theorem run_shiftBody (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hbs : bsize = 32 * n)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState z s mem n bsize esize msize k) =
      some (estimateState z s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 2080 (32 * n)) 2112
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 2080 (32 * n) 2112 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2784 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2080 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080) 2784 =
      UInt256.ofNat (2080 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32 * n)) 2080 =
      Exp.mcopyMem mem 2080 2112 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 2080 2112 (32 * n) 2784 (Or.inr (by omega))]
    exact htl
  have hmodTL : (2080 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 2080 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hbsz : (UInt256.ofNat bsize).toNat = 32 * n := by
    rw [hbs, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact hmod
  have hbsw : UInt256.ofNat bsize = UInt256.ofNat (32 * n) := by
    rw [hbs]
  have huv (a : Nat) (ha : a + 32 ≤ 2080) :
      MachineState.readWord (uMem mem n) a = MachineState.readWord mem a :=
    Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcShiftBody, pcEstimate,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, hbsz, hbsw, hu1312, hu1344, hu1376, hu1408, hu1440,
      hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals rfl


private theorem ofNat_zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) :=
  Monpro.zero_lt_eq_double_isZero x

private theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  simp only [UInt256.addMod, Nat.add_comm]

private theorem estimate_notZero_maxWord : UInt256.lnot (⟨0⟩ : UInt256) = Monpro.maxWord := by decide

private theorem estimate_notZeroOfNat_maxWord : UInt256.lnot (UInt256.ofNat 0) = Monpro.maxWord := by
  decide

private theorem saturation_gt_eq_lt (a b : UInt256) : a.gt b = b.lt a := by
  unfold UInt256.gt UInt256.lt
  split <;> [skip; skip] <;> simp_all
@[simp] private theorem newEstimatePC2960 : Artifact.submissionArtifact.instructionPC 2108 = 2727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2961 : Artifact.submissionArtifact.instructionPC 2109 = 2730 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2962 : Artifact.submissionArtifact.instructionPC 2110 = 2731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2963 : Artifact.submissionArtifact.instructionPC 2111 = 2732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2964 : Artifact.submissionArtifact.instructionPC 2112 = 2735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2965 : Artifact.submissionArtifact.instructionPC 2113 = 2736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2966 : Artifact.submissionArtifact.instructionPC 2114 = 2737 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2967 : Artifact.submissionArtifact.instructionPC 2115 = 2738 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2750 : Artifact.submissionArtifact.instructionPC 2116 = 2739 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2751 : Artifact.submissionArtifact.instructionPC 2117 = 2740 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2752 : Artifact.submissionArtifact.instructionPC 2118 = 2741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2753 : Artifact.submissionArtifact.instructionPC 2119 = 2742 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2754 : Artifact.submissionArtifact.instructionPC 2120 = 2743 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2755 : Artifact.submissionArtifact.instructionPC 2121 = 2744 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2756 : Artifact.submissionArtifact.instructionPC 2122 = 2745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2757 : Artifact.submissionArtifact.instructionPC 2123 = 2746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2758 : Artifact.submissionArtifact.instructionPC 2124 = 2747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2284 : Artifact.submissionArtifact.instructionPC 2091 = 2702 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2285 : Artifact.submissionArtifact.instructionPC 2092 = 2703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2286 : Artifact.submissionArtifact.instructionPC 2093 = 2704 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2333 : Artifact.submissionArtifact.instructionPC 2327 = 2977 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2334 : Artifact.submissionArtifact.instructionPC 2328 = 2978 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2335 : Artifact.submissionArtifact.instructionPC 2329 = 2979 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2336 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2279 : Artifact.submissionArtifact.instructionPC 2086 = 2693 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2280 : Artifact.submissionArtifact.instructionPC 2087 = 2694 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2281 : Artifact.submissionArtifact.instructionPC 2088 = 2697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2282 : Artifact.submissionArtifact.instructionPC 2089 = 2698 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2283 : Artifact.submissionArtifact.instructionPC 2090 = 2699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2284 : Artifact.submissionArtifact.instructionPC 2091 = 2702 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2285 : Artifact.submissionArtifact.instructionPC 2092 = 2703 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2286 : Artifact.submissionArtifact.instructionPC 2093 = 2704 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2291 : Artifact.submissionArtifact.instructionPC 2094 = 2705 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2292 : Artifact.submissionArtifact.instructionPC 2095 = 2706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2293 : Artifact.submissionArtifact.instructionPC 2096 = 2709 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2294 : Artifact.submissionArtifact.instructionPC 2097 = 2712 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2295 : Artifact.submissionArtifact.instructionPC 2098 = 2713 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2296 : Artifact.submissionArtifact.instructionPC 2099 = 2714 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2297 : Artifact.submissionArtifact.instructionPC 2100 = 2717 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2298 : Artifact.submissionArtifact.instructionPC 2101 = 2718 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2299 : Artifact.submissionArtifact.instructionPC 2102 = 2719 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2300 : Artifact.submissionArtifact.instructionPC 2103 = 2722 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2301 : Artifact.submissionArtifact.instructionPC 2104 = 2723 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2302 : Artifact.submissionArtifact.instructionPC 2105 = 2724 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2303 : Artifact.submissionArtifact.instructionPC 2106 = 2725 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2304 : Artifact.submissionArtifact.instructionPC 2107 = 2726 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2305 : Artifact.submissionArtifact.instructionPC 2108 = 2727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2306 : Artifact.submissionArtifact.instructionPC 2109 = 2730 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2307 : Artifact.submissionArtifact.instructionPC 2110 = 2731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2308 : Artifact.submissionArtifact.instructionPC 2111 = 2732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2309 : Artifact.submissionArtifact.instructionPC 2112 = 2735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2310 : Artifact.submissionArtifact.instructionPC 2113 = 2736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2311 : Artifact.submissionArtifact.instructionPC 2114 = 2737 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2312 : Artifact.submissionArtifact.instructionPC 2115 = 2738 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2313 : Artifact.submissionArtifact.instructionPC 2116 = 2739 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2314 : Artifact.submissionArtifact.instructionPC 2117 = 2740 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2315 : Artifact.submissionArtifact.instructionPC 2118 = 2741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2316 : Artifact.submissionArtifact.instructionPC 2119 = 2742 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2317 : Artifact.submissionArtifact.instructionPC 2120 = 2743 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2318 : Artifact.submissionArtifact.instructionPC 2121 = 2744 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2319 : Artifact.submissionArtifact.instructionPC 2122 = 2745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2320 : Artifact.submissionArtifact.instructionPC 2123 = 2746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2321 : Artifact.submissionArtifact.instructionPC 2124 = 2747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2322 : Artifact.submissionArtifact.instructionPC 2125 = 2748 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2323 : Artifact.submissionArtifact.instructionPC 2126 = 2749 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2324 : Artifact.submissionArtifact.instructionPC 2127 = 2750 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2325 : Artifact.submissionArtifact.instructionPC 2128 = 2751 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2326 : Artifact.submissionArtifact.instructionPC 2129 = 2752 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2327 : Artifact.submissionArtifact.instructionPC 2130 = 2753 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2328 : Artifact.submissionArtifact.instructionPC 2322 = 2972 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2329 : Artifact.submissionArtifact.instructionPC 2323 = 2973 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2330 : Artifact.submissionArtifact.instructionPC 2324 = 2974 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2331 : Artifact.submissionArtifact.instructionPC 2325 = 2975 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2332 : Artifact.submissionArtifact.instructionPC 2326 = 2976 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2333 : Artifact.submissionArtifact.instructionPC 2327 = 2977 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2334 : Artifact.submissionArtifact.instructionPC 2328 = 2978 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2335 : Artifact.submissionArtifact.instructionPC 2329 = 2979 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2336 : Artifact.submissionArtifact.instructionPC 2330 = 2980 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2337 : Artifact.submissionArtifact.instructionPC 2331 = 2983 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_estimate (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1536 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2112 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hE : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1568 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hF : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1632 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hG : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1664 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hI : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk3026, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, slotKState, rideSlots, entrySlots, shiftEntry,
      pcEstimate, pcMacSetup, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hB, hC, hD, hE, hF, hG, hH, hI, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm, saturation_gt_eq_lt,
      estimate_notZero_maxWord, estimate_notZeroOfNat_maxWord]




end Challenge.Modexp.Submission.Proofs.Fast.Shift
