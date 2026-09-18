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

@[simp] private theorem followupPC2764 : Artifact.submissionArtifact.instructionPC 2464 = 3054 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2765 : Artifact.submissionArtifact.instructionPC 2465 = 3057 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2458 = 3048 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2459 = 3049 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2460 = 3050 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl


@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2466 = 3058 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2467 = 3059 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2467 = 3059 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2467 = 3059 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl



@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2470 = 3062 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2471 = 3063 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2472 = 3064 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2473 = 3065 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2474 = 3066 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2475 = 3067 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2476 = 3068 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2477 = 3069 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2478 = 3070 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2479 = 3071 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2480 = 3072 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2481 = 3075 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2482 = 3076 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2483 = 3077 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2484 = 3078 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2485 = 3079 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2486 = 3082 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2487 = 3083 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2488 = 3084 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2489 = 3085 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2490 = 3086 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2491 = 3087 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2492 = 3088 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2493 = 3089 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2494 = 3090 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2495 = 3091 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2496 = 3092 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2497 = 3093 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2498 = 3096 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2499 = 3097 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2500 = 3098 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2501 = 3099 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2611 = 3246 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2612 = 3247 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2613 = 3249 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2614 = 3250 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2617 = 3255 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_shiftHead_go (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize k) =
      some (shiftBodyState s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, kState, pcShiftLoop, pcShiftBody,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

/-- `blk3013` with no steps to go: jump to `SHIFT_DONE`. -/
theorem run_shiftHead_done (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize 0) =
      some (shiftDoneState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftDoneState, kState, pcShiftLoop, pcShiftDone,
      outer, Exp.outer, hcode, hrun, jumpDest5366, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3018`: `MCOPY(TN, TS, s32)` (the retained accumulator shifted up one limb) and `t[0] := 0`. -/
theorem run_shiftBody (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hact : 89 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState s mem n bsize esize msize k) =
      some (estimateState s mem n bsize esize msize k) := by
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
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, kState, pcShiftBody, pcEstimate, uMem,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- Generic word identity; the quotient clamp itself is unchanged. -/
private theorem saturation_gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := by
  rfl

private theorem ofNat_zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) :=
  Monpro.zero_lt_eq_double_isZero x

private theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  simp only [UInt256.addMod, Nat.add_comm]

@[simp] private theorem newEstimatePC2960 : Artifact.submissionArtifact.instructionPC 2224 = 2761 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2961 : Artifact.submissionArtifact.instructionPC 2225 = 2762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2962 : Artifact.submissionArtifact.instructionPC 2226 = 2765 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2963 : Artifact.submissionArtifact.instructionPC 2227 = 2766 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2964 : Artifact.submissionArtifact.instructionPC 2228 = 2767 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2965 : Artifact.submissionArtifact.instructionPC 2229 = 2769 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2966 : Artifact.submissionArtifact.instructionPC 2230 = 2770 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePC2967 : Artifact.submissionArtifact.instructionPC 2231 = 2772 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2750 : Artifact.submissionArtifact.instructionPC 2232 = 2773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2751 : Artifact.submissionArtifact.instructionPC 2233 = 2774 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2752 : Artifact.submissionArtifact.instructionPC 2234 = 2776 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2753 : Artifact.submissionArtifact.instructionPC 2235 = 2777 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2754 : Artifact.submissionArtifact.instructionPC 2236 = 2778 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2755 : Artifact.submissionArtifact.instructionPC 2237 = 2779 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2756 : Artifact.submissionArtifact.instructionPC 2238 = 2780 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2757 : Artifact.submissionArtifact.instructionPC 2239 = 2781 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem newEstimatePCk2758 : Artifact.submissionArtifact.instructionPC 2240 = 2782 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2284 : Artifact.submissionArtifact.instructionPC 2203 = 2732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2285 : Artifact.submissionArtifact.instructionPC 2204 = 2735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2286 : Artifact.submissionArtifact.instructionPC 2205 = 2736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2287 : Artifact.submissionArtifact.instructionPC 2206 = 2737 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2288 : Artifact.submissionArtifact.instructionPC 2207 = 2738 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2333 : Artifact.submissionArtifact.instructionPC 2460 = 3050 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2334 : Artifact.submissionArtifact.instructionPC 2461 = 3051 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2335 : Artifact.submissionArtifact.instructionPC 2462 = 3052 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem dagInstructionPC2336 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2279 : Artifact.submissionArtifact.instructionPC 2198 = 2723 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2280 : Artifact.submissionArtifact.instructionPC 2199 = 2726 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2281 : Artifact.submissionArtifact.instructionPC 2200 = 2727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2282 : Artifact.submissionArtifact.instructionPC 2201 = 2728 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2283 : Artifact.submissionArtifact.instructionPC 2202 = 2731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2284 : Artifact.submissionArtifact.instructionPC 2203 = 2732 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2285 : Artifact.submissionArtifact.instructionPC 2204 = 2735 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2286 : Artifact.submissionArtifact.instructionPC 2205 = 2736 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2287 : Artifact.submissionArtifact.instructionPC 2206 = 2737 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2288 : Artifact.submissionArtifact.instructionPC 2207 = 2738 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2289 : Artifact.submissionArtifact.instructionPC 2208 = 2741 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2290 : Artifact.submissionArtifact.instructionPC 2209 = 2742 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2291 : Artifact.submissionArtifact.instructionPC 2210 = 2743 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2292 : Artifact.submissionArtifact.instructionPC 2211 = 2746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2293 : Artifact.submissionArtifact.instructionPC 2212 = 2747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2294 : Artifact.submissionArtifact.instructionPC 2213 = 2748 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2295 : Artifact.submissionArtifact.instructionPC 2214 = 2749 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2296 : Artifact.submissionArtifact.instructionPC 2215 = 2750 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2297 : Artifact.submissionArtifact.instructionPC 2216 = 2751 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2298 : Artifact.submissionArtifact.instructionPC 2217 = 2752 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2299 : Artifact.submissionArtifact.instructionPC 2218 = 2753 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2300 : Artifact.submissionArtifact.instructionPC 2219 = 2756 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2301 : Artifact.submissionArtifact.instructionPC 2220 = 2757 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2302 : Artifact.submissionArtifact.instructionPC 2221 = 2758 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2303 : Artifact.submissionArtifact.instructionPC 2222 = 2759 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2304 : Artifact.submissionArtifact.instructionPC 2223 = 2760 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2305 : Artifact.submissionArtifact.instructionPC 2224 = 2761 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2306 : Artifact.submissionArtifact.instructionPC 2225 = 2762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2307 : Artifact.submissionArtifact.instructionPC 2226 = 2765 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2308 : Artifact.submissionArtifact.instructionPC 2227 = 2766 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2309 : Artifact.submissionArtifact.instructionPC 2228 = 2767 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2310 : Artifact.submissionArtifact.instructionPC 2229 = 2769 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2311 : Artifact.submissionArtifact.instructionPC 2230 = 2770 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2312 : Artifact.submissionArtifact.instructionPC 2231 = 2772 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2313 : Artifact.submissionArtifact.instructionPC 2232 = 2773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2314 : Artifact.submissionArtifact.instructionPC 2233 = 2774 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2315 : Artifact.submissionArtifact.instructionPC 2234 = 2776 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2316 : Artifact.submissionArtifact.instructionPC 2235 = 2777 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2317 : Artifact.submissionArtifact.instructionPC 2236 = 2778 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2318 : Artifact.submissionArtifact.instructionPC 2237 = 2779 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2319 : Artifact.submissionArtifact.instructionPC 2238 = 2780 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2320 : Artifact.submissionArtifact.instructionPC 2239 = 2781 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2321 : Artifact.submissionArtifact.instructionPC 2240 = 2782 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2322 : Artifact.submissionArtifact.instructionPC 2241 = 2785 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2323 : Artifact.submissionArtifact.instructionPC 2242 = 2786 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2324 : Artifact.submissionArtifact.instructionPC 2243 = 2787 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2325 : Artifact.submissionArtifact.instructionPC 2244 = 2788 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2326 : Artifact.submissionArtifact.instructionPC 2245 = 2789 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2327 : Artifact.submissionArtifact.instructionPC 2246 = 2790 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2328 : Artifact.submissionArtifact.instructionPC 2455 = 3043 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2329 : Artifact.submissionArtifact.instructionPC 2456 = 3046 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2330 : Artifact.submissionArtifact.instructionPC 2457 = 3047 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2331 : Artifact.submissionArtifact.instructionPC 2458 = 3048 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2332 : Artifact.submissionArtifact.instructionPC 2459 = 3049 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2333 : Artifact.submissionArtifact.instructionPC 2460 = 3050 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2334 : Artifact.submissionArtifact.instructionPC 2461 = 3051 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2335 : Artifact.submissionArtifact.instructionPC 2462 = 3052 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2336 : Artifact.submissionArtifact.instructionPC 2463 = 3053 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem nopMovePC2337 : Artifact.submissionArtifact.instructionPC 2464 = 3054 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_estimate (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState s mem n bsize esize msize k) =
      some (macSetupState s mem n bsize esize msize k) := by
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
      estimateState, macSetupState, kState, pcEstimate, pcMacSetup, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hB, hC, hD, hE, hF, hG, hH, hI, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, saturation_gt_eq_lt, addMod_comm]




end Challenge.Modexp.Submission.Proofs.Fast.Shift
