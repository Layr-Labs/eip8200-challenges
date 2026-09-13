import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell2
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
private theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide
attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2337 = 3143 := by rfl
@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2338 = 3145 := by rfl
@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2339 = 3146 := by rfl
@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2340 = 3149 := by rfl
@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2340 = 3149 := by rfl
@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2340 = 3149 := by rfl
@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2340 = 3149 := by rfl
@[simp] private theorem compactLoopPC2756 : Artifact.submissionArtifact.instructionPC 2343 = 3152 := by rfl
@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2422 = 3237 := by rfl
@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2423 = 3240 := by rfl
@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2423 = 3240 := by rfl
@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2423 = 3240 := by rfl
@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2424 = 3241 := by rfl
@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2425 = 3242 := by rfl
@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2426 = 3243 := by rfl
@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2427 = 3244 := by rfl
@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2428 = 3245 := by rfl
@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2429 = 3246 := by rfl
@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2430 = 3247 := by rfl
@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2431 = 3248 := by rfl
@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2432 = 3249 := by rfl
@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2433 = 3250 := by rfl
@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2434 = 3251 := by rfl
@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2435 = 3252 := by rfl
@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2436 = 3253 := by rfl
@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2437 = 3254 := by rfl
@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2438 = 3255 := by rfl
@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2439 = 3256 := by rfl
@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2440 = 3257 := by rfl
@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2441 = 3258 := by rfl
@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2442 = 3259 := by rfl
@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2443 = 3260 := by rfl
@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2444 = 3261 := by rfl
@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2445 = 3262 := by rfl
@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2446 = 3263 := by rfl
@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2447 = 3264 := by rfl
@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2448 = 3265 := by rfl
@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2449 = 3266 := by rfl
@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2450 = 3267 := by rfl
@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2451 = 3268 := by rfl
@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2452 = 3269 := by rfl
@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2453 = 3270 := by rfl
@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2454 = 3271 := by rfl
@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2455 = 3272 := by rfl
@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2456 = 3273 := by rfl
@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2457 = 3274 := by rfl
@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2496 = 3317 := by rfl
@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2497 = 3318 := by rfl
@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2498 = 3319 := by rfl
@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2499 = 3322 := by rfl
@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2502 = 3325 := by rfl

def cellPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2421 .JUMPDEST,
   pushAt 2422 2 832,
   opAt 2423 (.Dup ⟨1, by decide⟩),
   opAt 2424 .SUB,
   opAt 2425 .MLOAD,
   opAt 2426 (.Dup ⟨2, by decide⟩),
   opAt 2427 (.Dup ⟨6, by decide⟩),
   opAt 2428 (.Dup ⟨2, by decide⟩),
   opAt 2429 .MUL,
   opAt 2430 (.Swap ⟨1, by decide⟩),
   opAt 2431 (.Dup ⟨7, by decide⟩),
   opAt 2432 .MULMOD,
   opAt 2433 (.Dup ⟨1, by decide⟩),
   opAt 2434 (.Dup ⟨1, by decide⟩),
   opAt 2435 .LT,
   opAt 2436 .SUB,
   opAt 2437 (.Dup ⟨5, by decide⟩),
   opAt 2438 (.Dup ⟨2, by decide⟩),
   opAt 2439 .ADD,
   opAt 2440 (.Dup ⟨0, by decide⟩),
   opAt 2441 (.Swap ⟨6, by decide⟩),
   opAt 2442 .GT,
   opAt 2443 .SUB,
   opAt 2444 .SUB,
   opAt 2445 (.Dup ⟨4, by decide⟩),
   opAt 2446 (.Dup ⟨2, by decide⟩),
   opAt 2447 .MLOAD,
   opAt 2448 .ADD,
   opAt 2449 (.Dup ⟨0, by decide⟩),
   opAt 2450 (.Swap ⟨5, by decide⟩),
   opAt 2451 .GT,
   opAt 2452 .ADD,
   opAt 2453 (.Swap ⟨3, by decide⟩),
   opAt 2454 (.Dup ⟨1, by decide⟩),
   opAt 2455 .MSTORE,
   opAt 2456 (.Dup ⟨2, by decide⟩),
   opAt 2457 .ADD]

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2421 = 3236 := by rfl

theorem run_cell2 (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 2112 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock cellPath
      { s with pc := UInt256.ofNat 3236
               stack := pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3275
                    stack := pt' :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n (j + 1)).carry :: q ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (Monpro.l1Step um q NEG n (j + 1)).memory } := by
  have hderived : pt - UInt256.ofNat 832 = pa := by
    conv_lhs => rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat pt]
    have hbound : pt.toNat < 2 ^ 256 := pt.val.isLt
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (a := pt.toNat) (b := 832)
      (by omega) hbound, Challenge.EvmProof.Word.word_eq_ofNat_toNat pa, hpt, hpa]
    congr 1
    unfold NEG
    omega
  have hderivedNat :
      (115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) -
        (832 : UInt256).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        NEG + 32 * (n - 1 - j) := by
    change (2 ^ 256 + (2112 + 32 * (n - 1 - j)) - (832 : UInt256).toNat) % 2 ^ 256 = _
    rw [← hpt, ← hpa, ← Challenge.EvmProof.Word.word_toNat_sub]
    exact congrArg UInt256.toNat (show pt - (832 : UInt256) = pa from hderived)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (NEG + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by unfold NEG; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cellPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacLoop, Monpro.l1Step, Monpro.macSum, Monpro.macCarry, Monpro.mulHi,
      Monpro.maxWord_literal, outer, Exp.outer,
      hrun, hcode, negK_literal, hderived, hderivedNat, hpa, hpt, hpa', hpt', hactA, hactT,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  first
  | rfl
  | exact ⟨by rw [Monpro.MacAlt.macSumNat], Monpro.MacAlt.macCarryFix _ _ _ _⟩


#print axioms run_cell2
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCell2
