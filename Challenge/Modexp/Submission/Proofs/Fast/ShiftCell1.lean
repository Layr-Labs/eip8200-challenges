import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
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

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2317 = 3149 := by rfl
@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2318 = 3151 := by rfl
@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2319 = 3152 := by rfl
@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2320 = 3155 := by rfl
@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2320 = 3155 := by rfl
@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2320 = 3155 := by rfl
@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2320 = 3155 := by rfl
@[simp] private theorem compactLoopPC2756 : Artifact.submissionArtifact.instructionPC 2323 = 3158 := by rfl
@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2365 = 3204 := by rfl
@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2366 = 3207 := by rfl
@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2366 = 3207 := by rfl
@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2366 = 3207 := by rfl
@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2367 = 3208 := by rfl
@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2368 = 3209 := by rfl
@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2369 = 3210 := by rfl
@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2370 = 3211 := by rfl
@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2371 = 3212 := by rfl
@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2372 = 3213 := by rfl
@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2373 = 3214 := by rfl
@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2374 = 3215 := by rfl
@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2375 = 3216 := by rfl
@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2376 = 3217 := by rfl
@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2377 = 3218 := by rfl
@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2378 = 3219 := by rfl
@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2379 = 3220 := by rfl
@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2380 = 3221 := by rfl
@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2381 = 3222 := by rfl
@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2382 = 3223 := by rfl
@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2383 = 3224 := by rfl
@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2384 = 3225 := by rfl
@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2385 = 3226 := by rfl
@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2386 = 3227 := by rfl
@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2387 = 3228 := by rfl
@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2388 = 3229 := by rfl
@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2389 = 3230 := by rfl
@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2390 = 3231 := by rfl
@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2391 = 3232 := by rfl
@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2392 = 3233 := by rfl
@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2393 = 3234 := by rfl
@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2394 = 3235 := by rfl
@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2395 = 3236 := by rfl
@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2396 = 3237 := by rfl
@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2397 = 3238 := by rfl
@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2398 = 3239 := by rfl
@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2399 = 3240 := by rfl
@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2400 = 3241 := by rfl
@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2476 = 3323 := by rfl
@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2477 = 3324 := by rfl
@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2478 = 3325 := by rfl
@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2479 = 3328 := by rfl
@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2482 = 3331 := by rfl

def cellPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2364 .JUMPDEST,
   pushAt 2365 2 832,
   opAt 2366 (.Dup ⟨1, by decide⟩),
   opAt 2367 .SUB,
   opAt 2368 .MLOAD,
   opAt 2369 (.Dup ⟨2, by decide⟩),
   opAt 2370 (.Dup ⟨6, by decide⟩),
   opAt 2371 (.Dup ⟨2, by decide⟩),
   opAt 2372 .MUL,
   opAt 2373 (.Swap ⟨1, by decide⟩),
   opAt 2374 (.Dup ⟨7, by decide⟩),
   opAt 2375 .MULMOD,
   opAt 2376 (.Dup ⟨1, by decide⟩),
   opAt 2377 (.Dup ⟨1, by decide⟩),
   opAt 2378 .LT,
   opAt 2379 .SUB,
   opAt 2380 (.Dup ⟨5, by decide⟩),
   opAt 2381 (.Dup ⟨2, by decide⟩),
   opAt 2382 .ADD,
   opAt 2383 (.Dup ⟨0, by decide⟩),
   opAt 2384 (.Swap ⟨6, by decide⟩),
   opAt 2385 .GT,
   opAt 2386 .SUB,
   opAt 2387 .SUB,
   opAt 2388 (.Dup ⟨4, by decide⟩),
   opAt 2389 (.Dup ⟨2, by decide⟩),
   opAt 2390 .MLOAD,
   opAt 2391 .ADD,
   opAt 2392 (.Dup ⟨0, by decide⟩),
   opAt 2393 (.Swap ⟨5, by decide⟩),
   opAt 2394 .GT,
   opAt 2395 .ADD,
   opAt 2396 (.Swap ⟨3, by decide⟩),
   opAt 2397 (.Dup ⟨1, by decide⟩),
   opAt 2398 .MSTORE,
   opAt 2399 (.Dup ⟨2, by decide⟩),
   opAt 2400 .ADD]

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2364 = 3203 := by rfl

theorem run_cell1 (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 2112 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock cellPath
      { s with pc := UInt256.ofNat 3203
               stack := pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3242
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


#print axioms run_cell1
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
