import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell3
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
def cellPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2301 .JUMPDEST,
   pushAt 2302 2 832,
   opAt 2303 (.Dup ⟨1, by decide⟩),
   opAt 2304 .SUB,
   opAt 2305 .MLOAD,
   opAt 2306 (.Dup ⟨2, by decide⟩),
   opAt 2307 (.Dup ⟨6, by decide⟩),
   opAt 2308 (.Dup ⟨2, by decide⟩),
   opAt 2309 .MUL,
   opAt 2310 (.Swap ⟨1, by decide⟩),
   opAt 2311 (.Dup ⟨7, by decide⟩),
   opAt 2312 .MULMOD,
   opAt 2313 (.Dup ⟨1, by decide⟩),
   opAt 2314 (.Dup ⟨1, by decide⟩),
   opAt 2315 .LT,
   opAt 2316 .SUB,
   opAt 2317 (.Dup ⟨5, by decide⟩),
   opAt 2318 (.Dup ⟨2, by decide⟩),
   opAt 2319 .ADD,
   opAt 2320 (.Dup ⟨0, by decide⟩),
   opAt 2321 (.Swap ⟨6, by decide⟩),
   opAt 2322 .GT,
   opAt 2323 .SUB,
   opAt 2324 .SUB,
   opAt 2325 (.Dup ⟨4, by decide⟩),
   opAt 2326 (.Dup ⟨2, by decide⟩),
   opAt 2327 .MLOAD,
   opAt 2328 .ADD,
   opAt 2329 (.Dup ⟨0, by decide⟩),
   opAt 2330 (.Swap ⟨5, by decide⟩),
   opAt 2331 .GT,
   opAt 2332 .ADD,
   opAt 2333 (.Swap ⟨3, by decide⟩),
   opAt 2334 (.Dup ⟨1, by decide⟩),
   opAt 2335 .MSTORE,
   opAt 2336 (.Dup ⟨2, by decide⟩),
   opAt 2337 .ADD]

private theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide
attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2183 = 2940 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2184 = 2941 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2185 = 2942 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2188 = 2949 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2188 = 2949 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2188 = 2949 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2188 = 2949 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl


@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2302 = 3069 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2303 = 3072 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2303 = 3072 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2303 = 3072 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2304 = 3073 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2305 = 3074 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2306 = 3075 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2307 = 3076 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2308 = 3077 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2309 = 3078 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2310 = 3079 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2311 = 3080 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2312 = 3081 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2313 = 3082 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2314 = 3083 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2315 = 3084 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2316 = 3085 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2317 = 3086 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2318 = 3087 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2319 = 3088 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2320 = 3089 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2321 = 3090 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2322 = 3091 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2323 = 3092 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2324 = 3093 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2325 = 3094 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2326 = 3095 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2327 = 3096 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2328 = 3097 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2329 = 3098 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2330 = 3099 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2331 = 3100 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2332 = 3101 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2333 = 3102 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2334 = 3103 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2335 = 3104 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2336 = 3105 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2337 = 3106 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2339 = 3110 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2340 = 3111 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2341 = 3112 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2342 = 3115 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2345 = 3118 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2301 = 3068 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_cell3 (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 2112 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock cellPath
      { s with pc := UInt256.ofNat 3068
               stack := pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3107
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


#print axioms run_cell3
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCell3
