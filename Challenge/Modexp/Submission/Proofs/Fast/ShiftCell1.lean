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

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
def cellPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2227 .JUMPDEST,
   pushAt 2228 2 832,
   opAt 2229 (.Dup ⟨1, by decide⟩),
   opAt 2230 .SUB,
   opAt 2231 .MLOAD,
   opAt 2232 (.Dup ⟨2, by decide⟩),
   opAt 2233 (.Dup ⟨6, by decide⟩),
   opAt 2234 (.Dup ⟨2, by decide⟩),
   opAt 2235 .MUL,
   opAt 2236 (.Swap ⟨1, by decide⟩),
   opAt 2237 (.Dup ⟨7, by decide⟩),
   opAt 2238 .MULMOD,
   opAt 2239 (.Dup ⟨1, by decide⟩),
   opAt 2240 (.Dup ⟨1, by decide⟩),
   opAt 2241 .LT,
   opAt 2242 .SUB,
   opAt 2243 (.Dup ⟨5, by decide⟩),
   opAt 2244 (.Dup ⟨2, by decide⟩),
   opAt 2245 .ADD,
   opAt 2246 (.Dup ⟨0, by decide⟩),
   opAt 2247 (.Swap ⟨6, by decide⟩),
   opAt 2248 .GT,
   opAt 2249 .SUB,
   opAt 2250 .SUB,
   opAt 2251 (.Dup ⟨4, by decide⟩),
   opAt 2252 (.Dup ⟨2, by decide⟩),
   opAt 2253 .MLOAD,
   opAt 2254 .ADD,
   opAt 2255 (.Dup ⟨0, by decide⟩),
   opAt 2256 (.Swap ⟨5, by decide⟩),
   opAt 2257 .GT,
   opAt 2258 .ADD,
   opAt 2259 (.Swap ⟨3, by decide⟩),
   opAt 2260 (.Dup ⟨1, by decide⟩),
   opAt 2261 .MSTORE,
   opAt 2262 (.Dup ⟨2, by decide⟩),
   opAt 2263 .ADD]

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


@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2228 = 2991 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2229 = 2994 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2229 = 2994 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2229 = 2994 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2230 = 2995 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2231 = 2996 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2232 = 2997 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2233 = 2998 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2234 = 2999 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2235 = 3000 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2236 = 3001 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2237 = 3002 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2238 = 3003 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2239 = 3004 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2240 = 3005 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2241 = 3006 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2242 = 3007 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2243 = 3008 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2244 = 3009 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2245 = 3010 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2246 = 3011 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2247 = 3012 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2248 = 3013 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2249 = 3014 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2250 = 3015 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2251 = 3016 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2252 = 3017 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2253 = 3018 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2254 = 3019 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2255 = 3020 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2256 = 3021 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2257 = 3022 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2258 = 3023 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2259 = 3024 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2260 = 3025 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2261 = 3026 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2262 = 3027 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2263 = 3028 := by
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

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2227 = 2990 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

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
      { s with pc := UInt256.ofNat 2990
               stack := pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3029
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
