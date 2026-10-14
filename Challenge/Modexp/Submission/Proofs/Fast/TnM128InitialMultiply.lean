import Challenge.Modexp.Submission.Proofs.Fast.TnM128MultiplySteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128InitialMultiply
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosCachedMidMemory TnCacheRowModel TnCacheRowPreserves
open TnM128RowsSteps TnM128RowSteps TnM128ReductionSteps

/-- The initialized kernel exposes the same completed carry-row memory as the
existing caller interface; the multiplier block is the one at `0x100`. -/
noncomputable def rows_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (pa n : Nat) (hn : n = 4 ∨ n = 8)
    (w3 ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (hminv : inverseInvariant mem n) (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) (hsnap : StagedOperand.Snapshot mem pa n)
    (hw3 : n = 8 → w3 = MachineState.readWord mem 192) :
    GasSteps
      (rowState s ⟨mpZeroed s mem n, UInt256.ofNat 0⟩ n 0 w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (framed {s with memory := CarryRowModel.rowsCarry (mpZeroed s mem n) pa 256 n n}
        (UInt256.ofNat 3902) (dst :: ret :: rest)) := by
  let z : CacheState := ⟨mpZeroed s mem n, UInt256.ofNat 0⟩
  have hn8 : n ≤ 8 := by omega
  have hz : Cached z.memory pa n tl inv m0 m96 m64 m32 :=
    ⟨hc.zeroed hn8 s, he.zeroed s n hn8, inverse_mpZeroed s mem n hn8 hminv,
      hsnap.zeroed_stage s hn8 hpa⟩
  have hpaFit : pa+32*n ≤ 2816 := by rcases hpa with h | rfl <;> omega
  have ha : aEnd.toNat = pa+32*(n-1) := by
    rw [hAend, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have g := TnM128MultiplySteps.multiply_steps s env z pa n hn
    w3 ent tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa ha hz
    (fun h => (hw3 h).trans (readWord_mpZeroed s mem n 192 hn8 (Or.inl (by decide))).symm)
  simpa only [z, TnCacheInitialMemory.lift_zeroed] using g

#print axioms rows_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128InitialMultiply
