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
existing caller interface. The second operand lies below the scratch region. -/
noncomputable def rows_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (pa pb n : Nat) (hn : n = 4 ∨ n = 8)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2048)
    (hminv : inverseInvariant mem n) (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) (hsnap : StagedOperand.Snapshot mem pa n) :
    GasSteps
      (TnM128Setup.outState s (mpZeroed s mem n) pb n 0 (UInt256.ofNat 3533)
        (TnM128Setup.l1Target n) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))
      (framed {s with memory := CarryRowModel.rowsCarry (mpZeroed s mem n) pa pb n n}
        (UInt256.ofNat 4156) (dst :: ret :: rest)) := by
  let z : CacheState := ⟨mpZeroed s mem n, UInt256.ofNat 0⟩
  have hn8 : n ≤ 8 := by omega
  have hz : Cached z.memory pa n tl inv m0 m96 m64 m32 :=
    ⟨hc.zeroed hn8 s, he.zeroed s n hn8, inverse_mpZeroed s mem n hn8 hminv,
      hsnap.zeroed_stage s hn8 hpa⟩
  have hpaFit : pa+32*n ≤ 2816 := by rcases hpa with h | rfl <;> omega
  have ha : aEnd.toNat = pa+32*(n-1) := by
    rw [hAend, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have g := TnM128MultiplySteps.multiply_steps s env z pa pb n hn
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa hpb (by omega)
    (Or.inl (by omega)) ha hz
  have hstart : TnM128Setup.outState s (mpZeroed s mem n) pb n 0 (UInt256.ofNat 3533)
      (TnM128Setup.l1Target n) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest) =
      rowState s z pb n 0 tl inv m0 aEnd m96 m64 m32 dst ret rest := by
    rcases hn with rfl | rfl <;>
      simp [TnM128Setup.outState, TnM128Setup.l1Target,
        TnM128Setup.zeroTn, rowState, TnCacheRowPointers.pointer, l1PC, l2PC,
        isFour, z, TnCacheFrameOps.frame, framed] <;> decide
  rw [hstart]
  simpa only [z, TnCacheInitialMemory.lift_zeroed] using g

#print axioms rows_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128InitialMultiply
