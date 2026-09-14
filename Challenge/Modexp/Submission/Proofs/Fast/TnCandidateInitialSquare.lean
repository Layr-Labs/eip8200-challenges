import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8FullSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareExit
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSetupFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateInitialSquare
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareModel
open CiosCachedMidMemory TnCacheRowModel TnCacheRowPreserves TnCacheSquareModel
open TnCandidateSquareRowSteps TnCandidateSquareRowsSteps

def finalTn (s : State) (mem : ByteArray) : UInt256 :=
  (squareRows ⟨mpZeroed s mem 8, UInt256.ofNat 0⟩ 8 8).tn

def last (mem : ByteArray) : UInt256 := sqX (SquareResult.sqRowsCarry mem 8 7) 8 7

theorem last_eq (mem : ByteArray) : last mem = sqX mem 8 7 := by
  unfold last sqX
  exact SquareResult.readWord_sqRowsCarry_far mem 8 (aAddr 8 7)
    (Or.inr (by decide)) 7 (by decide)

/-- The initialized, specialized eight-limb square exposes its materialized
carry-row memory and the unchanged caller frame, with the final carry explicit. -/
noncomputable def square_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (a0 tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hminv : inverseInvariant mem 8) (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    GasSteps
      { TnCacheSetup.outState s (mpZeroed s mem 8) 2368 8 0 (UInt256.ofNat 4471)
          (TnCacheSetup.l1Target 8) inv m0
          (tl :: m96 :: m64 :: m32 :: a0 :: dst :: ret :: rest) with pc := UInt256.ofNat 4441 }
      (TnCandidateSquareExit.frameAt (finalTn s mem) 4362 s
        (SquareResult.sqRowsCarry (mpZeroed s mem 8) 8 8) 8 (UInt256.ofNat 2336)
        (UInt256.ofNat 4036) tl inv m0 m96 m64 m32 (last (mpZeroed s mem 8)) dst ret rest) := by
  let z : CacheState := ⟨mpZeroed s mem 8, UInt256.ofNat 0⟩
  have hz : Cached z.memory 2368 8 tl inv m0 m96 m64 m32 :=
    ⟨hc.zeroed (by decide) s, he.zeroed s 8 (by decide),
      inverse_mpZeroed s mem 8 (by decide) hminv, by intro _ _; rfl⟩
  have g := TnCandidateR8FullSteps.square_steps s env z a0 tl inv m0 m96 m64 m32 dst ret rest
    hcap hact hz (readWord_mpZeroed_zero s mem 8 2336 (by decide) (by decide))
  have hlast : previous (UInt256.ofNat 0) z.memory 8 8 = last z.memory :=
    (last_eq z.memory).symm
  rw [hlast] at g
  have h1 : TnCacheSetup.l1Target 8 = UInt256.ofNat 3740 := by decide
  have h2 : TnCacheSetup.l2Target 8 = UInt256.ofNat 4023 := by decide
  simpa only [TnCacheSetup.outState, TnCacheSetup.zeroTn, h1, h2,
    rowState, if_pos (show 0 < 8 by decide), sqEnt, TnCacheRowPointers.pointer,
    TnCandidateSquareFullSteps.exitState, TnCandidateSquareExit.frameAt,
    TnCandidateSquareExit.frameStack, finalTn, z, TnCacheInitialMemory.lift_zeroed,
    TnCacheFrameOps.frame, framed, TnCandidateReductionSteps.l2PC,
    if_neg (show ¬ (8 : Nat) = 4 by decide), Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    List.cons_append, List.nil_append] using g

#print axioms square_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateInitialSquare
