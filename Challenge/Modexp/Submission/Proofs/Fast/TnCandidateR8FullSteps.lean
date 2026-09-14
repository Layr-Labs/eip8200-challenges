import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareTailSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareFullSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8FullSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves
open TnCandidateSquareRowSteps TnCandidateSquareRowsSteps TnCandidateSquareTailSteps
open TnCandidateSquareFullSteps

/-- The specialized eight-limb row zero, all seven following rows, the carry
flush, and the square exit branch compute the existing square model. -/
noncomputable def square_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (z : CacheState) (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached z.memory 2368 8 tl inv m0 m96 m64 m32)
    (hzero : MachineState.readWord z.memory 2336 = UInt256.ofNat 0) :
    GasSteps
      { rowState s z 8 0 aprev tl inv m0 m96 m64 m32 dst ret rest with
          pc := UInt256.ofNat 4441 }
      (exitState s (SquareResult.sqRowsCarry (lift z.memory z.tn) 8 8)
        (squareRows z 8 8).tn 8 (previous (UInt256.ofNat 0) z.memory 8 8)
        tl inv m0 m96 m64 m32 dst ret rest) := by
  have hj : Decode.isValidJumpDest TnCandidate.bytecode 3740 = true :=
    TnCandidateL1Jumps.entry_jump 7 (by decide)
  have g0 := TnCandidateR8RowZero.prologue_steps s env z.memory z.tn
    inv m0 tl m96 m64 m32 aprev (dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hzero hj
  have g1 := suffix_steps s env z 8 0 (Or.inr rfl) (by decide)
    (UInt256.ofNat 0) tl inv m0 m96 m64 m32 dst ret rest hcap hact hc
  have first := g0.trans g1
  have g2 := rows_from s env z 8 1 (Or.inr rfl)
    (UInt256.ofNat 0) tl inv m0 m96 m64 m32 dst ret rest hcap hact hc (by decide)
    7 (by decide)
  have hrow : resultOfTb z 8 0 (UInt256.ofNat 0) = squareRows z 8 1 := rfl
  rw [hrow] at first
  have core := first.trans g2
  have done := finish_steps s env (squareRows z 8 8) 8 (by decide)
    (previous (UInt256.ofNat 0) z.memory 8 8) tl inv m0 m96 m64 m32 dst ret rest hcap hact
  have all := core.trans done
  rw [← squareRows_lift z 8 8 le_rfl (by decide)] at all
  simpa only [rowState, TnCandidateSquareSteps.outState, TnCacheRowPointers.pointer,
    if_pos (show 0 < 8 by decide), sqEnt, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceAdd] using all

#print axioms square_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8FullSteps
