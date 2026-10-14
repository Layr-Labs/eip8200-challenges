import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFinishSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel SquareResult
open TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves
open TnM128SquareFirstModel TnM128SquareTailSteps TnM128SquareFinishSteps

def finalCache (mem : ByteArray) : CacheState := run (first mem) 8 1 7

/-- All eight square rows, from row 0 at 5092 to the `n8` block (4207) with the carry word on the
stack (`final_lift` relates the memory to the machine-carry square model). -/
noncomputable def square_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (aprev w3 tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached mem 2368 8 tl inv m0 m96 m64 m32)
    (hw3 : w3 = MachineState.readWord mem 192)
    (ent : UInt256 := UInt256.ofNat 3347) :
    GasSteps (TnM128SquareFirstSteps.input s mem aprev w3 tl inv m0 m96 m64 m32 dst ret rest ent)
      (exitState s (finalCache mem).memory (finalCache mem).tn 8
        (sqX mem 8 7) w3 tl inv m0 m96 m64 m32 dst ret rest) := by
  have g0 := TnM128SquareFirstSteps.steps s env mem aprev w3 tl inv m0 m96 m64 m32 dst ret rest hcap
    hact hc hw3 ent
  have g1 := TnM128SquareTailSteps.steps s env (first mem) 8 1 rfl
    w3 tl inv m0 m96 m64 m32 dst ret rest hcap hact (first_cached s hc)
    (hw3.trans (first_read s mem 192 (Or.inl (by decide))).symm) 7 (by decide)
  have g2 := finish_steps s env (finalCache mem) 8 (by decide)
    (previous (finalCache mem).memory 8 8) w3 tl inv m0 m96 m64 m32 dst ret rest hcap hact
  have both := (g0.trans g1).trans g2
  have hp : previous (finalCache mem).memory 8 8 = sqX mem 8 7 := by
    change MachineState.readWord (run (first mem) 8 1 7).memory (aAddr 8 7) = _
    rw [run_read (first mem) 8 1 (aAddr 8 7) (by decide)
      (Or.inr (by decide)) 7 (by decide), first_read s mem (aAddr 8 7) (Or.inr (by decide))]
    rfl
  rw [hp] at both
  exact both

/-- The square's memory is the rows' model with the carry word left out. -/
theorem final_lift (s : State) (mem : ByteArray) (hscr : R8RowZeroExact.ScratchZero mem) :
    lift (finalCache mem).memory (finalCache mem).tn = sqRowsCarry (mpZeroed s mem 8) 8 8 :=
  run_lift (first mem) (mpZeroed s mem 8) 8 1 (by decide) (first_lift s mem hscr) 7 (by decide)

#print axioms square_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullSteps
