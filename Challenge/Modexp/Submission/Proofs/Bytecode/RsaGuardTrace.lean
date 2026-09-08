import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunPre
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunOne
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunTwo
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunThree
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunFour
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardHit
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-! RSA guard control-flow composition. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardTrace

open EvmSemantics
open EvmSemantics.EVM
open RsaGuardDefs

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_missA (input : ByteArray)
    (h128 : modulusSize input ≠ 128) (h256 : modulusSize input ≠ 256) :
    Challenge.EvmProof.GasSteps (entryState input) (missState input) :=
  (sound prePath (RsaGuardRunPre.run_pre_taken input h128 h256)).trans
    (sound missPath (RsaGuardRunPre.run_miss input))

def gasSteps_missB (input : ByteArray)
    (hpre : modulusSize input = 128 ∨ modulusSize input = 256)
    (hm0 : ¬RsaGuardLogic.MatchesOne input)
    (hm1 : ¬RsaGuardLogic.MatchesTwo input)
    (hm2 : ¬RsaGuardLogic.MatchesThree input)
    (hm3 : ¬RsaGuardLogic.MatchesFour input)
    : Challenge.EvmProof.GasSteps (entryState input) (missState input) :=
  (sound prePath (by
    rcases hpre with h | h
    · exact RsaGuardRunPre.run_pre_untaken128 input h
    · exact RsaGuardRunPre.run_pre_untaken256 input h)).trans
  ((sound mPathOne (RsaGuardRunOne.run_miss input hm0)).trans ((sound mPathTwo (RsaGuardRunTwo.run_miss input hm1)).trans ((sound mPathThree (RsaGuardRunThree.run_miss input hm2)).trans ((sound mPathFour (RsaGuardRunFour.run_miss input hm3)).trans (sound missPath (RsaGuardRunPre.run_miss input))))))

def gasSteps_hitOne (input : ByteArray)
    (h : RsaGuardLogic.MatchesOne input) :
    Challenge.EvmProof.GasSteps (entryState input)
      (RsaGuardHit.hitReturnedStateOne input) :=
  (sound prePath (RsaGuardRunPre.run_pre_untaken128 input h.2.2.1)).trans
  (sound hPathOne (RsaGuardHit.run_hitOne input))

def hitFullOne (input : ByteArray)
    (h : RsaGuardLogic.MatchesOne input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨RsaGuardHit.hitReturnedStateOne input, ⟨gasSteps_hitOne input h⟩,
    by rfl, RsaResult.hitResultOne input h⟩

def gasSteps_hitTwo (input : ByteArray)
    (h : RsaGuardLogic.MatchesTwo input) :
    Challenge.EvmProof.GasSteps (entryState input)
      (RsaGuardHit.hitReturnedStateTwo input) :=
  (sound prePath (RsaGuardRunPre.run_pre_untaken128 input h.2.2.1)).trans
  ((sound mPathOne (RsaGuardRunOne.run_miss input (RsaGuardLogic.excl_Two_One input h))).trans (sound hPathTwo (RsaGuardHit.run_hitTwo input)))

def hitFullTwo (input : ByteArray)
    (h : RsaGuardLogic.MatchesTwo input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨RsaGuardHit.hitReturnedStateTwo input, ⟨gasSteps_hitTwo input h⟩,
    by rfl, RsaResult.hitResultTwo input h⟩

def gasSteps_hitThree (input : ByteArray)
    (h : RsaGuardLogic.MatchesThree input) :
    Challenge.EvmProof.GasSteps (entryState input)
      (RsaGuardHit.hitReturnedStateThree input) :=
  (sound prePath (RsaGuardRunPre.run_pre_untaken256 input h.2.2.1)).trans
  ((sound mPathOne (RsaGuardRunOne.run_miss input (RsaGuardLogic.excl_Three_One input h))).trans ((sound mPathTwo (RsaGuardRunTwo.run_miss input (RsaGuardLogic.excl_Three_Two input h))).trans (sound hPathThree (RsaGuardHit.run_hitThree input))))

def hitFullThree (input : ByteArray)
    (h : RsaGuardLogic.MatchesThree input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨RsaGuardHit.hitReturnedStateThree input, ⟨gasSteps_hitThree input h⟩,
    by rfl, RsaResult.hitResultThree input h⟩

def gasSteps_hitFour (input : ByteArray)
    (h : RsaGuardLogic.MatchesFour input) :
    Challenge.EvmProof.GasSteps (entryState input)
      (RsaGuardHit.hitReturnedStateFour input) :=
  (sound prePath (RsaGuardRunPre.run_pre_untaken256 input h.2.2.1)).trans
  ((sound mPathOne (RsaGuardRunOne.run_miss input (RsaGuardLogic.excl_Four_One input h))).trans ((sound mPathTwo (RsaGuardRunTwo.run_miss input (RsaGuardLogic.excl_Four_Two input h))).trans ((sound mPathThree (RsaGuardRunThree.run_miss input (RsaGuardLogic.excl_Four_Three input h))).trans (sound hPathFour (RsaGuardHit.run_hitFour input)))))

def hitFullFour (input : ByteArray)
    (h : RsaGuardLogic.MatchesFour input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨RsaGuardHit.hitReturnedStateFour input, ⟨gasSteps_hitFour input h⟩,
    by rfl, RsaResult.hitResultFour input h⟩

def gasSteps_miss (input : ByteArray)
    (h : ¬RsaGuardLogic.Matches input) :
    Challenge.EvmProof.GasSteps (entryState input) (missState input) := by
  have h0 := RsaGuardLogic.missOne_of input h
  have h1 := RsaGuardLogic.missTwo_of input h
  have h2 := RsaGuardLogic.missThree_of input h
  have h3 := RsaGuardLogic.missFour_of input h
  by_cases hpre : modulusSize input = 128 ∨ modulusSize input = 256
  · exact gasSteps_missB input hpre h0 h1 h2 h3
  · push_neg at hpre
    exact gasSteps_missA input hpre.1 hpre.2

def missFull (input : ByteArray) (h : ¬RsaGuardLogic.Matches input) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 3924)
      (Main.trampolineState input 1314) :=
  gasSteps_miss input h

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardTrace
