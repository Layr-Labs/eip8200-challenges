import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.LocatedBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalMulRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Exact repeated-word scanner for the isolated candidate. This joins the
retained anchor to the unchanged repeated-word backend, but is not the
whole-image entry certificate. -/
namespace RetainedRepeat114
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate RetainedIntegration105

private def scanner := TerminalMulRaw.template

theorem actual_scanner_slice :
    (RetainedBridge111.Candidate.instructions.drop 5260).take scanner.length = scanner := by
  rfl

private theorem scanner_bounds :
    5260 + scanner.length ≤ RetainedBridge111.Candidate.instructions.length := by
  rw [RetainedBridge111.Candidate.instruction_count]
  decide

private theorem scanner_wf : StackRoundData.TemplateWellFormed scanner := by decide

private def scannerSite : GenericRoundSite RetainedBridge111.Candidate.artifact .Osaka scanner :=
  StackSiteBuilder.ofSlice scanner 5260 actual_scanner_slice scanner_bounds
    RetainedLocated113.code_bound
    (StackRoundData.templateWellFormed_mem scanner_wf) (by decide)

private theorem scannerSite_pc : scannerSite.startPC = UInt256.ofNat 9429 := by
  change UInt256.ofNat (RetainedBridge111.Candidate.artifact.instructionPC 5260) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem scanner_advances : ∀ i ∈ scanner.dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  decide

/-- The terminal MUL consumes the reference, leaving exactly one accumulator
above the arbitrary original stack tail. Nonzero reference and Boolean seed
are proven by the anchor and equality-accumulator contracts, not assumed
from benchmark vectors. -/
def gasSteps_scanner (s : State) (rho : List UInt256) (e : RetainedLocated113.Env s)
    (hs : rho.length ≤ 980)
    (href : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    GasSteps
      {s with pc := UInt256.ofNat 9429, stack :=
        [DirectGuard.equalityAcc s.executionEnv.calldata 0,
         KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho}
      {s with pc := UInt256.ofNat 9632, stack :=
        [DirectGuard.equalityAcc s.executionEnv.calldata 10] ++ rho} := by
  apply RecognitionLift.gasSteps_of_raw scannerSite
    {s with pc := UInt256.ofNat 9429, stack :=
      [DirectGuard.equalityAcc s.executionEnv.calldata 0,
       KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho}
    _ e.code e.fork e.run e.np scannerSite_pc.symm scanner_advances
  simpa only [scanner] using TerminalMulRaw.run_equalityAcc s rho (by omega) e.run href

/-- Candidate-specific decoded execution from PC21 through the repeated-word
anchor, seed, all full-word comparisons, and terminal MUL at PC9629. -/
def gasSteps_anchor_scanner (s : State) (rho : List UInt256) (e : RetainedLocated113.Env s)
    (hs : rho.length ≤ 980)
    (href : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    GasSteps {s with pc := UInt256.ofNat 21, stack := rho}
      {s with pc := UInt256.ofNat 9632, stack :=
        [DirectGuard.equalityAcc s.executionEnv.calldata 10] ++ rho} :=
  (RetainedLocated113.gasSteps_anchor_repeat s rho e hs href).trans
    (gasSteps_scanner s rho e hs href)

#print axioms actual_scanner_slice
#print axioms gasSteps_scanner
#print axioms gasSteps_anchor_scanner
end RetainedRepeat114
