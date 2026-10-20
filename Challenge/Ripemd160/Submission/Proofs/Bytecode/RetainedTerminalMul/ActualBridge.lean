import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.LocatedBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

/-! Transport the retained-word sidecar's located traces to the actual submission.
The instruction-vector equality is kernel checked; the code equality follows from
both assembly certificates, rather than assuming that the two images agree. -/
namespace RetainedActual115
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105 RetainedResultEdge112

theorem instructions_eq_actual :
    RetainedBridge111.Candidate.instructions = Artifact.submissionArtifact.instructions := by
  rfl

theorem candidateCode_eq_actual :
    RetainedBridge111.Candidate.candidateCode = submissionBytecode := by
  have h := Artifact.submissionArtifact.assembly_eq
  rw [← instructions_eq_actual] at h
  have hd : Artifact.submissionArtifact.data = [] := rfl
  rw [hd] at h
  exact RetainedBridge111.Candidate.exact_assembly.symm.trans h

theorem artifact_eq_actual :
    RetainedBridge111.Candidate.artifact = Artifact.submissionArtifact := by
  have hc := candidateCode_eq_actual
  have hi := instructions_eq_actual
  have hd : RetainedBridge111.Candidate.artifact.data = Artifact.submissionArtifact.data := rfl
  have ext (a b : DataProgramArtifact)
      (hc : a.code = b.code) (hi : a.instructions = b.instructions)
      (hd : a.data = b.data) : a = b := by
    cases a with
    | mk ac ai ad ap =>
      cases b with
      | mk bc bi bd bp =>
        cases hc
        cases hi
        cases hd
        rfl
  exact ext _ _ hc hi hd

structure Env (s : State) : Prop where
  code : s.executionEnv.code = submissionBytecode
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def Env.toSidecar {s : State} (e : Env s) : RetainedLocated113.Env s :=
  ⟨e.code.trans candidateCode_eq_actual.symm, e.fork, e.run, e.np⟩

def gasSteps_data (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0) :=
  RetainedLocated113.gasSteps_data s rho e.toSidecar hs ha

def gasSteps_return (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :=
  RetainedLocated113.gasSteps_return s rho e.toSidecar hs ha hz

def gasSteps_miss (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hn : retainedResult s.executionEnv.calldata ≠ 0) :=
  RetainedLocated113.gasSteps_miss s rho e.toSidecar hs ha hn

def gasSteps_anchor_return (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :=
  RetainedLocated113.gasSteps_anchor_return s rho e.toSidecar hs ha hne hz

def gasSteps_anchor_miss (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hn : retainedResult s.executionEnv.calldata ≠ 0) :=
  RetainedLocated113.gasSteps_anchor_miss s rho e.toSidecar hs ha hne hn

def gasSteps_anchor_repeat (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980)
    (heq : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :=
  RetainedLocated113.gasSteps_anchor_repeat s rho e.toSidecar hs heq

private def initialEnv (input : ByteArray) : Env (initialState submissionBytecode input 0) :=
  ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩

/-- The anchor fall-through retains the first word at the cold seed entry. -/
def gasSteps_anchor_fall (input : ByteArray)
    (href : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    GasSteps (DirectGuard.atPC input 18) (DirectGuard.sizeMatched input) := by
  have h := RetainedLocated113.lift .anchor (initialState submissionBytecode input 0) _
    (initialEnv input).toSidecar []
    (RetainedIntegration105.run_anchor_fall (initialState submissionBytecode input 0) []
      (by decide) rfl href)
  simpa only [DirectGuard.sizeMatched, DirectGuard.atPC,
    List.append_nil, initialState_calldata, initialState_stack, RetainedLocated113.pc] using h

def gasSteps_anchor_low_fall (input : ByteArray)
    (href : Low64RepeatMath.condition input = 0) :
    GasSteps (DirectGuard.atPC input 18) (DirectGuard.sizeMatched input) := by
  have h := RetainedLocated113.lift .anchor (initialState submissionBytecode input 0) _
    (initialEnv input).toSidecar []
    (RetainedIntegration105.run_anchor_low_fall (initialState submissionBytecode input 0) []
      (by decide) rfl href)
  simpa only [DirectGuard.sizeMatched, DirectGuard.atPC,
    List.append_nil, initialState_calldata, initialState_stack, RetainedLocated113.pc] using h

/-- The taken edge enters the private 1000-byte scanner with the retained word. -/
def gasSteps_anchor_taken (input : ByteArray)
    (href : Low64RepeatMath.condition input ≠ 0) :
    GasSteps (DirectGuard.atPC input 18)
      {PatternedScan.stS input 8157 [] with stack := [MachineState.readWord input 0]} := by
  have hv : Decode.isValidJumpDest submissionBytecode 8157 = true := by
    rw [← candidateCode_eq_actual]
    exact RetainedLocated113.valid_anchor
  have h := RetainedLocated113.lift .anchor (initialState submissionBytecode input 0) _
    (initialEnv input).toSidecar []
    (RetainedIntegration105.run_anchor_taken (initialState submissionBytecode input 0) []
      (by decide) rfl href hv)
  simpa only [DirectGuard.atPC, PatternedScan.stS,
    List.append_nil, initialState_calldata, initialState_stack, RetainedLocated113.pc] using h

#print axioms instructions_eq_actual
#print axioms candidateCode_eq_actual
#print axioms artifact_eq_actual
#print axioms gasSteps_anchor_fall
#print axioms gasSteps_anchor_taken
end RetainedActual115
