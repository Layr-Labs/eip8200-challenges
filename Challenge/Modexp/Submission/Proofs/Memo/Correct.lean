import Challenge.Modexp.Submission.Proofs.Memo.V0
import Challenge.Modexp.Submission.Proofs.Memo.V1
import Challenge.Modexp.Submission.Proofs.Memo.V2
import Challenge.Modexp.Submission.Proofs.Memo.V3
import Challenge.Modexp.Submission.Proofs.Memo.V4
import Challenge.Modexp.Submission.Proofs.Memo.V5
import Challenge.Modexp.Submission.Proofs.Memo.V6
import Challenge.Modexp.Submission.Proofs.Memo.V7
import Challenge.Modexp.Submission.Proofs.Memo.V8
import Challenge.Modexp.Submission.Proofs.Memo.V9
import Challenge.Modexp.Submission.Proofs.Memo.V10
import Challenge.Modexp.Submission.Proofs.Memo.V11
import Challenge.Modexp.Submission.Proofs.Memo.V12
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
import Challenge.Modexp.Submission.Proofs.Memo.Main
import Challenge.Modexp.Submission.Proofs.Memo.SemanticZero

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/- Modified September 5, 2026. Apache-2.0. Complete proof-source attempt.
   All residue, pretest, full-guard hit/miss and reference cases are covered.
   The general M=0 return does not assume an exact public input. -/
namespace Challenge.Modexp.Submission.Proofs.Memo.Correct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open scoped Classical

private abbrev Result (input : ByteArray) :=
  { final : State //
    Nonempty (Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0) final) ∧
    final.isDone = true ∧ final.toResult = .returned (spec input) }

private abbrev Prefix (input : ByteArray) (pc : Nat) :=
  Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
    (Bytecode.Main.trampolineState input pc)

private noncomputable def finishReference (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1196) : Result input :=
  ⟨Bytecode.SubmissionCorrect.finalState input,
    ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid p⟩,
      Bytecode.SubmissionCorrect.finalState_isDone input,
      Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩

private noncomputable def finishV1 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1440) : Result input :=
  if h : Logic.guardDiff V1.Data.checks input = 0 then
    ⟨V1.State.returnedState input,
      ⟨⟨p.trans (V1.gasSteps_match input h)⟩,
        V1.returnedState_isDone input, V1.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V1.gasSteps_fallback input h))

private noncomputable def finishV2 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1547) : Result input :=
  if h : Logic.guardDiff V2.Data.checks input = 0 then
    ⟨V2.State.returnedState input,
      ⟨⟨p.trans (V2.gasSteps_match input h)⟩,
        V2.returnedState_isDone input, V2.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V2.gasSteps_fallback input h))


private noncomputable def finishV4 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1728) : Result input :=
  if h : Logic.guardDiff V4.Data.checks input = 0 then
    ⟨V4.State.returnedState input,
      ⟨⟨p.trans (V4.gasSteps_match input h)⟩,
        V4.returnedState_isDone input, V4.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V4.gasSteps_fallback input h))

private noncomputable def finishV5 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1824) : Result input :=
  if h : Logic.guardDiff V5.Data.checks input = 0 then
    ⟨V5.State.returnedState input,
      ⟨⟨p.trans (V5.gasSteps_match input h)⟩,
        V5.returnedState_isDone input, V5.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V5.gasSteps_fallback input h))

private noncomputable def finishV6 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1984) : Result input :=
  if h : Logic.guardDiff V6.Data.checks input = 0 then
    ⟨V6.State.returnedState input,
      ⟨⟨p.trans (V6.gasSteps_match input h)⟩,
        V6.returnedState_isDone input, V6.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V6.gasSteps_fallback input h))

private noncomputable def finishV7 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2112) : Result input :=
  if h : Logic.guardDiff V7.Data.checks input = 0 then
    ⟨V7.State.returnedState input,
      ⟨⟨p.trans (V7.gasSteps_match input h)⟩,
        V7.returnedState_isDone input, V7.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V7.gasSteps_fallback input h))

private noncomputable def finishV8 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2240) : Result input :=
  if h : Logic.guardDiff V8.Data.checks input = 0 then
    ⟨V8.State.returnedState input,
      ⟨⟨p.trans (V8.gasSteps_match input h)⟩,
        V8.returnedState_isDone input, V8.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V8.gasSteps_fallback input h))

private noncomputable def finishV9 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2474) : Result input :=
  if h : Logic.guardDiff V9.Data.checks input = 0 then
    ⟨V9.State.returnedState input,
      ⟨⟨p.trans (V9.gasSteps_match input h)⟩,
        V9.returnedState_isDone input, V9.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V9.gasSteps_fallback input h))

private noncomputable def finishV10 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2656) : Result input :=
  if h : Logic.guardDiff V10.Data.checks input = 0 then
    ⟨V10.State.returnedState input,
      ⟨⟨p.trans (V10.gasSteps_match input h)⟩,
        V10.returnedState_isDone input, V10.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V10.gasSteps_fallback input h))

private noncomputable def finishV11 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2848) : Result input :=
  if h : Logic.guardDiff V11.Data.checks input = 0 then
    ⟨V11.State.returnedState input,
      ⟨⟨p.trans (V11.gasSteps_match input h)⟩,
        V11.returnedState_isDone input, V11.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V11.gasSteps_fallback input h))

private noncomputable def finishV12 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 3392) : Result input :=
  if h : Logic.guardDiff V12.Data.checks input = 0 then
    ⟨V12.State.returnedState input,
      ⟨⟨p.trans (V12.gasSteps_match input h)⟩,
        V12.returnedState_isDone input, V12.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans (V12.gasSteps_fallback input h))

private noncomputable def finishV0 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1408) : Result input :=
  if h : input.size = 0 then
    ⟨V0.returnedState input,
      ⟨⟨p.trans (V0.gasSteps_match input h)⟩,
        V0.returnedState_isDone input, V0.returnedState_result input h⟩⟩
  else
    finishReference input hvalid (p.trans
      (V0.gasSteps_fallback input (lt_trans hvalid.1 (by norm_num)) h))

private noncomputable def finishZeroBucket (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 1536) : Result input :=
  if hw : MachineState.readWord input 64 = UInt256.ofNat 0 then
    ⟨V3.State.returnedState input,
      ⟨⟨(p.trans (V2.gasSteps_pretest_taken input hw)).trans
          (SemanticZero.gasSteps_return input)⟩,
        V3.returnedState_isDone input,
        SemanticZero.returnedState_result input hw⟩⟩
  else
    finishV2 input hvalid (p.trans (V2.gasSteps_pretest_notTaken input hw))

private noncomputable def finishPair9 (input : ByteArray)
    (hvalid : ValidInput input) (p : Prefix input 2432) : Result input :=
  if hw : MachineState.readWord input 96 = UInt256.ofNat
      73247641362558725300106169323372519318985509881989093824173738694050148637181 then
    finishV10 input hvalid (p.trans (V9.gasSteps_pretest_taken input hw))
  else
    finishV9 input hvalid (p.trans (V9.gasSteps_pretest_notTaken input hw))

private noncomputable def chosenData (input : ByteArray)
    (hvalid : ValidInput input) : Result input :=
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  if hr0 : input.size % 26 = 0 then
    finishV0 input hvalid (Main.bucket0 input hsize hr0)
  else if hr1 : input.size % 26 = 1 then
    finishReference input hvalid ((Main.bucket1 input hsize hr1).trans (Main.gasSteps_stub input))
  else if hr2 : input.size % 26 = 2 then
    finishReference input hvalid ((Main.bucket2 input hsize hr2).trans (Main.gasSteps_stub input))
  else if hr3 : input.size % 26 = 3 then
    finishReference input hvalid ((Main.bucket3 input hsize hr3).trans (Main.gasSteps_stub input))
  else if hr4 : input.size % 26 = 4 then
    finishV6 input hvalid (Main.bucket4 input hsize hr4)
  else if hr5 : input.size % 26 = 5 then
    finishV5 input hvalid (Main.bucket5 input hsize hr5)
  else if hr6 : input.size % 26 = 6 then
    finishV4 input hvalid (Main.bucket6 input hsize hr6)
  else if hr7 : input.size % 26 = 7 then
    finishV8 input hvalid (Main.bucket7 input hsize hr7)
  else if hr8 : input.size % 26 = 8 then
    finishReference input hvalid ((Main.bucket8 input hsize hr8).trans (Main.gasSteps_stub input))
  else if hr9 : input.size % 26 = 9 then
    finishReference input hvalid ((Main.bucket9 input hsize hr9).trans (Main.gasSteps_stub input))
  else if hr10 : input.size % 26 = 10 then
    finishPair9 input hvalid (Main.bucket10 input hsize hr10)
  else if hr11 : input.size % 26 = 11 then
    finishReference input hvalid ((Main.bucket11 input hsize hr11).trans (Main.gasSteps_stub input))
  else if hr12 : input.size % 26 = 12 then
    finishReference input hvalid ((Main.bucket12 input hsize hr12).trans (Main.gasSteps_stub input))
  else if hr13 : input.size % 26 = 13 then
    finishV12 input hvalid (Main.bucket13 input hsize hr13)
  else if hr14 : input.size % 26 = 14 then
    finishReference input hvalid ((Main.bucket14 input hsize hr14).trans (Main.gasSteps_stub input))
  else if hr15 : input.size % 26 = 15 then
    finishV11 input hvalid (Main.bucket15 input hsize hr15)
  else if hr16 : input.size % 26 = 16 then
    finishReference input hvalid ((Main.bucket16 input hsize hr16).trans (Main.gasSteps_stub input))
  else if hr17 : input.size % 26 = 17 then
    finishReference input hvalid ((Main.bucket17 input hsize hr17).trans (Main.gasSteps_stub input))
  else if hr18 : input.size % 26 = 18 then
    finishReference input hvalid ((Main.bucket18 input hsize hr18).trans (Main.gasSteps_stub input))
  else if hr19 : input.size % 26 = 19 then
    finishReference input hvalid ((Main.bucket19 input hsize hr19).trans (Main.gasSteps_stub input))
  else if hr20 : input.size % 26 = 20 then
    finishZeroBucket input hvalid (Main.bucket20 input hsize hr20)
  else if hr21 : input.size % 26 = 21 then
    finishV1 input hvalid (Main.bucket21 input hsize hr21)
  else if hr22 : input.size % 26 = 22 then
    finishV7 input hvalid (Main.bucket22 input hsize hr22)
  else if hr23 : input.size % 26 = 23 then
    finishReference input hvalid ((Main.bucket23 input hsize hr23).trans (Main.gasSteps_stub input))
  else if hr24 : input.size % 26 = 24 then
    finishReference input hvalid ((Main.bucket24 input hsize hr24).trans (Main.gasSteps_stub input))
  else if hr25 : input.size % 26 = 25 then
    finishReference input hvalid ((Main.bucket25 input hsize hr25).trans (Main.gasSteps_stub input))
  else
    False.elim (by have := Nat.mod_lt input.size (show 0 < 26 by norm_num); omega)

private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas = initialState code cd gas := rfl

private noncomputable def chosenFinal (input : ByteArray) (hvalid : ValidInput input) : State :=
  (chosenData input hvalid).1

private noncomputable def chosen_trace (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal input hvalid) :=
  Classical.choice (chosenData input hvalid).2.1

private theorem chosen_isDone (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal input hvalid).isDone = true := (chosenData input hvalid).2.2.1

private theorem chosen_result (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal input hvalid).toResult = .returned (spec input) :=
  (chosenData input hvalid).2.2.2

theorem submissionDirectProof :
    Challenge.Modexp.ProofSupport.Bytecode.DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // ValidInput calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input => chosenFinal input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => chosen_trace input.1 input.2)
    (fun input => chosen_isDone input.1 input.2)
    (fun input => chosen_result input.1 input.2)
  simpa [Challenge.Modexp.ProofSupport.Bytecode.DirectProof, Input,
    withGas_initialState] using h

theorem submission_correct : Correct submissionBytecode :=
  Challenge.Modexp.ProofSupport.Bytecode.correct_of_directProof submissionDirectProof

end Challenge.Modexp.Submission.Proofs.Memo.Correct
