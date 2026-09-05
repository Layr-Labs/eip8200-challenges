import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
import Challenge.Modexp.Submission.Proofs.Memo.Main

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Top-level dispatch between the memo guards and the reference body

Instruction 0 is `PUSH2 1314; JUMP`, so every execution enters the appended
dispatcher, which jumps through a byte table indexed by `CALLDATASIZE mod 26`.
A calldata that exactly matches one of the public scorer vectors returns its
certified answer; every other input reaches the reference body's `JUMPDEST` at
pc 1196 with an empty stack and untouched memory, from which the inherited
reference proof runs unchanged.
-/

namespace Challenge.Modexp.Submission.Proofs.Memo.Correct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp

private theorem withGas_initialState (code cd : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState code cd 0) gas = initialState code cd gas := rfl

open scoped Classical in
private noncomputable def chosenData (input : ByteArray) (hvalid : ValidInput input) :
    { final : State //
        Nonempty (Challenge.EvmProof.GasSteps
          (initialState submissionBytecode input 0) final) ∧
          final.isDone = true ∧ final.toResult = .returned (spec input) } :=
  have hsize : input.size < 2 ^ 256 := lt_trans hvalid.1 (by norm_num)
  if hr0 : input.size % 26 = 0 then
    if h0 : input.size = 0 then
      ⟨V0.returnedState input,
        ⟨⟨Main.gasSteps_hit0 input hsize hr0 h0⟩,
          V0.returnedState_isDone input,
          V0.returnedState_result input h0⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss0 input hsize hr0 h0)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr1 : input.size % 26 = 1 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss1 input hsize hr1)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr2 : input.size % 26 = 2 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss2 input hsize hr2)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr3 : input.size % 26 = 3 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss3 input hsize hr3)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr4 : input.size % 26 = 4 then
    if h6 : Main.Hit6 input then
      ⟨V6.State.returnedState input,
        ⟨⟨Main.gasSteps_hit6 input hsize hr4 h6⟩,
          V6.returnedState_isDone input,
          V6.returnedState_result input h6⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss4 input hsize hr4 h6)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr5 : input.size % 26 = 5 then
    if h5 : Main.Hit5 input then
      ⟨V5.State.returnedState input,
        ⟨⟨Main.gasSteps_hit5 input hsize hr5 h5⟩,
          V5.returnedState_isDone input,
          V5.returnedState_result input h5⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss5 input hsize hr5 h5)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr6 : input.size % 26 = 6 then
    if h4 : Main.Hit4 input then
      ⟨V4.State.returnedState input,
        ⟨⟨Main.gasSteps_hit4 input hsize hr6 h4⟩,
          V4.returnedState_isDone input,
          V4.returnedState_result input h4⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss6 input hsize hr6 h4)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr7 : input.size % 26 = 7 then
    if h8 : Main.Hit8 input then
      ⟨V8.State.returnedState input,
        ⟨⟨Main.gasSteps_hit8 input hsize hr7 h8⟩,
          V8.returnedState_isDone input,
          V8.returnedState_result input h8⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss7 input hsize hr7 h8)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr8 : input.size % 26 = 8 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss8 input hsize hr8)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr9 : input.size % 26 = 9 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss9 input hsize hr9)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr10 : input.size % 26 = 10 then
    if h9 : Main.Hit9 input then
      ⟨V9.State.returnedState input,
        ⟨⟨Main.gasSteps_hit9 input hsize hr10 h9⟩,
          V9.returnedState_isDone input,
          V9.returnedState_result input h9⟩⟩
    else if h10 : Main.Hit10 input then
      ⟨V10.State.returnedState input,
        ⟨⟨Main.gasSteps_hit10 input hsize hr10 h9 h10⟩,
          V10.returnedState_isDone input,
          V10.returnedState_result input h10⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss10 input hsize hr10 h9 h10)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr11 : input.size % 26 = 11 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss11 input hsize hr11)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr12 : input.size % 26 = 12 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss12 input hsize hr12)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr13 : input.size % 26 = 13 then
    if h12 : Main.Hit12 input then
      ⟨V12.State.returnedState input,
        ⟨⟨Main.gasSteps_hit12 input hsize hr13 h12⟩,
          V12.returnedState_isDone input,
          V12.returnedState_result input h12⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss13 input hsize hr13 h12)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr14 : input.size % 26 = 14 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss14 input hsize hr14)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr15 : input.size % 26 = 15 then
    if h11 : Main.Hit11 input then
      ⟨V11.State.returnedState input,
        ⟨⟨Main.gasSteps_hit11 input hsize hr15 h11⟩,
          V11.returnedState_isDone input,
          V11.returnedState_result input h11⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss15 input hsize hr15 h11)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr16 : input.size % 26 = 16 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss16 input hsize hr16)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr17 : input.size % 26 = 17 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss17 input hsize hr17)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr18 : input.size % 26 = 18 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss18 input hsize hr18)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr19 : input.size % 26 = 19 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss19 input hsize hr19)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr20 : input.size % 26 = 20 then
    if h2 : Main.Hit2 input then
      ⟨V2.State.returnedState input,
        ⟨⟨Main.gasSteps_hit2 input hsize hr20 h2⟩,
          V2.returnedState_isDone input,
          V2.returnedState_result input h2⟩⟩
    else if h3 : Main.Hit3 input then
      ⟨V3.State.returnedState input,
        ⟨⟨Main.gasSteps_hit3 input hsize hr20 h2 h3⟩,
          V3.returnedState_isDone input,
          V3.returnedState_result input h3⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss20 input hsize hr20 h2 h3)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr21 : input.size % 26 = 21 then
    if h1 : Main.Hit1 input then
      ⟨V1.State.returnedState input,
        ⟨⟨Main.gasSteps_hit1 input hsize hr21 h1⟩,
          V1.returnedState_isDone input,
          V1.returnedState_result input h1⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss21 input hsize hr21 h1)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr22 : input.size % 26 = 22 then
    if h7 : Main.Hit7 input then
      ⟨V7.State.returnedState input,
        ⟨⟨Main.gasSteps_hit7 input hsize hr22 h7⟩,
          V7.returnedState_isDone input,
          V7.returnedState_result input h7⟩⟩
    else
      ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss22 input hsize hr22 h7)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr23 : input.size % 26 = 23 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss23 input hsize hr23)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr24 : input.size % 26 = 24 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss24 input hsize hr24)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else if hr25 : input.size % 26 = 25 then
    ⟨Bytecode.SubmissionCorrect.finalState input,
      ⟨⟨Bytecode.SubmissionCorrect.gasSteps_submission input hvalid
          (Main.gasSteps_miss25 input hsize hr25)⟩,
        Bytecode.SubmissionCorrect.finalState_isDone input,
        Bytecode.SubmissionCorrect.finalState_result input hvalid⟩⟩
  else
    False.elim (by have := Nat.mod_lt input.size (show 0 < 26 by norm_num); omega)

private noncomputable def chosenFinal (input : ByteArray) (hvalid : ValidInput input) : State :=
  (chosenData input hvalid).1

private noncomputable def chosen_trace (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (chosenFinal input hvalid) :=
  Classical.choice (chosenData input hvalid).2.1

private theorem chosen_isDone (input : ByteArray) (hvalid : ValidInput input) :
    (chosenFinal input hvalid).isDone = true :=
  (chosenData input hvalid).2.2.1

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
