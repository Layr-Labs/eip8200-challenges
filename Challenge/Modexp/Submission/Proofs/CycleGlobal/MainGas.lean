import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainTrampolinesLow
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainTrampolinesHigh
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainHeaderLoad
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainHeaderCheck
noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.Main
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

private def gasSteps_tramp0 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (trampolineState input 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka tramp0Path rfl rfl (run_tramp0 input)
      rfl deployAddress_not_precompile

/-- The body's own `JUMPDEST`, reached when the legacy fast path declines. -/
private def gasSteps_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 533)
      (headerEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka tramp7DestPath rfl rfl
      (run_tramp7Dest input) rfl deployAddress_not_precompile

private def gasSteps_headerLoad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerEntryState input)
      (headerLoadedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka headerLoadPath rfl rfl (run_headerLoad input)
      rfl deployAddress_not_precompile

private def gasSteps_headerCheck (input : ByteArray) :
    Challenge.EvmProof.GasSteps (headerLoadedState input) (headerState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka headerCheckPath rfl rfl
      (run_headerCheck input) rfl deployAddress_not_precompile

@[simp] private theorem gasSteps_tramp0_cost (input : ByteArray) :
    (gasSteps_tramp0 input).cost = 0 := by rfl

@[simp] private theorem gasSteps_tramp7Dest_cost (input : ByteArray) :
    (gasSteps_tramp7Dest input).cost = 1 := by rfl

@[simp] private theorem gasSteps_headerLoad_cost (input : ByteArray) :
    (gasSteps_headerLoad input).cost = 17 := by rfl

-- `JUMPDEST ; JUMPDEST` costs 1 + 1 (was `PUSH2 ; POP` = 3 + 2).
@[simp] private theorem gasSteps_headerCheck_cost (input : ByteArray) :
    (gasSteps_headerCheck input).cost = 0 := by rfl

/-- The header block starting from the body `JUMPDEST` at pc 1326 rather than
from the entry.  The appended fast path reaches that pc itself, so the entry hop
is factored out. -/
def gasSteps_headerFromBody (input : ByteArray) :
    Challenge.EvmProof.GasSteps (trampolineState input 533)
      (headerState input) := by
  exact (gasSteps_tramp7Dest input).trans <|
    (gasSteps_headerLoad input).trans (gasSteps_headerCheck input)

/-- The total initial hop to the early-word dispatcher. -/
def gasSteps_entryHop (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (trampolineState input 0) := gasSteps_tramp0 input

/-- The reference header block, prefixed by whatever trace reaches the body
`JUMPDEST` at pc 1326.  The appended fast path supplies that prefix on the
inputs it declines. -/
def gasSteps_header (input : ByteArray) (_hvalid : ValidInput input)
    (entry : Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (trampolineState input 533)) :
    Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (headerState input) :=
  entry.trans (gasSteps_headerFromBody input)

end CycleSubmission.Global.Main
