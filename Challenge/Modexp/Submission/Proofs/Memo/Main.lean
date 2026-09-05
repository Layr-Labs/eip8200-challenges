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
import Challenge.Modexp.Submission.Proofs.Memo.EmptyReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.MainGas

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.Main

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch

private def sound {s t : State} (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

abbrev init (input : ByteArray) : State := initialState submissionBytecode input 0

def Hit1 (input : ByteArray) : Prop :=
  guardDiff V1.Data.checks input = 0

def Hit2 (input : ByteArray) : Prop :=
  guardDiff V2.Data.checks input = 0

def Hit3 (input : ByteArray) : Prop :=
  guardDiff V3.Data.checks input = 0

def Hit4 (input : ByteArray) : Prop :=
  guardDiff V4.Data.checks input = 0

def Hit5 (input : ByteArray) : Prop :=
  guardDiff V5.Data.checks input = 0

def Hit6 (input : ByteArray) : Prop :=
  guardDiff V6.Data.checks input = 0

def Hit7 (input : ByteArray) : Prop :=
  guardDiff V7.Data.checks input = 0

def Hit8 (input : ByteArray) : Prop :=
  guardDiff V8.Data.checks input = 0

def Hit9 (input : ByteArray) : Prop :=
  guardDiff V9.Data.checks input = 0

def Hit10 (input : ByteArray) : Prop :=
  guardDiff V10.Data.checks input = 0

def Hit11 (input : ByteArray) : Prop :=
  guardDiff V11.Data.checks input = 0

def Hit12 (input : ByteArray) : Prop :=
  guardDiff V12.Data.checks input = 0

/-- Entry hop, dispatcher prefix, `ADD` and the computed `JUMP` for residue `r` with table entry `e`. -/
def gasSteps_bucket (input : ByteArray) (r e : Nat) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = r)
    (he : UInt256.byteAt (UInt256.ofNat r) (UInt256.ofNat 19978037702055533804967148740280010722836663273717868341649456475336210066219) = UInt256.ofNat e)
    (he255 : e ≤ 255)
    (hjump : Decode.isValidJumpDest submissionBytecode (32 * e) = true) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input (32 * e)) :=
  ((Bytecode.Main.gasSteps_entryHop input).trans
    (sound prefixPath rfl (run_prefix input r e hsize hr he he255) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_jump input (32 * e) (by omega) hjump) rfl rfl deployAddress_not_precompile)

def gasSteps_stub (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Bytecode.Main.trampolineState input 1376) (Bytecode.Main.trampolineState input 1196) :=
  (sound stubPrefixPath rfl (run_stub_prefix input) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_stub_jump input) rfl rfl deployAddress_not_precompile)

def gasSteps_hit0 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 0) (h : input.size = 0) :
    Challenge.EvmProof.GasSteps (init input) (V0.returnedState input) :=
  (gasSteps_bucket input 0 44 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1035 (by rfl))).trans (V0.gasSteps_match input h)

def gasSteps_miss0 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 0) (h : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 0 44 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1035 (by rfl))).trans (V0.gasSteps_fallback input hsize h)

def gasSteps_miss1 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 1) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 1 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss2 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 2) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 2 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss3 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 3) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 3 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_hit6 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 4) (h : Hit6 input) :
    Challenge.EvmProof.GasSteps (init input) (V6.State.returnedState input) :=
  (gasSteps_bucket input 4 59 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1250 (by rfl))).trans (V6.gasSteps_match input h)

def gasSteps_miss4 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 4) (hk : ¬ Hit6 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 4 59 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1250 (by rfl))).trans (V6.gasSteps_fallback input hk)

def gasSteps_hit5 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 5) (h : Hit5 input) :
    Challenge.EvmProof.GasSteps (init input) (V5.State.returnedState input) :=
  (gasSteps_bucket input 5 54 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1195 (by rfl))).trans (V5.gasSteps_match input h)

def gasSteps_miss5 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 5) (hk : ¬ Hit5 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 5 54 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1195 (by rfl))).trans (V5.gasSteps_fallback input hk)

def gasSteps_hit4 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 6) (h : Hit4 input) :
    Challenge.EvmProof.GasSteps (init input) (V4.State.returnedState input) :=
  (gasSteps_bucket input 6 52 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1170 (by rfl))).trans (V4.gasSteps_match input h)

def gasSteps_miss6 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 6) (hk : ¬ Hit4 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 6 52 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1170 (by rfl))).trans (V4.gasSteps_fallback input hk)

def gasSteps_hit8 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 7) (h : Hit8 input) :
    Challenge.EvmProof.GasSteps (init input) (V8.State.returnedState input) :=
  (gasSteps_bucket input 7 68 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1364 (by rfl))).trans (V8.gasSteps_match input h)

def gasSteps_miss7 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 7) (hk : ¬ Hit8 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 7 68 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1364 (by rfl))).trans (V8.gasSteps_fallback input hk)

def gasSteps_miss8 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 8) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 8 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss9 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 9) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 9 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_hit9 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 10) (hw : MachineState.readWord input 94 ≠ UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (h : Hit9 input) :
    Challenge.EvmProof.GasSteps (init input) (V9.State.returnedState input) :=
  ((gasSteps_bucket input 10 74 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1424 (by rfl))).trans (V9.gasSteps_pretest_notTaken input hw)).trans (V9.gasSteps_match input h)

def gasSteps_miss10a (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 10) (hw : MachineState.readWord input 94 ≠ UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (hk : ¬ Hit9 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  ((gasSteps_bucket input 10 74 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1424 (by rfl))).trans (V9.gasSteps_pretest_notTaken input hw)).trans (V9.gasSteps_fallback input hk)

def gasSteps_hit10 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 10) (hw : MachineState.readWord input 94 = UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (h : Hit10 input) :
    Challenge.EvmProof.GasSteps (init input) (V10.State.returnedState input) :=
  ((gasSteps_bucket input 10 74 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1424 (by rfl))).trans (V9.gasSteps_pretest_taken input hw)).trans (V10.gasSteps_match input h)

def gasSteps_miss10b (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 10) (hw : MachineState.readWord input 94 = UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (hs : ¬ Hit10 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  ((gasSteps_bucket input 10 74 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1424 (by rfl))).trans (V9.gasSteps_pretest_taken input hw)).trans (V10.gasSteps_fallback input hs)

def gasSteps_miss11 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 11) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 11 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss12 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 12) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 12 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_hit12 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 13) (h : Hit12 input) :
    Challenge.EvmProof.GasSteps (init input) (V12.State.returnedState input) :=
  (gasSteps_bucket input 13 105 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1608 (by rfl))).trans (V12.gasSteps_match input h)

def gasSteps_miss13 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 13) (hk : ¬ Hit12 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 13 105 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1608 (by rfl))).trans (V12.gasSteps_fallback input hk)

def gasSteps_miss14 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 14) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 14 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_hit11 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 15) (h : Hit11 input) :
    Challenge.EvmProof.GasSteps (init input) (V11.State.returnedState input) :=
  (gasSteps_bucket input 15 89 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1532 (by rfl))).trans (V11.gasSteps_match input h)

def gasSteps_miss15 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 15) (hk : ¬ Hit11 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 15 89 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1532 (by rfl))).trans (V11.gasSteps_fallback input hk)

def gasSteps_miss16 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 16) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 16 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss17 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 17) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 17 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss18 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 18) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 18 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss19 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 19) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 19 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_hit2 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 20) (hw : MachineState.readWord input 64 ≠ UInt256.ofNat 0) (h : Hit2 input) :
    Challenge.EvmProof.GasSteps (init input) (V2.State.returnedState input) :=
  ((gasSteps_bucket input 20 47 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1089 (by rfl))).trans (V2.gasSteps_pretest_notTaken input hw)).trans (V2.gasSteps_match input h)

def gasSteps_miss20a (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 20) (hw : MachineState.readWord input 64 ≠ UInt256.ofNat 0) (hk : ¬ Hit2 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  ((gasSteps_bucket input 20 47 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1089 (by rfl))).trans (V2.gasSteps_pretest_notTaken input hw)).trans (V2.gasSteps_fallback input hk)

/-- Zero modulus length routes to the appended empty-return block. -/
def gasSteps_empty (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 20) (hw : MachineState.readWord input 64 = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps (init input) (EmptyReturn.returnedState input) :=
  ((gasSteps_bucket input 20 47 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1089 (by rfl))).trans (V2.gasSteps_pretest_taken input hw)).trans
    (sound EmptyReturn.returnPath rfl (EmptyReturn.run_return input) rfl rfl deployAddress_not_precompile)

def gasSteps_hit1 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 21) (h : Hit1 input) :
    Challenge.EvmProof.GasSteps (init input) (V1.State.returnedState input) :=
  (gasSteps_bucket input 21 45 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1065 (by rfl))).trans (V1.gasSteps_match input h)

def gasSteps_miss21 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 21) (hk : ¬ Hit1 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 21 45 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1065 (by rfl))).trans (V1.gasSteps_fallback input hk)

def gasSteps_hit7 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 22) (h : Hit7 input) :
    Challenge.EvmProof.GasSteps (init input) (V7.State.returnedState input) :=
  (gasSteps_bucket input 22 64 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1307 (by rfl))).trans (V7.gasSteps_match input h)

def gasSteps_miss22 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 22) (hk : ¬ Hit7 input) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 22 64 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1307 (by rfl))).trans (V7.gasSteps_fallback input hk)

def gasSteps_miss23 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 23) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 23 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss24 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 24) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 24 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

def gasSteps_miss25 (input : ByteArray) (hsize : input.size < 2 ^ 256) (hr : input.size % 26 = 25) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1196) :=
  (gasSteps_bucket input 25 43 hsize hr (by decide +kernel) (by norm_num)
      (Artifact.isValidJumpDest_index 1005 (by rfl))).trans (gasSteps_stub input)

end Challenge.Modexp.Submission.Proofs.Memo.Main
