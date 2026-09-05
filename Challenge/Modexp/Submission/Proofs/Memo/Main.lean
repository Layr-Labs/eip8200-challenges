import Challenge.Modexp.Submission.Proofs.Bytecode.MainGas
import Challenge.Modexp.Submission.Proofs.Memo.Dispatch

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/- Modified September 5, 2026. Apache-2.0. Complete proof-source attempt.
   Reuses the 8d4880 crown's unchanged absolute-alignment dispatcher. -/
namespace Challenge.Modexp.Submission.Proofs.Memo.Main
open EvmSemantics EvmSemantics.EVM
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
      s.executionEnv.codeAddr = false) : Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

abbrev init (input : ByteArray) : State := initialState submissionBytecode input 0

def gasSteps_bucket (input : ByteArray) (r e : Nat) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = r)
    (he : UInt256.byteAt (UInt256.ofNat r) (UInt256.ofNat 19978037702372708034821103941948154258537848763203913937270760471517377276715) = UInt256.ofNat e)
    (he255 : e ≤ 255)
    (hjump : Decode.isValidJumpDest submissionBytecode (32 * e) = true) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input (32 * e)) :=
  ((Bytecode.Main.gasSteps_entryHop input).trans
    (sound prefixPath rfl (run_prefix input r e hsize hr he he255) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_jump input (32 * e) (by omega) hjump) rfl rfl deployAddress_not_precompile)

def gasSteps_stub (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Bytecode.Main.trampolineState input 1376)
      (Bytecode.Main.trampolineState input 1196) :=
  (sound stubPrefixPath rfl (run_stub_prefix input) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_stub_jump input) rfl rfl deployAddress_not_precompile)

def bucket0 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 0) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1408) :=
  gasSteps_bucket input 0 44 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1035 (by rfl))

def bucket1 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 1) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 1 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket2 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 2) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 2 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket3 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 3) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 3 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket4 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 4) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1984) :=
  gasSteps_bucket input 4 62 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1321 (by rfl))

def bucket5 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 5) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1824) :=
  gasSteps_bucket input 5 57 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1271 (by rfl))

def bucket6 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 6) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1728) :=
  gasSteps_bucket input 6 54 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1219 (by rfl))

def bucket7 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 7) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 2240) :=
  gasSteps_bucket input 7 70 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1426 (by rfl))

def bucket8 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 8) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 8 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket9 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 9) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 9 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket10 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 10) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 2432) :=
  gasSteps_bucket input 10 76 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1477 (by rfl))

def bucket11 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 11) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 11 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket12 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 12) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 12 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket13 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 13) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 3392) :=
  gasSteps_bucket input 13 106 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1678 (by rfl))

def bucket14 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 14) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 14 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket15 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 15) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 2848) :=
  gasSteps_bucket input 15 89 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1576 (by rfl))

def bucket16 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 16) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 16 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket17 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 17) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 17 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket18 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 18) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 18 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket19 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 19) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 19 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket20 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 20) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1536) :=
  gasSteps_bucket input 20 48 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1116 (by rfl))

def bucket21 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 21) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1440) :=
  gasSteps_bucket input 21 45 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1065 (by rfl))

def bucket22 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 22) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 2112) :=
  gasSteps_bucket input 22 66 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1374 (by rfl))

def bucket23 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 23) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 23 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket24 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 24) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 24 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

def bucket25 (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = 25) :
    Challenge.EvmProof.GasSteps (init input) (Bytecode.Main.trampolineState input 1376) :=
  gasSteps_bucket input 25 43 hsize hr (by decide +kernel) (by norm_num)
    (Artifact.isValidJumpDest_index 1005 (by rfl))

end Challenge.Modexp.Submission.Proofs.Memo.Main
