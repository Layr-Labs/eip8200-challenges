import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierDispatch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Verifier end to end

`gasSteps_verify_hit` composes dispatch, the verifier's hit run, and the
digest-table return into one `GasSteps` from `patternedEntry` to the returned
state.  `gasSteps_verify_miss` composes dispatch and the miss run into
`GasSteps` to the fallback state.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar PatternedScanState PatternedScanTrace
open VerifierData VerifierRun VerifierFinish VerifierLogic VerifierDispatch

/-- Hit: dispatch to the verifier, run it to the digest entry, store and
return. -/
def gasSteps_verify_hit (n : Nat) (input : ByteArray)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32)
    (hsize : input.size = n)
    (hacc : verifyAcc input n = 0) :
    GasSteps (patternedEntry input) (vReturned n input) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact (sound dispatchPath56 (run_dispatch56 input hsize)).trans
        ((sound verifyPath56 (run_verify56_hit input hacc)).trans
          (gasSteps_vreturn 56 input (by decide) hsize))
    | exact (sound dispatchPath120 (run_dispatch120 input hsize)).trans
        ((sound verifyPath120 (run_verify120_hit input hacc)).trans
          (gasSteps_vreturn 120 input (by decide) hsize))
    | exact (sound dispatchPath64 (run_dispatch64 input hsize)).trans
        ((sound verifyPath64 (run_verify64_hit input hacc)).trans
          (gasSteps_vreturn 64 input (by decide) hsize))
    | exact (sound dispatchPath65 (run_dispatch65 input hsize)).trans
        ((sound verifyPath65 (run_verify65_hit input hacc)).trans
          (gasSteps_vreturn 65 input (by decide) hsize))
    | exact (sound dispatchPath128 (run_dispatch128 input hsize)).trans
        ((sound verifyPath128 (run_verify128_hit input hacc)).trans
          (gasSteps_vreturn 128 input (by decide) hsize))
    | exact (sound dispatchPath63 (run_dispatch63 input hsize)).trans
        ((sound verifyPath63 (run_verify63_hit input hacc)).trans
          (gasSteps_vreturn 63 input (by decide) hsize))
    | exact (sound dispatchPath119 (run_dispatch119 input hsize)).trans
        ((sound verifyPath119 (run_verify119_hit input hacc)).trans
          (gasSteps_vreturn 119 input (by decide) hsize))
    | exact (sound dispatchPath55 (run_dispatch55 input hsize)).trans
        ((sound verifyPath55 (run_verify55_hit input hacc)).trans
          (gasSteps_vreturn 55 input (by decide) hsize))
    | exact (sound dispatchPath256 (run_dispatch256 input hsize)).trans
        ((sound verifyPath256 (run_verify256_hit input hacc)).trans
          (gasSteps_vreturn 256 input (by decide) hsize))
    | exact (sound dispatchPath376 (run_dispatch376 input hsize)).trans
        ((sound verifyPath376 (run_verify376_hit input hacc)).trans
          (gasSteps_vreturn 376 input (by decide) hsize))
    | exact (sound dispatchPath1000 (run_dispatch1000 input hsize)).trans
        ((sound verifyPath1000 (run_verify1000_hit input hacc)).trans
          (gasSteps_vreturn 1000 input (by decide) hsize))
    | exact (sound dispatchPath1 (run_dispatch1 input hsize)).trans
        ((sound verifyPath1 (run_verify1_hit input hacc)).trans
          (gasSteps_vreturn 1 input (by decide) hsize))
    | exact (sound dispatchPath31 (run_dispatch31 input hsize)).trans
        ((sound verifyPath31 (run_verify31_hit input hacc)).trans
          (gasSteps_vreturn 31 input (by decide) hsize))
    | exact (sound dispatchPath32 (run_dispatch32 input hsize)).trans
        ((sound verifyPath32 (run_verify32_hit input hacc)).trans
          (gasSteps_vreturn 32 input (by decide) hsize))

/-- Miss: dispatch to the verifier, run it to the fallback. -/
def gasSteps_verify_miss (n : Nat) (input : ByteArray)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32)
    (hsize : input.size = n)
    (hacc : verifyAcc input n ≠ 0) :
    GasSteps (patternedEntry input) (fallbackState input) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact (sound dispatchPath56 (run_dispatch56 input hsize)).trans
        (sound verifyPath56 (run_verify56_miss input hacc))
    | exact (sound dispatchPath120 (run_dispatch120 input hsize)).trans
        (sound verifyPath120 (run_verify120_miss input hacc))
    | exact (sound dispatchPath64 (run_dispatch64 input hsize)).trans
        (sound verifyPath64 (run_verify64_miss input hacc))
    | exact (sound dispatchPath65 (run_dispatch65 input hsize)).trans
        (sound verifyPath65 (run_verify65_miss input hacc))
    | exact (sound dispatchPath128 (run_dispatch128 input hsize)).trans
        (sound verifyPath128 (run_verify128_miss input hacc))
    | exact (sound dispatchPath63 (run_dispatch63 input hsize)).trans
        (sound verifyPath63 (run_verify63_miss input hacc))
    | exact (sound dispatchPath119 (run_dispatch119 input hsize)).trans
        (sound verifyPath119 (run_verify119_miss input hacc))
    | exact (sound dispatchPath55 (run_dispatch55 input hsize)).trans
        (sound verifyPath55 (run_verify55_miss input hacc))
    | exact (sound dispatchPath256 (run_dispatch256 input hsize)).trans
        (sound verifyPath256 (run_verify256_miss input hacc))
    | exact (sound dispatchPath376 (run_dispatch376 input hsize)).trans
        (sound verifyPath376 (run_verify376_miss input hacc))
    | exact (sound dispatchPath1000 (run_dispatch1000 input hsize)).trans
        (sound verifyPath1000 (run_verify1000_miss input hacc))
    | exact (sound dispatchPath1 (run_dispatch1 input hsize)).trans
        (sound verifyPath1 (run_verify1_miss input hacc))
    | exact (sound dispatchPath31 (run_dispatch31 input hsize)).trans
        (sound verifyPath31 (run_verify31_miss input hacc))
    | exact (sound dispatchPath32 (run_dispatch32 input hsize)).trans
        (sound verifyPath32 (run_verify32_miss input hacc))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierCorrect
