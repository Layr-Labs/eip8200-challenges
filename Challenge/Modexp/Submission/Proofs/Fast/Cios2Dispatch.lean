import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# CIOS2 size dispatcher

The appended dispatcher observes the existing `S32` setup word.  Widths four
and eight limbs enter the specialized block; every other width retains the
original MONPRO entry at pc 1939.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def dispatchState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4202
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def specializedEntryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4225
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

theorem jumpDest4057 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4202 = true := by
  exact Artifact.isValidJumpDest_index 2942 (by rfl)

theorem jumpDest4080 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4225 = true := by
  exact Artifact.isValidJumpDest_index 2956 (by rfl)

private theorem activeWords9344 (s : State) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := by
  have hnat : MachineState.activeWordsAfter s.activeWords.toNat 9344 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    simp only [show (32 : Nat) ≠ 0 by decide, if_false]
    exact Nat.max_eq_left (by omega)
  rw [hnat]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

private theorem toNat_ne_of_ne {a b : UInt256} (h : a ≠ b) :
    a.toNat ≠ b.toNat := by
  intro hab
  apply h
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UInt256.toNat] at hab
      congr
      exact Fin.ext hab

set_option linter.unusedSimpArgs false in
theorem run_dispatch4 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat 128) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2DispatchGuard
      (dispatchState s mem pa pb pdst ret rest) =
      some (specializedEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h4080 : (4225 : UInt256).toNat = 4225 := by decide
  have h4080' : (4225 : UInt256) = UInt256.ofNat 4225 := by decide
  have hcond128 :
      ((UInt256.ofNat 256).eq (UInt256.ofNat 128)).toNat |||
        ((UInt256.ofNat 128).eq (UInt256.ofNat 128)).toNat ≠ 0 := by decide
  simp (config := { maxSteps := 400000 })
    [cios2DispatchGuard, Cios2Paths.Dispatch.dispatchPC, Cios2Paths.Dispatch.startIndex,
      Cios2Paths.Dispatch.opAt, Cios2Paths.Dispatch.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      dispatchState, specializedEntryState, hc4, hc5, hc6, hc7, hrun, hcode,
      hs32, hcond128, activeWords9344 s hact, h4080, h4080', jumpDest4080,
      UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_dispatch8 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2DispatchGuard
      (dispatchState s mem pa pb pdst ret rest) =
      some (specializedEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h4080 : (4225 : UInt256).toNat = 4225 := by decide
  have h4080' : (4225 : UInt256) = UInt256.ofNat 4225 := by decide
  have hcond256 :
      ((UInt256.ofNat 256).eq (UInt256.ofNat 256)).toNat |||
        ((UInt256.ofNat 128).eq (UInt256.ofNat 256)).toNat ≠ 0 := by decide
  simp (config := { maxSteps := 400000 })
    [cios2DispatchGuard, Cios2Paths.Dispatch.dispatchPC, Cios2Paths.Dispatch.startIndex,
      Cios2Paths.Dispatch.opAt, Cios2Paths.Dispatch.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      dispatchState, specializedEntryState, hc4, hc5, hc6, hc7, hrun, hcode,
      hs32, hcond256, activeWords9344 s hact, h4080, h4080', jumpDest4080,
      UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_dispatchFallback (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (h128 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2Dispatch
      (dispatchState s mem pa pb pdst ret rest) =
      some (mpEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h1939 : (1939 : UInt256).toNat = 1939 := by decide
  have h1939' : (1939 : UInt256) = UInt256.ofNat 1939 := by decide
  have h128Nat : (UInt256.ofNat 128).toNat ≠
      (MachineState.readWord mem 9344).toNat :=
    toNat_ne_of_ne h128.symm
  have h256Nat : (UInt256.ofNat 256).toNat ≠
      (MachineState.readWord mem 9344).toNat :=
    toNat_ne_of_ne h256.symm
  have hcond :
      ((UInt256.ofNat 256).eq (MachineState.readWord mem 9344)).toNat |||
        ((UInt256.ofNat 128).eq (MachineState.readWord mem 9344)).toNat = 0 := by
    rw [UInt256.eq, UInt256.eq]
    simp only [if_neg h256Nat, if_neg h128Nat]
    decide
  simp (config := { maxSteps := 400000 })
    [cios2Dispatch, cios2DispatchGuard,
      Cios2Paths.Dispatch.dispatchPC, Cios2Paths.Dispatch.startIndex,
      Cios2Paths.Dispatch.opAt, Cios2Paths.Dispatch.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      dispatchState, mpEntryState, hc4, hc5, hc6, hc7, hrun, hcode,
      h128, h256, h128Nat, h256Nat, hcond, activeWords9344 s hact,
      h1939, h1939', jumpDest1939,
      UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

opaque gasSteps_dispatch4 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat 128) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (specializedEntryState s mem pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2DispatchGuard hcode hfork
    (run_dispatch4 s mem pa pb pdst ret rest hcap hrun hcode hact hs32) hrun hnp

opaque gasSteps_dispatch8 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat 256) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (specializedEntryState s mem pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2DispatchGuard hcode hfork
    (run_dispatch8 s mem pa pb pdst ret rest hcap hrun hcode hact hs32) hrun hnp

opaque gasSteps_dispatchFallback (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (h128 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 256) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2Dispatch hcode hfork
    (run_dispatchFallback s mem pa pb pdst ret rest hcap hrun hcode hact h128 h256)
    hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
