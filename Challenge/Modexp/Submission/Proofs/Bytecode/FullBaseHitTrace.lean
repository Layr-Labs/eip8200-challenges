import Challenge.Modexp.Submission.Proofs.Fast.FullBaseGuardCore
import Challenge.Modexp.Submission.Proofs.Fast.FullBasePaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Concrete located traces for the full-width-base hit branch

This module connects the small symbolic helper blocks to the submitted
artifact.  The inherited ADDMOD and Montgomery-product calls are deliberately
left as opaque boundaries; their existing subroutine contracts compose with
the three traces below.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FullBase

set_option linter.unusedSimpArgs false in
theorem run_redirect (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1195
      (redirectState s memory n bsize esize msize) =
      some (entryState s memory n bsize esize msize) := by
  simp [blk1195, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    redirectState, entryState, outer, hcode, hrun, jumpDest3606,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hb : bsize < 2 ^ 256) (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseGuard
      (entryState s memory n bsize esize msize) =
      some (if Matches memory n bsize
        then copyState s memory n bsize esize msize
        else fallbackState s memory n bsize esize msize) := by
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have haw : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have hnat : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [hnat]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hgw := guardWord_eq memory n bsize hn32 hb
  by_cases hm : Matches memory n bsize
  · rw [if_pos hm] at hgw
    have hc : ¬ UInt256.isTrue (guardWord memory n bsize) := by
      rw [hgw]
      decide
    change ¬(((UInt256.shiftRight (MachineState.readWord memory 0) (UInt256.ofNat 255)).land
      ((UInt256.ofNat bsize).eq (UInt256.ofNat (32 * n)))).isZero.isTrue) at hc
    simp (config := { maxSteps := 300000 })
      [blkFullBaseGuard, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        entryState, copyState, outer, hcode, hrun, hactive, hzeroNat, haw,
        fullBasePC, jumpDest3661, hm, guardWord, hc,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]
  · rw [if_neg hm] at hgw
    have hc : UInt256.isTrue (guardWord memory n bsize) := by
      rw [hgw]
      decide
    change (((UInt256.shiftRight (MachineState.readWord memory 0) (UInt256.ofNat 255)).land
      ((UInt256.ofNat bsize).eq (UInt256.ofNat (32 * n)))).isZero.isTrue) at hc
    simp (config := { maxSteps := 300000 })
      [blkFullBaseGuard, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        entryState, fallbackState, outer, hcode, hrun, hactive, hzeroNat, haw,
        fullBasePC, jumpDest3661, hm, guardWord, hc,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_copyAdd (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseCopyAdd
      (copyState s memory n bsize esize msize) =
      some (addCallState s memory input n bsize esize msize) := by
  rw [show Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseCopyAdd
      (copyState s memory n bsize esize msize) =
      runInstructions copyAddProgram (copyState s memory n bsize esize msize) by
    simp (config := { maxSteps := 300000 })
      [blkFullBaseCopyAdd, copyAddProgram, runInstructions, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        copyState, outer, hcode, hrun, fullBasePC, jumpDest2467,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]]
  exact Challenge.Modexp.Submission.Proofs.Fast.FullBase.run_copyAdd
    s memory input n bsize esize msize hn32 hactive hdata
      (by simpa [hcode] using jumpDest2467)

set_option linter.unusedSimpArgs false in
theorem run_afterAdd (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseAfterAdd
      (afterAddState s memory n bsize esize msize) =
      some (monproCallState s memory n bsize esize msize) := by
  rw [show Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseAfterAdd
      (afterAddState s memory n bsize esize msize) =
      runInstructions afterAddProgram (afterAddState s memory n bsize esize msize) by
    simp (config := { maxSteps := 300000 })
      [blkFullBaseAfterAdd, afterAddProgram, runInstructions, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        afterAddState, outer, hcode, hrun, fullBasePC, jumpDest1939,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]]
  exact Challenge.Modexp.Submission.Proofs.Fast.FullBase.run_afterAdd
    s memory n bsize esize msize (by simpa [hcode] using jumpDest1939)

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_redirect (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (redirectState s memory n bsize esize msize)
      (entryState s memory n bsize esize msize) :=
  sound blk1195 (run_redirect s memory n bsize esize msize hcode hrun)
    hcode hfork hrun hnp

def gasSteps_guard (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hb : bsize < 2 ^ 256) (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState s memory n bsize esize msize)
      (if Matches memory n bsize
        then copyState s memory n bsize esize msize
        else fallbackState s memory n bsize esize msize) :=
  sound blkFullBaseGuard
    (run_guard s memory n bsize esize msize hn32 hb hactive hcode hrun)
    hcode hfork hrun hnp

def gasSteps_copyAdd (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (copyState s memory n bsize esize msize)
      (addCallState s memory input n bsize esize msize) :=
  sound blkFullBaseCopyAdd
    (run_copyAdd s memory input n bsize esize msize hn32 hactive hdata hcode hrun)
    hcode hfork hrun hnp

def gasSteps_afterAdd (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (afterAddState s memory n bsize esize msize)
      (monproCallState s memory n bsize esize msize) :=
  sound blkFullBaseAfterAdd
    (run_afterAdd s memory n bsize esize msize hcode hrun)
    hcode hfork hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace
