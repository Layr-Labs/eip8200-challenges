import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

/-!
# Concrete trace for the direct RR-leading helper

This module is the sole bridge between the symbolic helper development and
the exact submitted Artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTrace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory
open RrLeadingPaths

set_option linter.unusedSimpArgs false in
theorem run_helper_small (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hsmall : n ≤ 3) (_hactive : 298 ≤ template.activeWords.toNat)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : template.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock helperSmallPath
      (entryState template mem n bsize esize msize) =
      some (exitState template mem n bsize esize msize) := by
  have hcounter : directCounter n = 0 :=
    directCounter_of_le_three hn2 hsmall
  have hn : n < 2 ^ 256 := by
    have hpow : 32 < 2 ^ 256 := by norm_num
    omega
  have hnot : ¬ 3 < n := by omega
  have hlt : UInt256.lt (UInt256.ofNat 3) (UInt256.ofNat n) =
      UInt256.ofNat 0 := by
    rw [wordLt_ofNat 3 n (by norm_num) hn]
    simp [ltWord, hnot]
  simp (config := { maxSteps := 600000 })
    [helperSmallPath, helperPrefixPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, exitState, outer, copiedMemory, copiedActiveWords,
      loadActiveWords, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2, hrun, hcode, hsize, hsmall, hlt,
      sizeWord_toNat hn32, helperPC, jump5323, jump1569, hcounter,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_helper_large (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hlarge : 3 < n) (_hactive : 298 ≤ template.activeWords.toNat)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : template.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock helperLargePath
      (entryState template mem n bsize esize msize) =
      some (exitState template mem n bsize esize msize) := by
  have hn : n < 2 ^ 256 := by
    have hpow : 32 < 2 ^ 256 := by norm_num
    omega
  have hlt : UInt256.lt (UInt256.ofNat 3) (UInt256.ofNat n) =
      UInt256.ofNat 1 := by
    rw [wordLt_ofNat 3 n (by norm_num) hn]
    simp [ltWord, hlarge]
  simp (config := { maxSteps := 600000 })
    [helperLargePath, helperPrefixPath, fallbackPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, exitState, outer, copiedMemory, copiedActiveWords,
      loadActiveWords, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2, hrun, hcode, hsize, hlarge, hlt,
      sizeWord_toNat hn32, helperPC, fallbackPC, jump5323, jump1569,
      counterWord n hn32,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]


def gasSteps_helper (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ template.activeWords.toNat)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : template.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : template.fork = .Osaka) (hrun : template.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      template.executionEnv.precompileConfig template.executionEnv.fork
      template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entryState template mem n bsize esize msize)
      (exitState template mem n bsize esize msize) := by
  by_cases hsmall : n ≤ 3
  · exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka helperSmallPath hcode hfork
      (run_helper_small template mem n bsize esize msize hn2 hn32 hsmall
        hactive hsize hcode hrun) hrun hnp
  · have hlarge : 3 < n := by omega
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka helperLargePath hcode hfork
      (run_helper_large template mem n bsize esize msize hn2 hn32 hlarge
        hactive hsize hcode hrun) hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTrace
