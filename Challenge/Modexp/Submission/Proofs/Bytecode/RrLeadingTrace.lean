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
theorem run_helper (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (_hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (_hactive : 298 ≤ template.activeWords.toNat)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : template.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock helperPath
      (entryState template mem n bsize esize msize) =
      some (exitState template mem n bsize esize msize) := by
  simp (config := { maxSteps := 600000 })
    [helperPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, exitState, outer, copiedMemory, copiedActiveWords,
      loadActiveWords, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2, hrun, hcode, hsize,
      sizeWord_toNat hn32, counterWord n hn32, helperPC, jump1569,
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
      (exitState template mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka helperPath hcode hfork
      (run_helper template mem n bsize esize msize hn2 hn32 hactive hsize
        hcode hrun) hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTrace
