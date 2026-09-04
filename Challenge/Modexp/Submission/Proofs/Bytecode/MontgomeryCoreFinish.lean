import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreState

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

abbrev submissionBytecode : ByteArray := Challenge.Modexp.submissionBytecode
abbrev scratch : UInt256 := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.scratch
abbrev kFinish : UInt256 := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kFinish
abbrev kReduce : UInt256 := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kReduce
abbrev kDone : UInt256 := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kDone
abbrev frame := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame

def finishEntry (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1736
           stack := frame n.toNat a b out modulus n np ret rest }

def finishReturned (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf s out modulus n.toNat
      kReduce (frame n.toNat a b out modulus n np ret rest) kDone
      (frame n.toNat a b out modulus n np ret rest) with
      pc := ret
      stack := rest }

private theorem jump1763 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1763 = true := by
  have hpc : Artifact.instructionPC 1314 = 1763 := by decide
  simpa [hpc, submissionBytecode] using (Artifact.isValidJumpDest_index 1314 (by rfl))

private theorem jump1777 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1777 = true := by
  have hpc : Artifact.instructionPC 1322 = 1777 := by decide
  simpa [hpc, submissionBytecode] using (Artifact.isValidJumpDest_index 1322 (by rfl))

def gasSteps_finish (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000)
    (hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps
      (finishEntry s a b out modulus n np ret rest)
      (finishReturned s a b out modulus n np ret rest) := by
  let saved := frame n.toNat a b out modulus n np ret rest
  let entry := finishEntry s a b out modulus n np ret rest
  let high := MachineState.readWord s.memory (scratch.toNat + 32 * n.toNat)
  let loaded := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState entry (scratch.toNat + 32 * n.toNat)
  let reduced := MontgomeryReduceBlock.reduceReturned loaded scratch modulus high n.toNat kReduce saved
  let copied := BigHelpers.copyReturned reduced out scratch n.toNat kDone saved

  have hsavedCap : saved.length < 1000 := by
    change rest.length + 8 < 1000
    omega
  have hcopyCap : saved.length < 1016 := by
    change rest.length + 8 < 1016
    omega
  have hn256 : n.toNat < 2 ^ 256 := by
    exact n.val.isLt

  have hentryStack : entry.stack = saved := by
    rfl
  have hentryPC : entry.pc = kFinish := by
    rfl
  have hentryCode : entry.executionEnv.code = submissionBytecode := by
    simpa [entry, finishEntry] using hcode
  have hentryFork : entry.fork = .Osaka := by
    simpa [entry, finishEntry] using hfork
  have hentryRun : entry.halt = .Running := by
    simpa [entry, finishEntry] using hrun
  have hentryNp :
      Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig entry.executionEnv.fork
        entry.executionEnv.codeAddr = false := by
    simpa [entry, finishEntry] using hnp
  have hhigh : high = MachineState.readWord entry.memory
      (scratch.toNat + 32 * n.toNat) := by
    rfl

  have hreduceTrace :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceCallPath entry =
        some (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceEntry entry a b out modulus n np ret high rest) := by
    exact Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_reduceCall entry a b out modulus n np ret high rest hcap
      hentryStack hentryPC
      hhigh hn hentryCode hentryRun
  have gReduceCall : GasSteps entry
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceEntry entry a b out modulus n np ret high rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceCallPath hentryCode hentryFork hreduceTrace hentryRun hentryNp

  have hloadedCode : loaded.executionEnv.code = submissionBytecode := by
    simpa [loaded, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState] using hentryCode
  have hloadedFork : loaded.fork = .Osaka := by
    simpa [loaded, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState] using hentryFork
  have hloadedRun : loaded.halt = .Running := by
    simpa [loaded, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState] using hentryRun
  have hloadedNp :
      Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig loaded.executionEnv.fork
        loaded.executionEnv.codeAddr = false := by
    simpa [loaded, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState] using hentryNp
  have hreduceTraceCap : saved.length < 1000 := hsavedCap
  have gRawReduce : GasSteps
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceEntry entry a b out modulus n np ret high rest) reduced := by
    simpa [reduced, loaded, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.reduceEntry] using
      (MontgomeryReduceBlock.gasSteps_reduce loaded scratch modulus high n.toNat kReduce saved
        hreduceTraceCap hn256 hloadedCode hloadedFork hloadedRun hloadedNp
        (by
          change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1763 = true
          exact jump1763))

  have hreduceStack : reduced.stack = saved := by
    rfl
  have hreducePC : reduced.pc = kReduce := by
    rfl
  have hreduceCode : reduced.executionEnv.code = submissionBytecode := by
    simpa [reduced, MontgomeryReduceBlock.reduceReturned] using hloadedCode
  have hreduceFork : reduced.fork = .Osaka := by
    simpa [reduced, MontgomeryReduceBlock.reduceReturned] using hloadedFork
  have hreduceRun : reduced.halt = .Running := by
    simpa [reduced, MontgomeryReduceBlock.reduceReturned] using hloadedRun
  have hreduceNp :
      Precompile.isPrecompileWithConfig reduced.executionEnv.precompileConfig reduced.executionEnv.fork
        reduced.executionEnv.codeAddr = false := by
    simpa [reduced, MontgomeryReduceBlock.reduceReturned] using hloadedNp

  have houtputTrace :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputCallPath reduced =
        some (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputEntry reduced a b out modulus n np ret rest) := by
    exact Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_outputCall reduced a b out modulus n np ret rest hcap
      hreduceStack hreducePC
      hn hreduceCode hreduceRun
  have gOutputCall : GasSteps reduced
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputEntry reduced a b out modulus n np ret rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputCallPath hreduceCode hreduceFork houtputTrace hreduceRun hreduceNp

  have gCopy : GasSteps
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputEntry reduced a b out modulus n np ret rest) copied := by
    simpa [copied, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.outputEntry] using
      (BigHelpers.gasSteps_copy reduced out scratch n.toNat kDone saved hcopyCap hn256
        hreduceCode hreduceFork hreduceRun hreduceNp
        (by
          change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1777 = true
          exact jump1777))

  have hcopyStack : copied.stack = saved := by
    rfl
  have hcopyPC : copied.pc = kDone := by
    rfl
  have hcopyCode : copied.executionEnv.code = submissionBytecode := by
    simpa [copied, BigHelpers.copyReturned] using hreduceCode
  have hcopyFork : copied.fork = .Osaka := by
    simpa [copied, BigHelpers.copyReturned] using hreduceFork
  have hcopyRun : copied.halt = .Running := by
    simpa [copied, BigHelpers.copyReturned] using hreduceRun
  have hcopyNp :
      Precompile.isPrecompileWithConfig copied.executionEnv.precompileConfig copied.executionEnv.fork
        copied.executionEnv.codeAddr = false := by
    simpa [copied, BigHelpers.copyReturned] using hreduceNp
  have hcleanupTrace :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanupPath copied =
        some (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanReturned copied a b out modulus n np ret rest) := by
    exact Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_cleanup copied n.toNat a b out modulus n np ret rest hcap
      hcopyStack hcopyPC
      hret hcopyCode hcopyRun
  have gCleanup : GasSteps copied
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanReturned copied a b out modulus n np ret rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanupPath hcopyCode hcopyFork hcleanupTrace hcopyRun hcopyNp

  have gAll : GasSteps entry (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanReturned copied a b out modulus n np ret rest) :=
    gReduceCall.trans <| gRawReduce.trans <| gOutputCall.trans <| gCopy.trans gCleanup
  have hout : (UInt256.ofNat out.toNat : UInt256) = out :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat out).symm
  have endpointEq :
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanReturned copied a b out modulus n np ret rest =
        finishReturned s a b out modulus n np ret rest := by
    dsimp only [finishReturned, finishEntry, saved, copied, reduced, loaded, high,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.cleanReturned, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.reducedLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.highWord,
      MontgomeryReduceBlock.reduceReturned, MontgomeryReduceBlock.reduceUseSub,
      BigHelpers.copyReturned]
    rw [hout]
    cases s
    rfl
  exact GasSteps.cast gAll rfl endpointEq

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish
