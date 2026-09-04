import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreExecution
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreGas

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver
open Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreExecution
open Challenge.Modexp.Submission.Proofs.Montgomery.CoreState

private theorem state_code (s : State)
    (hcode : s.executionEnv.code = submissionBytecode) :
    s.executionEnv.code = Artifact.submissionArtifact.code := by
  simpa [Artifact.submissionArtifact] using hcode

private theorem first_frame (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    (firstReturned s i a b out modulus n np ret
      (MachineState.readWord s.memory (a.toNat + 32 * i)) rest).stack =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame i a b out modulus n np ret rest := by
  simp [firstReturned, MontgomeryWordBlock.returned, frame,
    Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame]

private theorem first_pc (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    (firstReturned s i a b out modulus n np ret
      (MachineState.readWord s.memory (a.toNat + 32 * i)) rest).pc =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kFirst := by
  rfl

private theorem second_frame (s : State) (i : Nat)
    (a b out modulus n np ret q : UInt256) (rest : List UInt256) :
    (secondReturned s i a b out modulus n np ret q rest).stack =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame i a b out modulus n np ret rest := by
  simp [secondReturned, MontgomeryWordBlock.returned, frame,
    Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame]

private theorem second_pc (s : State) (i : Nat)
    (a b out modulus n np ret q : UInt256) (rest : List UInt256) :
    (secondReturned s i a b out modulus n np ret q rest).pc =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kSecond := by
  rfl

private theorem shifted_frame (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    (shiftCopied s i a b out modulus n np ret rest).stack =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame i a b out modulus n np ret rest := by
  simp [shiftCopied, BigHelpers.copyReturned, frame,
    Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame]

private theorem shifted_pc (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    (shiftCopied s i a b out modulus n np ret rest).pc =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kShift := by
  rfl

def gasSteps_iteration (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hn : n.toNat ≤ 32) (hi : i < n.toNat)
    (hcap : rest.length + 8 < 1000)
    (haddr : a.toNat + 32 * i < 2 ^ 256)
    (hbFit : b.toNat + 32 * n.toNat < B)
    (hmodFit : modulus.toNat + 32 * n.toNat < B)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loop s i a b out modulus n np ret rest)
      (loop (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step s a b modulus n.toNat i np ret rest)
        (i + 1) a b out modulus n np ret rest) := by
  let digit : UInt256 := MachineState.readWord s.memory (a.toNat + 32 * i)
  let first : State :=
    firstReturned s i a b out modulus n np ret digit rest
  have hfirstCode : first.executionEnv.code = submissionBytecode := by
    simpa [first, digit, firstReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.bodyEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop] using hcode
  have hfirstFork : first.fork = .Osaka := by
    simpa [first, digit, firstReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.bodyEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop, State.fork] using hfork
  have hfirstRun : first.halt = .Running := by
    simpa [first, digit, firstReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.bodyEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop] using hrun
  have hfirstNp :
      Precompile.isPrecompileWithConfig first.executionEnv.precompileConfig
        first.executionEnv.fork first.executionEnv.codeAddr = false := by
    simpa [first, digit, firstReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.bodyEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop] using hnp
  have hsecondCallRun :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.secondCallPath first =
        some (secondEntry first i a b out modulus n np ret
          (MachineState.readWord first.memory scratch.toNat * np) rest) := by
    simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.secondEntry, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.secondEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loadState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.touch, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.touch,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame, frame, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.scratch, scratch,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kSecond, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.kSecond] using
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_secondCall first i a b out modulus n np ret digit
        (MachineState.readWord first.memory scratch.toNat * np) rest hcap
        (by simpa [first, digit] using first_frame s i a b out modulus n np ret rest)
        (by simpa [first, digit] using first_pc s i a b out modulus n np ret rest)
        (by rfl) hn hfirstCode hfirstRun)
  have gsecondCall :
      GasSteps first
        (secondEntry first i a b out modulus n np ret
          (MachineState.readWord first.memory scratch.toNat * np) rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.secondCallPath (state_code first hfirstCode)
      hfirstFork hsecondCallRun hfirstRun hfirstNp
  let q : UInt256 := MachineState.readWord first.memory scratch.toNat * np
  let second : State := secondReturned first i a b out modulus n np ret q rest
  have hsecondCode : second.executionEnv.code = submissionBytecode := by
    simpa [second, q, secondReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState] using hfirstCode
  have hsecondFork : second.fork = .Osaka := by
    simpa [second, q, secondReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState, State.fork] using hfirstFork
  have hsecondRun : second.halt = .Running := by
    simpa [second, q, secondReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState] using hfirstRun
  have hsecondNp :
      Precompile.isPrecompileWithConfig second.executionEnv.precompileConfig
        second.executionEnv.fork second.executionEnv.codeAddr = false := by
    simpa [second, q, secondReturned, MontgomeryWordBlock.returned,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loadState] using hfirstNp
  have gsecondWord := gasSteps_secondWord first i a b out modulus n np ret q rest
    hcap hn hmodFit hfirstCode hfirstFork hfirstRun hfirstNp
  have hshiftCallRun :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftCallPath second =
        some (shiftEntry second i a b out modulus n np ret rest) := by
    simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftEntry, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.shiftEntry,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame, frame, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.scratch, scratch,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.kShift, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.kShift] using
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_shiftCall second i a b out modulus n np ret rest hcap
        (by simpa [second, q] using second_frame first i a b out modulus n np ret q rest)
        (by simpa [second, q] using second_pc first i a b out modulus n np ret q rest)
        hn hsecondCode hsecondRun)
  have gshiftCall :
      GasSteps second (shiftEntry second i a b out modulus n np ret rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftCallPath (state_code second hsecondCode)
      hsecondFork hshiftCallRun hsecondRun hsecondNp
  let shifted : State := shiftCopied second i a b out modulus n np ret rest
  have hshiftedCode : shifted.executionEnv.code = submissionBytecode := by
    simpa [shifted, shiftCopied, BigHelpers.copyReturned] using hsecondCode
  have hshiftedFork : shifted.fork = .Osaka := by
    simpa [shifted, shiftCopied, BigHelpers.copyReturned, State.fork] using hsecondFork
  have hshiftedRun : shifted.halt = .Running := by
    simpa [shifted, shiftCopied, BigHelpers.copyReturned] using hsecondRun
  have hshiftedNp :
      Precompile.isPrecompileWithConfig shifted.executionEnv.precompileConfig
        shifted.executionEnv.fork shifted.executionEnv.codeAddr = false := by
    simpa [shifted, shiftCopied, BigHelpers.copyReturned] using hsecondNp
  have hshiftZeroRun :
      Stepper.runLocatedBlock Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftZeroPath shifted =
        some (loop (zeroState shifted (scratch.toNat + 32 * (n.toNat + 1)))
          (i + 1) a b out modulus n np ret rest) := by
    simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftZeroState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.loop,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.zeroState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.zeroState, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.touch,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.touch, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame, frame,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.scratch, scratch] using
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.run_shiftZero shifted i a b out modulus n np ret rest hcap
        (by simpa [shifted] using shifted_frame second i a b out modulus n np ret rest)
        (by simpa [shifted] using shifted_pc second i a b out modulus n np ret rest)
        hn hshiftedCode hshiftedRun)
  have gshiftZero :
      GasSteps shifted
        (loop (zeroState shifted (scratch.toNat + 32 * (n.toNat + 1)))
          (i + 1) a b out modulus n np ret rest) :=
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.shiftZeroPath (state_code shifted hshiftedCode)
      hshiftedFork hshiftZeroRun hshiftedRun hshiftedNp
  have hchain :
      GasSteps (loop s i a b out modulus n np ret rest)
        (runtimeStep s i a b out modulus n np ret rest) := by
    exact (gasSteps_guard s i a b out modulus n np ret rest hcap hi hcode hfork hrun hnp).trans <|
      (gasSteps_firstCall s i a b out modulus n np ret digit rest hcap haddr
        (by rfl) hcode hfork hrun hnp).trans <|
      (gasSteps_firstWord s i a b out modulus n np ret digit rest hcap hn hbFit
        hcode hfork hrun hnp).trans <|
      gsecondCall.trans <|
      gsecondWord.trans <|
      gshiftCall.trans <|
      (gasSteps_shiftCopy second i a b out modulus n np ret rest hcap hn
        hsecondCode hsecondFork hsecondRun hsecondNp).trans <|
      gshiftZero
  exact GasSteps.cast hchain rfl (runtimeStep_step s i a b out modulus n np ret rest)

private theorem progress_code (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256) (rest : List UInt256) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).executionEnv.code =
      submissionBytecode := by
  rw [progress_executionEnv]
  exact hcode

private theorem progress_fork (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256) (rest : List UInt256) (i : Nat)
    (hfork : s.fork = .Osaka) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).fork = .Osaka := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreExecution.progress_fork]
  exact hfork

private theorem progress_run (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256) (rest : List UInt256) (i : Nat)
    (hrun : s.halt = .Running) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).halt = .Running := by
  rw [progress_halt]
  exact hrun

private theorem progress_np (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256) (rest : List UInt256) (i : Nat)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Precompile.isPrecompileWithConfig
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).executionEnv.precompileConfig
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).executionEnv.fork
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).executionEnv.codeAddr = false := by
  rw [progress_executionEnv]
  exact hnp

def gasSteps_loop (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hn : n.toNat ≤ 32) (hcap : rest.length + 8 < 1000)
    (haFit : a.toNat + 32 * n.toNat < B)
    (hbFit : b.toNat + 32 * n.toNat < B)
    (hmodFit : modulus.toNat + 32 * n.toNat < B)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (modelLoop s a b out modulus n np ret rest 0)
      (modelLoop s a b out modulus n np ret rest n.toNat) := by
  exact GasSteps.iterateBounded
    (I := fun i => modelLoop s a b out modulus n np ret rest i) n.toNat
    (fun i hi => by
      let p := Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n.toNat np ret rest i
      have hpCode : p.executionEnv.code = submissionBytecode := by
        simpa [p] using progress_code s a b modulus n.toNat np ret rest i hcode
      have hpFork : p.fork = .Osaka := by
        simpa [p] using progress_fork s a b modulus n.toNat np ret rest i hfork
      have hpRun : p.halt = .Running := by
        simpa [p] using progress_run s a b modulus n.toNat np ret rest i hrun
      have hpNp :
          Precompile.isPrecompileWithConfig p.executionEnv.precompileConfig
            p.executionEnv.fork p.executionEnv.codeAddr = false := by
        simpa [p] using progress_np s a b modulus n.toNat np ret rest i hnp
      have hiLe : i ≤ n.toNat := Nat.le_of_lt hi
      have haddrB : a.toNat + 32 * i < B := by omega
      have haddr : a.toNat + 32 * i < 2 ^ 256 := by
        simpa [B, radix] using haddrB
      have hbody := gasSteps_iteration p i a b out modulus n np ret rest hn hi hcap
        haddr hbFit hmodFit hpCode hpFork hpRun hpNp
      simpa [modelLoop, p, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress] using hbody)

def gasSteps_core (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hn : n.toNat ≤ 32) (hcap : rest.length + 8 < 1000)
    (haFit : a.toNat + 32 * n.toNat < B)
    (hbFit : b.toNat + 32 * n.toNat < B)
    (hmodFit : modulus.toNat + 32 * n.toNat < B)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (entry s a b out modulus n np ret rest)
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish.finishReturned
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n.toNat np ret rest n.toNat)
        a b out modulus n np ret rest) := by
  let pN : State :=
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n.toNat np ret rest n.toNat
  have hpNCode : pN.executionEnv.code = submissionBytecode := by
    simpa [pN] using progress_code s a b modulus n.toNat np ret rest n.toNat hcode
  have hpNFork : pN.fork = .Osaka := by
    simpa [pN] using progress_fork s a b modulus n.toNat np ret rest n.toNat hfork
  have hpNRun : pN.halt = .Running := by
    simpa [pN] using progress_run s a b modulus n.toNat np ret rest n.toNat hrun
  have hpNNp :
      Precompile.isPrecompileWithConfig pN.executionEnv.precompileConfig
        pN.executionEnv.fork pN.executionEnv.codeAddr = false := by
    simpa [pN] using progress_np s a b modulus n.toNat np ret rest n.toNat hnp
  have gclear := gasSteps_clearPrefix s a b out modulus n np ret rest hn hcap hcode hfork hrun hnp
  have gloop := gasSteps_loop s a b out modulus n np ret rest hn hcap haFit hbFit hmodFit
    hcode hfork hrun hnp
  have gguard := gasSteps_guard_finish pN a b out modulus n np ret rest hcap
    hpNCode hpNFork hpNRun hpNNp
  have gfinish :
      GasSteps (finish pN a b out modulus n np ret rest)
        (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish.finishReturned pN a b out modulus n np ret rest) := by
    simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish.finishEntry, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.finish,
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths.frame, frame] using
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish.gasSteps_finish pN a b out modulus n np ret rest hcap hn
        hpNCode hpNFork hpNRun hpNNp hret)
  exact gclear.trans <| gloop.trans <| gguard.trans <| gfinish

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreGas
