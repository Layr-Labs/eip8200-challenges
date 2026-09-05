import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreState

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreExecution

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver
open Challenge.Modexp.Submission.Proofs.Montgomery.CoreState

def modelLoop (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n.toNat np ret rest i)
    i a b out modulus n np ret rest

theorem modelLoop_zero (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) :
    modelLoop s a b out modulus n np ret rest 0 =
      Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.clearState s n.toNat) 0
        a b out modulus n np ret rest := by
  rfl

theorem modelLoop_frame (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (i : Nat) :
    (modelLoop s a b out modulus n np ret rest i).pc = kLoop ∧
      (modelLoop s a b out modulus n np ret rest i).stack =
        frame i a b out modulus n np ret rest := by
  simp [modelLoop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.kLoop]

theorem progress_executionEnv (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256)
    (rest : List UInt256) (i : Nat) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).executionEnv =
      s.executionEnv := by
  induction i with
  | zero => simp [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.clearLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf]
  | succ i ih =>
      simp only [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.firstLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.secondLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.shiftLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.copyLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.zeroLeaf]
      exact ih

theorem progress_halt (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256)
    (rest : List UInt256) (i : Nat) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).halt = s.halt := by
  induction i with
  | zero => simp [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.clearLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf]
  | succ i ih =>
      simp only [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.firstLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.secondLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.shiftLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.copyLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.zeroLeaf]
      exact ih

theorem progress_fork (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256)
    (rest : List UInt256) (i : Nat) :
    (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i).fork = s.fork := by
  induction i with
  | zero => simp [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.clearLeaf,
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf, State.fork]
  | succ i ih =>
      simp only [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.firstLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.secondLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.shiftLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.copyLeaf, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.zeroLeaf]
      exact ih

theorem modelLoop_code (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode) :
    (modelLoop s a b out modulus n np ret rest i).executionEnv.code =
      submissionBytecode := by
  simp only [modelLoop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop]
  rw [progress_executionEnv]
  exact hcode

theorem modelLoop_halt (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (i : Nat) (hrun : s.halt = .Running) :
      (modelLoop s a b out modulus n np ret rest i).halt = .Running := by
  simp only [modelLoop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop]
  rw [progress_halt]
  exact hrun

theorem modelLoop_fork (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (i : Nat) :
    (modelLoop s a b out modulus n np ret rest i).fork = s.fork := by
  simp only [modelLoop, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop]
  rw [progress_fork]

def gasSteps_clearPrefix (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hn : n.toNat ≤ 32)
    (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s a b out modulus n np ret rest)
      (modelLoop s a b out modulus n np ret rest 0) := by
  have hclear : Decode.isValidJumpDest submissionBytecode kClear.toNat = true := by
    have hpc : Artifact.instructionPC 1236 = 1641 := by decide
    have h := Artifact.isValidJumpDest_index 1236 (by rfl)
    rw [hpc] at h
    simpa [kClear] using h
  have hcountWord : n + 2 = UInt256.ofNat (n.toNat + 2) := by
    apply Word.word_ext
    rw [Word.word_toNat_add, Word.word_toNat_ofNat]
    have htwo : (2 : UInt256).toNat = 2 := by decide
    rw [htwo]
  have hclearSteps :
      GasSteps (clearCall s a b out modulus n np ret rest)
        (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
          (frame 0 a b out modulus n np ret rest)) := by
    simpa [clearCall, BigHelpers.clearEntry, frame, scratch, kClear,
      hcountWord, Word.ofNat_add_mod, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt] using
      (BigHelpers.gasSteps_clear s scratch (n.toNat + 2) kClear
        (frame 0 a b out modulus n np ret rest)
        (by simp [frame]; omega) (by omega) hcode hfork hrun hnp hclear)
  exact (gasSteps_entryClear s a b out modulus n np ret rest hcap hcode hfork
    hrun hnp).trans <|
    hclearSteps.trans <|
    (gasSteps_clearReturn s a b out modulus n np ret rest hn hcap hcode hfork
      hrun hnp)

def firstReturned (s : State) (i : Nat)
    (a b out modulus n np ret digit : UInt256) (rest : List UInt256) : State :=
  MontgomeryWordBlock.returned
    (loadState (bodyEntry s i a b out modulus n np ret rest)
      (a.toNat + 32 * i))
    scratch b digit n.toNat kFirst
    (frame i a b out modulus n np ret rest)

def secondReturned (s : State) (i : Nat)
    (a b out modulus n np ret q : UInt256) (rest : List UInt256) : State :=
  MontgomeryWordBlock.returned (loadState s scratch.toNat)
    scratch modulus q n.toNat kSecond
    (frame i a b out modulus n np ret rest)

private theorem jump_kFirst :
    Decode.isValidJumpDest submissionBytecode kFirst.toNat = true := by
  have hpc : Artifact.instructionPC 1260 = 1676 := by decide
  have h := Artifact.isValidJumpDest_index 1260 (by rfl)
  rw [hpc] at h
  simpa [kFirst] using h

private theorem jump_kSecond :
    Decode.isValidJumpDest submissionBytecode kSecond.toNat = true := by
  have hpc : Artifact.instructionPC 1273 = 1697 := by decide
  have h := Artifact.isValidJumpDest_index 1273 (by rfl)
  rw [hpc] at h
  simpa [kSecond] using h

private theorem jump_kShift :
    Decode.isValidJumpDest submissionBytecode kShift.toNat = true := by
  have hpc : Artifact.instructionPC 1282 = 1715 := by decide
  have h := Artifact.isValidJumpDest_index 1282 (by rfl)
  rw [hpc] at h
  simpa [kShift] using h

private theorem jump_kReduce :
    Decode.isValidJumpDest submissionBytecode kReduce.toNat = true := by
  have hpc : Artifact.instructionPC 1314 = 1763 := by decide
  have h := Artifact.isValidJumpDest_index 1314 (by rfl)
  rw [hpc] at h
  simpa [kReduce] using h

private theorem jump_kDone :
    Decode.isValidJumpDest submissionBytecode kDone.toNat = true := by
  have hpc : Artifact.instructionPC 1322 = 1777 := by decide
  have h := Artifact.isValidJumpDest_index 1322 (by rfl)
  rw [hpc] at h
  simpa [kDone] using h

def gasSteps_firstWord (s : State) (i : Nat)
    (a b out modulus n np ret digit : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000) (hn : n.toNat ≤ 32)
    (hbFit : b.toNat + 32 * n.toNat < Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.B)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (firstEntry (bodyEntry s i a b out modulus n np ret rest)
          i a b out modulus n np ret digit rest)
        (firstReturned s i a b out modulus n np ret digit rest) := by
  have hcode' :
      (loadState (bodyEntry s i a b out modulus n np ret rest)
        (a.toNat + 32 * i)).executionEnv.code = submissionBytecode := by
    simpa [loadState, bodyEntry, loop] using hcode
  have hfork' :
      (loadState (bodyEntry s i a b out modulus n np ret rest)
        (a.toNat + 32 * i)).fork = .Osaka := by
    simpa [loadState, bodyEntry, loop, State.fork] using hfork
  have hrun' :
      (loadState (bodyEntry s i a b out modulus n np ret rest)
        (a.toNat + 32 * i)).halt = .Running := by
    simpa [loadState, bodyEntry, loop] using hrun
  have hnp' :
      Precompile.isPrecompileWithConfig
          (loadState (bodyEntry s i a b out modulus n np ret rest)
            (a.toNat + 32 * i)).executionEnv.precompileConfig
          (loadState (bodyEntry s i a b out modulus n np ret rest)
            (a.toNat + 32 * i)).executionEnv.fork
          (loadState (bodyEntry s i a b out modulus n np ret rest)
            (a.toNat + 32 * i)).executionEnv.codeAddr = false := by
    simpa [loadState, bodyEntry, loop, State.fork] using hnp
  have hwordFit : b.toNat + 32 * n.toNat < 2 ^ 256 := by
    simpa [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.B, radix] using hbFit
  have htFit : scratch.toNat + 32 * n.toNat + 64 < 2 ^ 256 := by
    norm_num [scratch]
    omega
  have hframeCap : (frame i a b out modulus n np ret rest).length < 1000 := by
    simp [frame]
    omega
  simpa [firstEntry, firstReturned] using
    (MontgomeryWordBlock.gasSteps_word
      (loadState (bodyEntry s i a b out modulus n np ret rest)
        (a.toNat + 32 * i))
      scratch b digit n.toNat kFirst
      (frame i a b out modulus n np ret rest)
      hframeCap hn hwordFit htFit hcode' hfork' hrun' hnp' jump_kFirst)

def gasSteps_secondWord (s : State) (i : Nat)
    (a b out modulus n np ret q : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000) (hn : n.toNat ≤ 32)
    (hmodFit : modulus.toNat + 32 * n.toNat < Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.B)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.secondEntry s i a b out modulus n np ret q rest)
      (secondReturned s i a b out modulus n np ret q rest) := by
  have hcode' :
      (loadState s scratch.toNat).executionEnv.code = submissionBytecode := by
    simpa [loadState] using hcode
  have hfork' : (loadState s scratch.toNat).fork = .Osaka := by
    simpa [loadState, State.fork] using hfork
  have hrun' : (loadState s scratch.toNat).halt = .Running := by
    simpa [loadState] using hrun
  have hnp' :
      Precompile.isPrecompileWithConfig (loadState s scratch.toNat).executionEnv.precompileConfig
        (loadState s scratch.toNat).executionEnv.fork
        (loadState s scratch.toNat).executionEnv.codeAddr = false := by
    simpa [loadState, State.fork] using hnp
  have hwordFit : modulus.toNat + 32 * n.toNat < 2 ^ 256 := by
    simpa [Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.B, radix] using hmodFit
  have htFit : scratch.toNat + 32 * n.toNat + 64 < 2 ^ 256 := by
    norm_num [scratch]
    omega
  have hframeCap : (frame i a b out modulus n np ret rest).length < 1000 := by
    simp [frame]
    omega
  simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.secondEntry, secondReturned] using
    (MontgomeryWordBlock.gasSteps_word (loadState s scratch.toNat)
      scratch modulus q n.toNat kSecond
      (frame i a b out modulus n np ret rest)
      hframeCap hn hwordFit htFit hcode' hfork' hrun' hnp' jump_kSecond)

def shiftCopied (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  BigHelpers.copyReturned s scratch (scratch + 32) (n.toNat + 1) kShift
    (frame i a b out modulus n np ret rest)

def reducedReturned (s : State)
    (a b out modulus n np ret high : UInt256) (rest : List UInt256) : State :=
  MontgomeryReduceBlock.reduceReturned
    (loadState s (scratch.toNat + 32 * n.toNat)) scratch modulus high n.toNat kReduce
    (frame n.toNat a b out modulus n np ret rest)

def outputCopied (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  BigHelpers.copyReturned s out scratch n.toNat kDone
    (frame n.toNat a b out modulus n np ret rest)

def gasSteps_shiftCopy (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000) (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.shiftEntry s i a b out modulus n np ret rest)
      (shiftCopied s i a b out modulus n np ret rest) := by
  have hcount : n.toNat + 1 < 2 ^ 256 := by omega
  have hframeCap : (frame i a b out modulus n np ret rest).length < 1016 := by
    simp [frame]
    omega
  simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.shiftEntry, shiftCopied, frame] using
    (BigHelpers.gasSteps_copy s scratch (scratch + 32) (n.toNat + 1) kShift
      (frame i a b out modulus n np ret rest)
      hframeCap hcount hcode hfork hrun hnp jump_kShift)

def gasSteps_reduceBlock (s : State)
    (a b out modulus n np ret high : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000) (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.reduceEntry s n.toNat a b out modulus n np ret high rest)
      (reducedReturned s a b out modulus n np ret high rest) := by
  have hcount : n.toNat < 2 ^ 256 := n.val.isLt
  have hframeCap : (frame n.toNat a b out modulus n np ret rest).length < 1000 := by
    simp [frame]
    omega
  have hcode' :
      (loadState s (scratch.toNat + 32 * n.toNat)).executionEnv.code = submissionBytecode := by
    simpa [loadState] using hcode
  have hfork' :
      (loadState s (scratch.toNat + 32 * n.toNat)).fork = .Osaka := by
    simpa [loadState, State.fork] using hfork
  have hrun' :
      (loadState s (scratch.toNat + 32 * n.toNat)).halt = .Running := by
    simpa [loadState] using hrun
  have hnp' :
      Precompile.isPrecompileWithConfig
          (loadState s (scratch.toNat + 32 * n.toNat)).executionEnv.precompileConfig
          (loadState s (scratch.toNat + 32 * n.toNat)).executionEnv.fork
          (loadState s (scratch.toNat + 32 * n.toNat)).executionEnv.codeAddr = false := by
    simpa [loadState, State.fork] using hnp
  simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.reduceEntry, reducedReturned] using
    (MontgomeryReduceBlock.gasSteps_reduce
      (loadState s (scratch.toNat + 32 * n.toNat)) scratch modulus high n.toNat kReduce
      (frame n.toNat a b out modulus n np ret rest)
      hframeCap hcount hcode' hfork' hrun' hnp' jump_kReduce)

def gasSteps_outputCopy (s : State)
    (a b out modulus n np ret : UInt256) (rest : List UInt256)
    (hcap : rest.length + 8 < 1000) (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.outputEntry s n.toNat a b out modulus n np ret rest)
      (outputCopied s a b out modulus n np ret rest) := by
  have hcount : n.toNat < 2 ^ 256 := n.val.isLt
  have hframeCap : (frame n.toNat a b out modulus n np ret rest).length < 1016 := by
    simp [frame]
    omega
  simpa [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.outputEntry, outputCopied, frame] using
    (BigHelpers.gasSteps_copy s out scratch n.toNat kDone
      (frame n.toNat a b out modulus n np ret rest)
      hframeCap hcount hcode hfork hrun hnp jump_kDone)

def runtimeStep (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.loop
    (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.zeroState
      (shiftCopied
        (secondReturned
          (firstReturned s i a b out modulus n np ret
            (MachineState.readWord s.memory (a.toNat + 32 * i)) rest)
          i a b out modulus n np ret
          (MachineState.readWord
              (firstReturned s i a b out modulus n np ret
                (MachineState.readWord s.memory (a.toNat + 32 * i)) rest).memory
              scratch.toNat * np) rest)
        i a b out modulus n np ret rest)
      (scratch.toNat + 32 * (n.toNat + 1)))
    (i + 1) a b out modulus n np ret rest

theorem firstReturned_state (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    firstReturned s i a b out modulus n np ret
        (MachineState.readWord s.memory (a.toNat + 32 * i)) rest =
      { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.firstLeaf s a b n.toNat i np ret rest with
          pc := kFirst, stack := frame i a b out modulus n np ret rest } := by
  cases s
  rfl

theorem secondReturned_state (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    secondReturned s i a b out modulus n np ret
        (MachineState.readWord s.memory scratch.toNat * np) rest =
      { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.secondLeaf s modulus np n.toNat ret rest with
          pc := kSecond, stack := frame i a b out modulus n np ret rest } := by
  cases s
  rfl

theorem shiftCopied_state (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    shiftCopied s i a b out modulus n np ret rest =
      { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.copyLeaf s n.toNat kShift rest with
          pc := kShift, stack := frame i a b out modulus n np ret rest } := by
  cases s
  rfl

theorem runtimeStep_step (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) :
    runtimeStep s i a b out modulus n np ret rest =
      loop (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step s a b modulus n.toNat i np ret rest)
        (i + 1) a b out modulus n np ret rest := by
  simp only [runtimeStep, Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.shiftLeaf, firstReturned_state,
    secondReturned_state, shiftCopied_state]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreExecution
