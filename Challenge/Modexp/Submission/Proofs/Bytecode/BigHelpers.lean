import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.EvmProof.Meter
import Challenge.Modexp.Submission.Proofs.Mcopy
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified multi-limb bytecode helpers

This module starts the direct proof of the arbitrary-precision path with the
two memory primitives emitted for `clearLimbs` and `copyLimbs`.  States are
parameterized by their caller so the same certificates can be reused at every
call site in `modexpBig` and `mulModBig`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def clearSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 15 .JUMPDEST, pushAt 16 0 0]

def clearGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 17 .JUMPDEST, opAt 18 (.Dup ⟨2, by decide⟩),
   opAt 19 (.Dup ⟨1, by decide⟩), opAt 20 .EQ, opAt 21 .JUMPDEST,
   pushAt 22 2 48, opAt 23 .JUMPI]

def clearBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 24 0 0, opAt 25 (.Dup ⟨1, by decide⟩), pushAt 26 1 5,
   opAt 27 .SHL, opAt 28 (.Dup ⟨3, by decide⟩), opAt 29 .ADD,
   opAt 30 .MSTORE, pushAt 31 1 1, opAt 32 (.Dup ⟨1, by decide⟩),
   opAt 33 .ADD, opAt 34 (.Swap ⟨0, by decide⟩), opAt 35 .POP,
   pushAt 36 2 21, opAt 37 .JUMP]

def clearExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 38 .JUMPDEST, opAt 39 .POP, opAt 40 .POP, opAt 41 .POP,
   opAt 42 .JUMP]

def clearOffset (ptr : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + ptr

def clearMemory (memory : ByteArray) (ptr : UInt256) : Nat → ByteArray
  | 0 => memory
  | i + 1 => MachineState.writeBytes (clearMemory memory ptr i)
      (Data.Bytes.natToBytesPadded 0 32) (clearOffset ptr i).toNat

def clearWords (active : UInt256) (ptr : UInt256) : Nat → UInt256
  | 0 => active
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (clearWords active ptr i).toNat (clearOffset ptr i).toNat 32)

def clearEntry (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 19
           stack := [ptr, UInt256.ofNat count, returnDest] ++ rest }

def clearLoop (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 21
           stack := [UInt256.ofNat i, ptr, UInt256.ofNat count, returnDest] ++ rest
           memory := clearMemory s.memory ptr i
           activeWords := clearWords s.activeWords ptr i }

def clearExit (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { clearLoop s ptr count count returnDest rest with pc := UInt256.ofNat 48 }

def clearBodyEntry (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { clearLoop s ptr count i returnDest rest with pc := UInt256.ofNat 30 }

def clearReturned (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rest
           memory := clearMemory s.memory ptr count
           activeWords := clearWords s.activeWords ptr count }

@[simp] private theorem clearPCs (i : Nat) (hi : 15 ≤ i) (hii : i ≤ 42) :
    Artifact.submissionArtifact.instructionPC i =
      [19,20,21,22,23,24,25,26,29,30,31,32,34,35,36,37,38,40,
       41,42,43,44,47,48,49,50,51,52][i - 15]! := by
  interval_cases i <;> decide

@[simp] private theorem jump21 :
    Decode.isValidJumpDest submissionBytecode 21 = true :=
  Artifact.isValidJumpDest_index 17 (by rfl)

@[simp] private theorem jump48 :
    Decode.isValidJumpDest submissionBytecode 48 = true :=
  Artifact.isValidJumpDest_index 38 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_clearSetup (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearSetupPath
      (clearEntry s ptr count returnDest rest) =
        some (clearLoop s ptr count 0 returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [clearSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    clearEntry, clearLoop, clearMemory, clearWords, clearPCs, hc3, hc4, hrun,
    hzero,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_clearGuard (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearGuardPath
      (clearLoop s ptr count i returnDest rest) =
        some (clearBodyEntry s ptr count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hnmod : count % 2 ^ 256 = count := Nat.mod_eq_of_lt hcount
  have hne : ¬ i % 2 ^ 256 = count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    omega
  have hneLiteral :
      ¬ i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hne ⊢
    exact hne
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hpc : UInt256.ofNat 26 + UInt256.ofNat 3 = UInt256.ofNat 29 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [clearGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    clearLoop, clearBodyEntry, clearPCs, hc4, hc5, hc6, hrun,
    UInt256.eq, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    himod, hnmod, hne, hneLiteral, hpc]

set_option linter.unusedSimpArgs false in
theorem run_clearBody (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearBodyPath
      (clearBodyEntry s ptr count i returnDest rest) =
        some (clearLoop s ptr count (i + 1) returnDest rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have htwentyOne : (21 : UInt256) = UInt256.ofNat 21 := by decide
  have htwentyOneNat : (21 : UInt256).toNat = 21 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (21 : UInt256).toNat = true := by
    rw [htwentyOneNat]
    exact jump21
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hoffcomm : ptr + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + ptr :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 200000 })
    [clearBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      clearBodyEntry, clearLoop, clearMemory, clearWords, clearOffset,
      clearPCs, hc4, hc5, hc6, hc7, hcode, hrun, hzero, hone, hinc,
      hoffcomm, hfive, htwentyOne, htwentyOneNat, hjump, jump21,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_clearFinishGuard (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearGuardPath
      (clearLoop s ptr count count returnDest rest) =
        some (clearExit s ptr count returnDest rest) := by
  have hnmod : count % 2 ^ 256 = count := Nat.mod_eq_of_lt hcount
  have hfortyEight : (48 : UInt256) = UInt256.ofNat 48 := by decide
  have hfortyEightNat : (48 : UInt256).toNat = 48 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (48 : UInt256).toNat = true := by
    rw [hfortyEightNat]
    exact jump48
  have hpc : UInt256.ofNat 26 + UInt256.ofNat 3 = UInt256.ofNat 29 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [clearGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    clearLoop, clearExit, clearPCs, hc4, hc5, hc6, hcode, hrun,
    UInt256.eq, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hnmod, hfortyEight, hfortyEightNat, hjump, jump48, hpc]

set_option linter.unusedSimpArgs false in
theorem run_clearExit (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearExitPath
      (clearExit s ptr count returnDest rest) =
        some (clearReturned s ptr count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [clearExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    clearExit, clearLoop, clearReturned, clearPCs, hc1, hc2, hc3, hc4,
    hcode, hvalid, hrun, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_clearSetup (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearEntry s ptr count returnDest rest)
      (clearLoop s ptr count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka clearSetupPath hcode hfork
      (run_clearSetup s ptr count returnDest rest hcap hrun) hrun hnp

def gasSteps_clearIteration (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hi : i < count) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count i returnDest rest)
      (clearLoop s ptr count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearGuard s ptr count i returnDest rest hcap hcount hi hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearBodyPath
        (by simpa [clearBodyEntry, clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
        (run_clearBody s ptr count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [clearBodyEntry, clearLoop] using hrun)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hnp))

def gasSteps_clearLoop (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count 0 returnDest rest)
      (clearLoop s ptr count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_clearIteration s ptr count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_clearFinish (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count count returnDest rest)
      (clearReturned s ptr count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearFinishGuard s ptr count returnDest rest hcap hcount hcode hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearExitPath
        (by simpa [clearExit, clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearExit, clearLoop, State.fork] using hfork)
        (run_clearExit s ptr count returnDest rest hcap hcode hvalid hrun)
        (by simpa [clearExit, clearLoop] using hrun)
        (by simpa [clearExit, clearLoop, State.fork] using hnp))

def gasSteps_clear (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (clearEntry s ptr count returnDest rest)
      (clearReturned s ptr count returnDest rest) :=
  (gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).trans <|
    (gasSteps_clearLoop s ptr count returnDest rest hcap hcount hcode hfork hrun hnp).trans
      (gasSteps_clearFinish s ptr count returnDest rest hcap hcount hcode hfork
        hrun hnp hvalid)

theorem clearOffset_ofNat (ptr i : Nat) (hfit : ptr + 32 * i < 2 ^ 256) :
    clearOffset (UInt256.ofNat ptr) i = UInt256.ofNat (ptr + 32 * i) := by
  have hi : i < 2 ^ 256 := by omega
  have hshiftResult : i * 2 ^ 5 < 2 ^ 256 := by omega
  have hshift := Challenge.EvmProof.Word.shiftLeft_ofNat
    (value := i) (shift := 5) hi (by norm_num) hshiftResult
  rw [clearOffset, hshift]
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i * 2 ^ 5) (b := ptr) (by omega)
  rw [hadd]
  congr 1
  omega

theorem clearOffset_toNat (ptr i : Nat) (hfit : ptr + 32 * i < 2 ^ 256) :
    (clearOffset (UInt256.ofNat ptr) i).toNat = ptr + 32 * i := by
  rw [clearOffset_ofNat ptr i hfit,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]

theorem readWord_clearMemory (memory : ByteArray) (ptr count j : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256) (hj : j < count) :
    (MachineState.readWord (clearMemory memory (UInt256.ofNat ptr) count)
      (ptr + 32 * j)).toNat = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [clearMemory]
      by_cases hjlast : j = count
      · subst j
        rw [clearOffset_toNat ptr count (by omega),
          Challenge.EvmProof.Memory.readWord_writeBytes_of_lt]
        · simp
        · norm_num
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) (by omega)
        · left
          rw [clearOffset_toNat ptr count (by omega)]
          omega

theorem memoryLimbs_clearMemory (memory : ByteArray) (ptr count : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    Limbs.memoryLimbs (clearMemory memory (UInt256.ofNat ptr) count)
      ptr count = List.replicate count 0 := by
  apply List.ext_get
  · simp [Limbs.memoryLimbs]
  · intro i hiLeft hiRight
    have hi : i < count := by simpa using hiRight
    simp [Limbs.memoryLimbs,
      readWord_clearMemory memory ptr count i hfit hi]

theorem clearMemory_represents_zero (memory : ByteArray) (ptr count : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256) :
    Limbs.Represents (clearMemory memory (UInt256.ofNat ptr) count)
      ptr count 0 := by
  refine ⟨Nat.pow_pos Limbs.radix_pos, ?_⟩
  rw [memoryLimbs_clearMemory memory ptr count hfit]
  simp [Limbs.limbDigits, Nat.digitsAppend]

theorem readWord_clearMemory_disjoint_region (memory : ByteArray)
    (dst ptr count iter j : Nat) (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst) :
    MachineState.readWord (clearMemory memory (UInt256.ofNat dst) iter)
        (ptr + 32 * j) = MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [clearMemory, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (n : Nat) :
            (Data.Bytes.natToBytesPadded n 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, clearOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem represents_clearMemory_disjoint_region (memory : ByteArray)
    (dst ptr count value : Nat) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents (clearMemory memory (UInt256.ofNat dst) count)
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [readWord_clearMemory_disjoint_region memory dst ptr count count j
    (by omega) (by simpa using hj) hdstfit hdisjoint]

theorem gasSteps_clearSetup_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      3 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearSetupPath 3 (run_clearSetup s ptr count returnDest rest hcap hrun)
    (by simpa [clearEntry, State.fork] using hfork)
    (by decide) (by rfl)
  unfold gasSteps_clearSetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp [clearEntry, clearLoop, clearWords] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost clearSetupPath
      (clearEntry s ptr count returnDest rest) = 3 := by
    simpa [clearEntry] using hmeter
  omega

theorem gasSteps_clearIteration_cost_potential (s : State) (ptr : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_clearIteration s ptr count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp).cost +
        MachineState.memCost (clearLoop s ptr count i returnDest rest).activeWords.toNat =
      69 + MachineState.memCost
        (clearLoop s ptr count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearGuardPath 24 (run_clearGuard s ptr count i returnDest rest
      hcap hcount hi hrun)
    (by simpa [clearLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearBodyPath 45 (run_clearBody s ptr count i returnDest rest hcap
      (by omega) hcode hrun)
    (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearGuard s ptr count i returnDest rest hcap hcount hi hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearBodyPath
        (by simpa [clearBodyEntry, clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
        (run_clearBody s ptr count i returnDest rest hcap (by omega) hcode hrun)
        (by simpa [clearBodyEntry, clearLoop] using hrun)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hnp)))
    24 45 hguard hbody
  simpa [gasSteps_clearIteration] using htrans

theorem gasSteps_clearLoop_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_clearLoop s ptr count returnDest rest hcap hcount hcode hfork
      hrun hnp).cost + MachineState.memCost
        (clearLoop s ptr count 0 returnDest rest).activeWords.toNat =
      count * 69 + MachineState.memCost
        (clearLoop s ptr count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_clearLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_clearIteration_cost_potential s ptr count i returnDest rest
    hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_clearFinish_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_clearFinish s ptr count returnDest rest hcap hcount hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost
        (clearLoop s ptr count count returnDest rest).activeWords.toNat =
      39 + MachineState.memCost
        (clearReturned s ptr count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearGuardPath 24 (run_clearFinishGuard s ptr count returnDest rest
      hcap hcount hcode hrun)
    (by simpa [clearLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearExitPath 15 (run_clearExit s ptr count returnDest rest hcap hcode
      hvalid hrun)
    (by simpa [clearExit, clearLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearFinishGuard s ptr count returnDest rest hcap hcount hcode hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka clearExitPath
        (by simpa [clearExit, clearLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [clearExit, clearLoop, State.fork] using hfork)
        (run_clearExit s ptr count returnDest rest hcap hcode hvalid hrun)
        (by simpa [clearExit, clearLoop] using hrun)
        (by simpa [clearExit, clearLoop, State.fork] using hnp)))
    24 15 hguard hexit
  simpa [gasSteps_clearFinish] using htrans

theorem gasSteps_clear_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_clear s ptr count returnDest rest hcap hcount hcode hfork hrun hnp
      hvalid).cost + MachineState.memCost s.activeWords.toNat =
      (42 + count * 69) + MachineState.memCost
        (clearReturned s ptr count returnDest rest).activeWords.toNat := by
  have hsetup := gasSteps_clearSetup_cost_potential s ptr count returnDest rest
    hcap hcode hfork hrun hnp
  have hloop := gasSteps_clearLoop_cost_potential s ptr count returnDest rest
    hcap hcount hcode hfork hrun hnp
  have hfinish := gasSteps_clearFinish_cost_potential s ptr count returnDest rest
    hcap hcount hcode hfork hrun hnp hvalid
  have hsetup' :
      (gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).cost +
          MachineState.memCost (clearEntry s ptr count returnDest rest).activeWords.toNat =
        3 + MachineState.memCost
          (clearLoop s ptr count 0 returnDest rest).activeWords.toNat := by
    simpa only [clearEntry, clearLoop, clearWords] using hsetup
  have hprefix := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp)
    (gasSteps_clearLoop s ptr count returnDest rest hcap hcount hcode hfork hrun hnp)
    3 (count * 69) hsetup' hloop
  have htotal := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).trans
      (gasSteps_clearLoop s ptr count returnDest rest hcap hcount hcode hfork hrun hnp))
    (gasSteps_clearFinish s ptr count returnDest rest hcap hcount hcode hfork
      hrun hnp hvalid) (3 + count * 69) 39 hprefix hfinish
  unfold gasSteps_clear
  simp only [Challenge.EvmProof.GasSteps.trans_cost] at htotal ⊢
  have hactive : (clearEntry s ptr count returnDest rest).activeWords =
      s.activeWords := by rfl
  rw [hactive] at htotal
  omega

/-! ## `copyLimbs` -/

def copySetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 46 .JUMPDEST, pushAt 47 0 0]

def copyGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 48 .JUMPDEST, opAt 49 (.Dup ⟨3, by decide⟩),
   opAt 50 (.Dup ⟨1, by decide⟩), opAt 51 .EQ, opAt 52 .JUMPDEST,
   pushAt 53 2 93, opAt 54 .JUMPI]

def copyBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 55 (.Dup ⟨0, by decide⟩), pushAt 56 1 5, opAt 57 .SHL,
   opAt 58 (.Dup ⟨3, by decide⟩), opAt 59 .ADD, opAt 60 .MLOAD,
   opAt 61 (.Dup ⟨1, by decide⟩), pushAt 62 1 5, opAt 63 .SHL,
   opAt 64 (.Dup ⟨3, by decide⟩), opAt 65 .ADD, opAt 66 .MSTORE,
   pushAt 67 1 1, opAt 68 (.Dup ⟨1, by decide⟩), opAt 69 .ADD,
   opAt 70 (.Swap ⟨0, by decide⟩), opAt 71 .POP,
   pushAt 72 2 60, opAt 73 .JUMP]

def copyExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 74 .JUMPDEST, opAt 75 .POP, opAt 76 .POP, opAt 77 .POP,
   opAt 78 .POP, opAt 79 .JUMP]

def copyMemory (memory : ByteArray) (dst src : UInt256) : Nat → ByteArray
  | 0 => memory
  | i + 1 =>
      let before := copyMemory memory dst src i
      MachineState.writeBytes before
        (Data.Bytes.natToBytesPadded
          (MachineState.readWord before (clearOffset src i).toNat).toNat 32)
        (clearOffset dst i).toNat

def copyWords (active : UInt256) (dst src : UInt256) : Nat → UInt256
  | 0 => active
  | i + 1 =>
      let loaded := UInt256.ofNat (MachineState.activeWordsAfter
        (copyWords active dst src i).toNat (clearOffset src i).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter loaded.toNat
        (clearOffset dst i).toNat 32)

def copyEntry (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 58
           stack := [dst, src, UInt256.ofNat count, returnDest] ++ rest }

def copyLoop (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 60
           stack := [UInt256.ofNat i, dst, src, UInt256.ofNat count,
             returnDest] ++ rest
           memory := copyMemory s.memory dst src i
           activeWords := copyWords s.activeWords dst src i }

def copyBodyEntry (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { copyLoop s dst src count i returnDest rest with pc := UInt256.ofNat 69 }

def copyExit (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { copyLoop s dst src count count returnDest rest with pc := UInt256.ofNat 93 }

def copyReturned (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rest
           memory := copyMemory s.memory dst src count
           activeWords := copyWords s.activeWords dst src count }

@[simp] private theorem copyPCs (i : Nat) (hi : 46 ≤ i) (hii : i ≤ 79) :
    Artifact.submissionArtifact.instructionPC i =
      [58,59,60,61,62,63,64,65,68,69,70,72,73,74,75,76,77,
       79,80,81,82,83,85,86,87,88,89,92,93,94,95,96,97,98][i - 46]! := by
  interval_cases i <;> decide

@[simp] private theorem jump60 :
    Decode.isValidJumpDest submissionBytecode 60 = true :=
  Artifact.isValidJumpDest_index 48 (by rfl)

@[simp] private theorem jump93 :
    Decode.isValidJumpDest submissionBytecode 93 = true :=
  Artifact.isValidJumpDest_index 74 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_copySetup (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copySetupPath
      (copyEntry s dst src count returnDest rest) =
        some (copyLoop s dst src count 0 returnDest rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [copySetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyEntry, copyLoop, copyMemory, copyWords, copyPCs, hc4, hc5, hrun,
    hzero, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_copyGuard (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyGuardPath
      (copyLoop s dst src count i returnDest rest) =
        some (copyBodyEntry s dst src count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hne : ¬ i % 2 ^ 256 = count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    omega
  have hneLiteral :
      ¬ i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hne ⊢
    exact hne
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hpc : UInt256.ofNat 65 + UInt256.ofNat 3 = UInt256.ofNat 68 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [copyGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyLoop, copyBodyEntry, copyPCs, hc5, hc6, hc7, hrun,
    UInt256.eq, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hneLiteral, hpc]

set_option linter.unusedSimpArgs false in
theorem run_copyBody (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyBodyPath
      (copyBodyEntry s dst src count i returnDest rest) =
        some (copyLoop s dst src count (i + 1) returnDest rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hsixty : (60 : UInt256) = UInt256.ofNat 60 := by decide
  have hsixtyNat : (60 : UInt256).toNat = 60 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (60 : UInt256).toNat = true := by
    rw [hsixtyNat]
    exact jump60
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hsrccomm : src + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + src :=
    Challenge.EvmProof.Word.word_add_comm _ _
  have hdstcomm : dst + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + dst :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp (config := { maxSteps := 250000 })
    [copyBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      copyBodyEntry, copyLoop, copyMemory, copyWords, clearOffset,
      copyPCs, hc5, hc6, hc7, hc8, hcode, hrun, hone, hfive, hinc,
      hsrccomm, hdstcomm, hsixty, hsixtyNat, hjump, jump60,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_copyFinishGuard (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyGuardPath
      (copyLoop s dst src count count returnDest rest) =
        some (copyExit s dst src count returnDest rest) := by
  have hninetyThree : (93 : UInt256) = UInt256.ofNat 93 := by decide
  have hninetyThreeNat : (93 : UInt256).toNat = 93 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (93 : UInt256).toNat = true := by
    rw [hninetyThreeNat]
    exact jump93
  have hpc : UInt256.ofNat 65 + UInt256.ofNat 3 = UInt256.ofNat 68 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [copyGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyLoop, copyExit, copyPCs, hc5, hc6, hc7, hcode, hrun,
    UInt256.eq, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hninetyThree, hninetyThreeNat, hjump, jump93, hpc]

set_option linter.unusedSimpArgs false in
theorem run_copyExit (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyExitPath
      (copyExit s dst src count returnDest rest) =
        some (copyReturned s dst src count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [copyExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyExit, copyLoop, copyReturned, copyPCs, hc1, hc2, hc3, hc4, hc5,
    hcode, hvalid, hrun, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_copySetup (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (copyEntry s dst src count returnDest rest)
      (copyLoop s dst src count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka copySetupPath hcode hfork
      (run_copySetup s dst src count returnDest rest hcap hrun) hrun hnp

def gasSteps_copyIteration (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (copyLoop s dst src count i returnDest rest)
      (copyLoop s dst src count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyGuardPath
        (by simpa [copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyLoop, State.fork] using hfork)
        (run_copyGuard s dst src count i returnDest rest hcap hcount hi hrun)
        (by simpa [copyLoop] using hrun)
        (by simpa [copyLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyBodyPath
        (by simpa [copyBodyEntry, copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyBodyEntry, copyLoop, State.fork] using hfork)
        (run_copyBody s dst src count i returnDest rest hcap (by omega) hcode hrun)
        (by simpa [copyBodyEntry, copyLoop] using hrun)
        (by simpa [copyBodyEntry, copyLoop, State.fork] using hnp))

def gasSteps_copyLoop (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (copyLoop s dst src count 0 returnDest rest)
      (copyLoop s dst src count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_copyIteration s dst src count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_copyFinish (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (copyLoop s dst src count count returnDest rest)
      (copyReturned s dst src count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyGuardPath
        (by simpa [copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyLoop, State.fork] using hfork)
        (run_copyFinishGuard s dst src count returnDest rest hcap hcode hrun)
        (by simpa [copyLoop] using hrun)
        (by simpa [copyLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyExitPath
        (by simpa [copyExit, copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyExit, copyLoop, State.fork] using hfork)
        (run_copyExit s dst src count returnDest rest hcap hcode hvalid hrun)
        (by simpa [copyExit, copyLoop] using hrun)
        (by simpa [copyExit, copyLoop, State.fork] using hnp))

def gasSteps_copy (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (copyEntry s dst src count returnDest rest)
      (copyReturned s dst src count returnDest rest) :=
  (gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp).trans <|
    (gasSteps_copyLoop s dst src count returnDest rest hcap hcount hcode hfork
      hrun hnp).trans
    (gasSteps_copyFinish s dst src count returnDest rest hcap hcode hfork hrun
      hnp hvalid)

theorem readWord_copyMemory_source (memory : ByteArray) (dst src count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (_hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst) :
    MachineState.readWord
        (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) iter)
        (src + 32 * j) =
      MachineState.readWord memory (src + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [copyMemory, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · rw [clearOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right
          have hsize :
              (Data.Bytes.natToBytesPadded
                (MachineState.readWord
                  (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) iter)
                  (clearOffset (UInt256.ofNat src) iter).toNat).toNat 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize]
          omega
        · left
          omega

theorem readWord_copyMemory_dest (memory : ByteArray) (dst src count j : Nat)
    (hj : j < count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst) :
    MachineState.readWord
        (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) count)
        (dst + 32 * j) =
      MachineState.readWord memory (src + 32 * j) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [copyMemory]
      by_cases hjlast : j = count
      · subst j
        rw [clearOffset_toNat dst count (by omega),
          Challenge.EvmProof.Memory.readWord_writeWord,
          clearOffset_toNat src count (by omega)]
        exact readWord_copyMemory_source memory dst src (count + 1) count count
          (by omega) (by omega) hdstfit hsrcfit hdisjoint
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · apply ih (by omega) (by omega) (by omega)
          rcases hdisjoint with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · left
          rw [clearOffset_toNat dst count (by omega)]
          omega

theorem memoryLimbs_copyMemory (memory : ByteArray) (dst src count : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst) :
    Limbs.memoryLimbs
        (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) count)
        dst count =
      Limbs.memoryLimbs memory src count := by
  apply List.ext_get
  · simp [Limbs.memoryLimbs]
  · intro i hiLeft hiRight
    have hi : i < count := by simpa [Limbs.memoryLimbs] using hiRight
    simp [Limbs.memoryLimbs,
      readWord_copyMemory_dest memory dst src count i hi hdstfit hsrcfit hdisjoint]

theorem copyMemory_represents (memory : ByteArray) (dst src count value : Nat)
    (hsrc : Limbs.Represents memory src count value)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst) :
    Limbs.Represents
      (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) count)
      dst count value := by
  refine ⟨hsrc.1, ?_⟩
  rw [memoryLimbs_copyMemory memory dst src count hdstfit hsrcfit hdisjoint,
    hsrc.2]

theorem readWord_copyMemory_disjoint_region (memory : ByteArray)
    (dst src ptr count iter j : Nat) (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst) :
    MachineState.readWord
        (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) iter)
        (ptr + 32 * j) = MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [copyMemory, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (n : Nat) :
            (Data.Bytes.natToBytesPadded n 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, clearOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem represents_copyMemory_disjoint_region (memory : ByteArray)
    (dst src ptr count value : Nat)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) count)
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [readWord_copyMemory_disjoint_region memory dst src ptr count count j
    (by omega) (by simpa using hj) hdstfit hdisjoint]

theorem gasSteps_copySetup_cost_potential (s : State) (dst src : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      3 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copySetupPath 3 (run_copySetup s dst src count returnDest rest hcap hrun)
    (by simpa [copyEntry, State.fork] using hfork)
    (by decide) (by rfl)
  unfold gasSteps_copySetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp [copyEntry, copyLoop, copyWords] at hmeter
  have hcost : Challenge.EvmProof.Stepper.runLocatedBlockCost copySetupPath
      (copyEntry s dst src count returnDest rest) = 3 := by
    simpa [copyEntry] using hmeter
  omega

theorem gasSteps_copyIteration_cost_potential (s : State) (dst src : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_copyIteration s dst src count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp).cost + MachineState.memCost
        (copyLoop s dst src count i returnDest rest).activeWords.toNat =
      85 + MachineState.memCost
        (copyLoop s dst src count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyGuardPath 24 (run_copyGuard s dst src count i returnDest rest
      hcap hcount hi hrun)
    (by simpa [copyLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyBodyPath 61 (run_copyBody s dst src count i returnDest rest hcap
      (by omega) hcode hrun)
    (by simpa [copyBodyEntry, copyLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyGuardPath
        (by simpa [copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyLoop, State.fork] using hfork)
        (run_copyGuard s dst src count i returnDest rest hcap hcount hi hrun)
        (by simpa [copyLoop] using hrun)
        (by simpa [copyLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyBodyPath
        (by simpa [copyBodyEntry, copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyBodyEntry, copyLoop, State.fork] using hfork)
        (run_copyBody s dst src count i returnDest rest hcap (by omega) hcode hrun)
        (by simpa [copyBodyEntry, copyLoop] using hrun)
        (by simpa [copyBodyEntry, copyLoop, State.fork] using hnp)))
    24 61 hguard hbody
  simpa [gasSteps_copyIteration] using htrans

theorem gasSteps_copyLoop_cost_potential (s : State) (dst src : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_copyLoop s dst src count returnDest rest hcap hcount hcode hfork
      hrun hnp).cost + MachineState.memCost
        (copyLoop s dst src count 0 returnDest rest).activeWords.toNat =
      count * 85 + MachineState.memCost
        (copyLoop s dst src count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_copyLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_copyIteration_cost_potential s dst src count i returnDest rest
    hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_copyFinish_cost_potential (s : State) (dst src : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_copyFinish s dst src count returnDest rest hcap hcode hfork hrun hnp
      hvalid).cost + MachineState.memCost
        (copyLoop s dst src count count returnDest rest).activeWords.toNat =
      41 + MachineState.memCost
        (copyReturned s dst src count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyGuardPath 24 (run_copyFinishGuard s dst src count returnDest rest
      hcap hcode hrun)
    (by simpa [copyLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyExitPath 17 (run_copyExit s dst src count returnDest rest hcap hcode
      hvalid hrun)
    (by simpa [copyExit, copyLoop, State.fork] using hfork)
    (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyGuardPath
        (by simpa [copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyLoop, State.fork] using hfork)
        (run_copyFinishGuard s dst src count returnDest rest hcap hcode hrun)
        (by simpa [copyLoop] using hrun)
        (by simpa [copyLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyExitPath
        (by simpa [copyExit, copyLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [copyExit, copyLoop, State.fork] using hfork)
        (run_copyExit s dst src count returnDest rest hcap hcode hvalid hrun)
        (by simpa [copyExit, copyLoop] using hrun)
        (by simpa [copyExit, copyLoop, State.fork] using hnp)))
    24 17 hguard hexit
  simpa [gasSteps_copyFinish] using htrans

theorem gasSteps_copy_cost_potential (s : State) (dst src : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_copy s dst src count returnDest rest hcap hcount hcode hfork hrun
      hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      (44 + count * 85) + MachineState.memCost
        (copyReturned s dst src count returnDest rest).activeWords.toNat := by
  have hsetup := gasSteps_copySetup_cost_potential s dst src count returnDest rest
    hcap hcode hfork hrun hnp
  have hloop := gasSteps_copyLoop_cost_potential s dst src count returnDest rest
    hcap hcount hcode hfork hrun hnp
  have hfinish := gasSteps_copyFinish_cost_potential s dst src count returnDest rest
    hcap hcode hfork hrun hnp hvalid
  have hsetup' :
      (gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp).cost +
          MachineState.memCost
            (copyEntry s dst src count returnDest rest).activeWords.toNat =
        3 + MachineState.memCost
          (copyLoop s dst src count 0 returnDest rest).activeWords.toNat := by
    simpa only [copyEntry, copyLoop, copyWords] using hsetup
  have hprefix := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp)
    (gasSteps_copyLoop s dst src count returnDest rest hcap hcount hcode hfork hrun hnp)
    3 (count * 85) hsetup' hloop
  have htotal := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp).trans
      (gasSteps_copyLoop s dst src count returnDest rest hcap hcount hcode hfork hrun hnp))
    (gasSteps_copyFinish s dst src count returnDest rest hcap hcode hfork hrun
      hnp hvalid) (3 + count * 85) 41 hprefix hfinish
  unfold gasSteps_copy
  simp only [Challenge.EvmProof.GasSteps.trans_cost] at htotal ⊢
  have hactive : (copyEntry s dst src count returnDest rest).activeWords =
      s.activeWords := by rfl
  rw [hactive] at htotal
  omega

/-! ## `addMaskedMod`: the fused one-pass routine

The routine appended at byte 1448 (instruction index 1071) computes

```
dst := (dst + take * src) % modulus
```

over `count` little-endian 32-byte limbs.  It first returns immediately when
`take * count = 0` — correct because the helper's contract already assumes the
destination is reduced — and otherwise makes a **single** pass over the limbs,
computing each sum limb and the matching limb of the wrapped difference
`sum - modulus` together.  The sum limbs are stored back into `dst`, the
difference limbs into the private scratch buffer at `0x1400`; one conditional
whole-buffer `MCOPY` then selects between them.
-/

/-! ### Word-level helpers -/

theorem word_add_assoc (a b c : UInt256) : a + b + c = a + (b + c) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem word_add_sub_self (a b : UInt256) : a + (b - a) = b := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_sub_cond]
  by_cases h : b.toNat < a.toNat
  · rw [if_pos h,
      show a.toNat + (2 ^ 256 + b.toNat - a.toNat) = 2 ^ 256 + b.toNat by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hb]
  · rw [if_neg h, show a.toNat + (b.toNat - a.toNat) = b.toNat by omega,
      Nat.mod_eq_of_lt hb]

/-- The loop's derived pointers: `dp + (x - dst)` is `dp` shifted onto `x`. -/
theorem word_shift_sub_cancel (o a b : UInt256) : o + a + (b - a) = o + b := by
  rw [word_add_assoc, word_add_sub_self]

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem word_gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl

/-- Borrowing out of `a - b` is the same as `a < a - b` in wrapped arithmetic. -/
theorem word_lt_sub_self (a b : UInt256) :
    UInt256.lt a (a - b) = UInt256.lt a b := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  have hsub := Challenge.EvmProof.Word.word_toNat_sub_cond a b
  by_cases h : a.toNat < b.toNat
  · rw [if_pos h] at hsub
    simp only [UInt256.lt, hsub, if_pos h,
      if_pos (show a.toNat < 2 ^ 256 + a.toNat - b.toNat by omega)]
  · rw [if_neg h] at hsub
    simp only [UInt256.lt, hsub, if_neg h,
      if_neg (show ¬ a.toNat < a.toNat - b.toNat by omega)]

theorem word_lor_flag_comm (a b : UInt256) (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1) :
    (UInt256.lor a b).toNat = (UInt256.lor b a).toNat := by
  simp only [Challenge.EvmProof.Word.word_toNat_lor]
  interval_cases h₁ : a.toNat <;> interval_cases h₂ : b.toNat <;> decide

theorem word_lt_toNat_le_one (a b : UInt256) : (UInt256.lt a b).toNat ≤ 1 := by
  rw [Challenge.EvmProof.Word.word_toNat_lt]
  split <;> omega

/-! ### The per-limb steps -/

theorem addLimbStep_toNat (x y carry : UInt256) (hcarry : carry.toNat ≤ 1) :
    let sum := x + y
    let z := sum + carry
    z.toNat = (x.toNat + y.toNat + carry.toNat) % Limbs.radix ∧
      (UInt256.lor (UInt256.lt sum x) (UInt256.lt z sum)).toNat =
        (x.toNat + y.toNat + carry.toNat) / Limbs.radix := by
  dsimp only
  constructor
  · simp only [Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
    have hcarryLt : carry.toNat < 2 ^ 256 :=
      carry.val.isLt
    calc
      ((x.toNat + y.toNat) % 2 ^ 256 + carry.toNat) % 2 ^ 256 =
          ((x.toNat + y.toNat) % 2 ^ 256 +
            carry.toNat % 2 ^ 256) % 2 ^ 256 := by
              rw [Nat.mod_eq_of_lt hcarryLt]
      _ = (x.toNat + y.toNat + carry.toNat) % 2 ^ 256 :=
        (Nat.add_mod (x.toNat + y.toNat) carry.toNat (2 ^ 256)).symm
  · simp only [Challenge.EvmProof.Word.word_toNat_lor,
      Challenge.EvmProof.Word.word_toNat_lt,
      Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
    exact Limbs.addCarryBits x.val.isLt y.val.isLt hcarry

theorem subLimbStep_toNat (x y borrow : UInt256)
    (hborrow : borrow.toNat ≤ 1) :
    let difference := x - y
    let z := difference - borrow
    let nextBorrow := if x.toNat < y.toNat + borrow.toNat then 1 else 0
    z.toNat = x.toNat + Limbs.radix * nextBorrow - y.toNat - borrow.toNat ∧
      (UInt256.lor (UInt256.lt x y)
        (UInt256.lt difference borrow)).toNat = nextBorrow := by
  dsimp only
  have hx : x.toNat < Limbs.radix := x.val.isLt
  have hy : y.toNat < Limbs.radix := y.val.isLt
  have hstep := Limbs.subLimbBits hx hy hborrow
  simpa only [Challenge.EvmProof.Word.word_toNat_sub_cond,
    Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_lt, Limbs.radix] using hstep

/-- The addition step in the operand order the fused routine actually uses:
the carry-out flags are produced by `GT` and combined with the second flag on
top of the stack. -/
theorem addLimbStep_fused (x y carry : UInt256) (hcarry : carry.toNat ≤ 1) :
    ((x + y) + carry).toNat = (x.toNat + y.toNat + carry.toNat) % Limbs.radix ∧
      (UInt256.lor (UInt256.gt (x + y) ((x + y) + carry))
        (UInt256.gt x (x + y))).toNat =
          (x.toNat + y.toNat + carry.toNat) / Limbs.radix := by
  have hstep := addLimbStep_toNat x y carry hcarry
  refine ⟨hstep.1, ?_⟩
  rw [word_gt_eq_lt, word_gt_eq_lt,
    word_lor_flag_comm _ _ (word_lt_toNat_le_one _ _) (word_lt_toNat_le_one _ _)]
  exact hstep.2

/-- The subtraction step in the operand order the fused routine uses: both
borrow flags are detected by comparing against the wrapped difference. -/
theorem subLimbStep_fused (x y borrow : UInt256) (hborrow : borrow.toNat ≤ 1) :
    ((x - y) - borrow).toNat =
        x.toNat + Limbs.radix * (if x.toNat < y.toNat + borrow.toNat then 1 else 0)
          - y.toNat - borrow.toNat ∧
      (UInt256.lor (UInt256.lt (x - y) ((x - y) - borrow))
        (UInt256.lt x (x - y))).toNat =
          if x.toNat < y.toNat + borrow.toNat then 1 else 0 := by
  have hstep := subLimbStep_toNat x y borrow hborrow
  refine ⟨hstep.1, ?_⟩
  rw [word_lt_sub_self, word_lt_sub_self,
    word_lor_flag_comm _ _ (word_lt_toNat_le_one _ _) (word_lt_toNat_le_one _ _)]
  exact hstep.2

/-! ### Memory bookkeeping -/

theorem addOffset_toNat (ptr i : Nat) (hfit : ptr + 32 * i < 2 ^ 256) :
    (UInt256.ofNat ptr +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat =
        ptr + 32 * i := by
  rw [Challenge.EvmProof.Word.word_add_comm]
  exact clearOffset_toNat ptr i hfit

/-- The running pointer the fused loop keeps: `dst` advanced by `32 * i`. -/
theorem fusedOffset_toNat (ptr i : Nat) (hfit : ptr + 32 * i < 2 ^ 256) :
    (UInt256.ofNat (32 * i) + UInt256.ofNat ptr).toNat = ptr + 32 * i := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * i + ptr < 2 ^ 256)]
  omega

theorem natToBytesPadded_size (value : Nat) :
    (Data.Bytes.natToBytesPadded value 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

theorem memoryLimbs_write_next (memory : ByteArray) (ptr i : Nat)
    (value : UInt256) :
    Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) (ptr + 32 * i))
        ptr (i + 1) =
      Limbs.memoryLimbs memory ptr i ++ [value.toNat] := by
  simp only [Limbs.memoryLimbs, List.range_succ, List.map_append,
    List.map_singleton]
  rw [Challenge.EvmProof.Memory.readWord_writeWord]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · left
    have hjlt : j < i := by simpa using hj
    omega

theorem memoryLimbs_succ (memory : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs memory ptr (count + 1) =
      Limbs.memoryLimbs memory ptr count ++
        [(MachineState.readWord memory (ptr + 32 * count)).toNat] := by
  simp [Limbs.memoryLimbs, List.range_succ]

theorem memoryLimbs_write_disjoint (memory : ByteArray) (value ptr count wptr : Nat)
    (hdisjoint : ptr + 32 * count ≤ wptr ∨ wptr + 32 ≤ ptr) :
    Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) wptr) ptr count =
      Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt : j < count := by simpa using hj
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  rw [natToBytesPadded_size]
  omega

theorem memoryLimbs_value_lt (memory : ByteArray) (ptr count : Nat) :
    Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr count) <
      Limbs.radix ^ count := by
  have hlt := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one
    (fun digit hdigit => Limbs.memoryLimb_lt memory ptr count hdigit)
  simpa using hlt

theorem represents_memoryLimbs_value (memory : ByteArray) (ptr count : Nat) :
    Limbs.Represents memory ptr count
      (Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr count)) := by
  rw [Limbs.represents_iff_value (memoryLimbs_value_lt memory ptr count)]

/-! ### The fused progress function -/

structure FusedProgress where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256
  borrow : UInt256

/-- Symbolic state of the fused loop after `i` limbs, phrased with the machine
words the routine actually holds.  Each round reads the destination, source and
modulus limb, forms the sum limb `z` and the wrapped difference limb `w`, and
stores `w` to the scratch buffer and then `z` to the destination — in that
order, because the source may alias the destination. -/
def fusedProgress (memory : ByteArray) (activeWords dst src modulus : UInt256) :
    Nat → FusedProgress
  | 0 => ⟨memory, activeWords, 0, 0⟩
  | i + 1 =>
      let before := fusedProgress memory activeWords dst src modulus i
      let off := UInt256.ofNat (32 * i)
      let dp := off + dst
      let sp := off + src
      let mp := off + modulus
      let cp := off + UInt256.ofNat 5120
      let x := MachineState.readWord before.memory dp.toNat
      let y := MachineState.readWord before.memory sp.toNat
      let sum := x + y
      let z := sum + before.carry
      let carry := UInt256.lor (UInt256.gt sum z) (UInt256.gt x sum)
      let m := MachineState.readWord before.memory mp.toNat
      let d := z - m
      let w := d - before.borrow
      let borrow := UInt256.lor (UInt256.lt d w) (UInt256.lt z d)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dp.toNat 32)
      let loadedSrc := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat sp.toNat 32)
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedSrc.toNat mp.toNat 32)
      let storedScratch := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat cp.toNat 32)
      let storedDst := UInt256.ofNat (MachineState.activeWordsAfter
        storedScratch.toNat dp.toNat 32)
      ⟨MachineState.writeBytes
          (MachineState.writeBytes before.memory
            (Data.Bytes.natToBytesPadded w.toNat 32) cp.toNat)
          (Data.Bytes.natToBytesPadded z.toNat 32) dp.toNat,
        storedDst, carry, borrow⟩

/-- The same recursion with the limb addresses already resolved to naturals.
All of the arithmetic below is carried out on this form. -/
def fusedNatProgress (memory : ByteArray) (activeWords : UInt256)
    (dst src modulus : Nat) : Nat → FusedProgress
  | 0 => ⟨memory, activeWords, 0, 0⟩
  | i + 1 =>
      let before := fusedNatProgress memory activeWords dst src modulus i
      let x := MachineState.readWord before.memory (dst + 32 * i)
      let y := MachineState.readWord before.memory (src + 32 * i)
      let sum := x + y
      let z := sum + before.carry
      let carry := UInt256.lor (UInt256.gt sum z) (UInt256.gt x sum)
      let m := MachineState.readWord before.memory (modulus + 32 * i)
      let d := z - m
      let w := d - before.borrow
      let borrow := UInt256.lor (UInt256.lt d w) (UInt256.lt z d)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat (dst + 32 * i) 32)
      let loadedSrc := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat (src + 32 * i) 32)
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedSrc.toNat (modulus + 32 * i) 32)
      let storedScratch := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat (5120 + 32 * i) 32)
      let storedDst := UInt256.ofNat (MachineState.activeWordsAfter
        storedScratch.toNat (dst + 32 * i) 32)
      ⟨MachineState.writeBytes
          (MachineState.writeBytes before.memory
            (Data.Bytes.natToBytesPadded w.toNat 32) (5120 + 32 * i))
          (Data.Bytes.natToBytesPadded z.toNat 32) (dst + 32 * i),
        storedDst, carry, borrow⟩

theorem fusedProgress_eq_nat (memory : ByteArray) (activeWords : UInt256)
    (dst src modulus iter : Nat)
    (hdstFit : dst + 32 * iter < 2 ^ 256) (hsrcFit : src + 32 * iter < 2 ^ 256)
    (hmodulusFit : modulus + 32 * iter < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * iter < 2 ^ 256) :
    fusedProgress memory activeWords (UInt256.ofNat dst) (UInt256.ofNat src)
        (UInt256.ofNat modulus) iter =
      fusedNatProgress memory activeWords dst src modulus iter := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      simp only [fusedProgress, fusedNatProgress,
        ih (by omega) (by omega) (by omega) (by omega),
        fusedOffset_toNat dst iter (by omega),
        fusedOffset_toNat src iter (by omega),
        fusedOffset_toNat modulus iter (by omega),
        fusedOffset_toNat 5120 iter (by omega)]

/-! ### Frame lemmas for the fused pass -/

/-- Every write the loop makes in its first `iter` rounds lands in
`[dst, dst + 32 * iter)` or `[0x1400, 0x1400 + 32 * iter)`, so a word outside
both windows is untouched. -/
theorem readWord_fusedNatProgress_stable (memory : ByteArray)
    (activeWords : UInt256) (dst src modulus iter addr : Nat)
    (hdisjointDst : addr + 32 ≤ dst ∨ dst + 32 * iter ≤ addr)
    (hdisjointCandidate : addr + 32 ≤ 5120 ∨ 5120 + 32 * iter ≤ addr) :
    MachineState.readWord
        (fusedNatProgress memory activeWords dst src modulus iter).memory addr =
      MachineState.readWord memory addr := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [fusedNatProgress, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega) (by omega)
      · rw [natToBytesPadded_size]
        omega
      · rw [natToBytesPadded_size]
        omega

/-- The same frame property stated for the machine-word form of the loop.  It
needs no information about `src` or `modulus`: the routine only ever writes to
the destination window and to the scratch buffer. -/
theorem readWord_fusedProgress_frame (memory : ByteArray) (activeWords : UInt256)
    (src modulus : UInt256) (dst iter addr : Nat)
    (hdstFit : dst + 32 * iter < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * iter < 2 ^ 256)
    (hdisjointDst : addr + 32 ≤ dst ∨ dst + 32 * iter ≤ addr)
    (hdisjointCandidate : addr + 32 ≤ 5120 ∨ 5120 + 32 * iter ≤ addr) :
    MachineState.readWord
        (fusedProgress memory activeWords (UInt256.ofNat dst) src modulus
          iter).memory addr =
      MachineState.readWord memory addr := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      have hoffDst :
          (UInt256.ofNat (32 * iter) + UInt256.ofNat dst).toNat = dst + 32 * iter :=
        fusedOffset_toNat dst iter (by omega)
      have hoffCandidate :
          (UInt256.ofNat (32 * iter) + UInt256.ofNat 5120).toNat =
            5120 + 32 * iter :=
        fusedOffset_toNat 5120 iter (by omega)
      rw [fusedProgress, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega) (by omega) (by omega) (by omega)
      · rw [natToBytesPadded_size, hoffCandidate]
        omega
      · rw [natToBytesPadded_size, hoffDst]
        omega

theorem memoryLimbs_fusedProgress_frame (memory : ByteArray)
    (activeWords : UInt256) (src modulus : UInt256) (dst iter ptr count : Nat)
    (hdstFit : dst + 32 * iter < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * iter < 2 ^ 256)
    (hdisjointDst : ptr + 32 * count ≤ dst ∨ dst + 32 * iter ≤ ptr)
    (hdisjointCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * iter ≤ ptr) :
    Limbs.memoryLimbs
        (fusedProgress memory activeWords (UInt256.ofNat dst) src modulus
          iter).memory ptr count =
      Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt : j < count := by simpa using hj
  exact congrArg UInt256.toNat (readWord_fusedProgress_frame memory activeWords
    src modulus dst iter (ptr + 32 * j) hdstFit hcandidateFit (by omega)
    (by omega))

theorem represents_fusedProgress_frame (memory : ByteArray)
    (activeWords : UInt256) (src modulus : UInt256)
    (dst iter ptr count value : Nat)
    (hdstFit : dst + 32 * iter < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * iter < 2 ^ 256)
    (hdisjointDst : ptr + 32 * count ≤ dst ∨ dst + 32 * iter ≤ ptr)
    (hdisjointCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * iter ≤ ptr)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (fusedProgress memory activeWords (UInt256.ofNat dst) src modulus
        iter).memory ptr count value :=
  ⟨hrep.1, (memoryLimbs_fusedProgress_frame memory activeWords src modulus dst
    iter ptr count hdstFit hcandidateFit hdisjointDst hdisjointCandidate).trans
      hrep.2⟩

/-! ### The digit-list model of one pass -/

/-- The limbs and final carry of the fixed-width sum `dst + src`. -/
def fusedSums (memory : ByteArray) (dst src count : Nat) : List Nat × Nat :=
  Limbs.addDigitLists (Limbs.memoryLimbs memory dst count)
    (Limbs.memoryLimbs memory src count) 0

/-- The limbs and final borrow of the wrapped difference `(dst + src) - modulus`. -/
def fusedDiffs (memory : ByteArray) (dst src modulus count : Nat) :
    List Nat × Nat :=
  Limbs.subDigitLists (fusedSums memory dst src count).1
    (Limbs.memoryLimbs memory modulus count) 0

theorem fusedSums_length (memory : ByteArray) (dst src count : Nat) :
    (fusedSums memory dst src count).1.length = count := by
  rw [fusedSums, Limbs.length_addDigitLists_left (by simp)]
  simp

theorem fusedSums_carry_le_one (memory : ByteArray) (dst src count : Nat) :
    (fusedSums memory dst src count).2 ≤ 1 :=
  Limbs.addDigitLists_carry_le_one (by simp)
    (fun digit hdigit => Limbs.memoryLimb_lt memory dst count hdigit)
    (fun digit hdigit => Limbs.memoryLimb_lt memory src count hdigit) (by omega)

theorem fusedDiffs_borrow_le_one (memory : ByteArray)
    (dst src modulus count : Nat) :
    (fusedDiffs memory dst src modulus count).2 ≤ 1 :=
  Limbs.subDigitLists_borrow_le_one (by rw [fusedSums_length]; simp) (by omega)

theorem fusedSums_succ (memory : ByteArray) (dst src count : Nat) :
    fusedSums memory dst src (count + 1) =
      ((fusedSums memory dst src count).1 ++
          [((MachineState.readWord memory (dst + 32 * count)).toNat +
              (MachineState.readWord memory (src + 32 * count)).toNat +
              (fusedSums memory dst src count).2) % Limbs.radix],
        ((MachineState.readWord memory (dst + 32 * count)).toNat +
            (MachineState.readWord memory (src + 32 * count)).toNat +
            (fusedSums memory dst src count).2) / Limbs.radix) := by
  unfold fusedSums
  rw [memoryLimbs_succ, memoryLimbs_succ,
    Limbs.addDigitLists_append_single (by simp)]

theorem fusedDiffs_succ (memory : ByteArray) (dst src modulus count : Nat) :
    fusedDiffs memory dst src modulus (count + 1) =
      ((fusedDiffs memory dst src modulus count).1 ++
          [((MachineState.readWord memory (dst + 32 * count)).toNat +
                (MachineState.readWord memory (src + 32 * count)).toNat +
                (fusedSums memory dst src count).2) % Limbs.radix +
              Limbs.radix *
                (if ((MachineState.readWord memory (dst + 32 * count)).toNat +
                      (MachineState.readWord memory (src + 32 * count)).toNat +
                      (fusedSums memory dst src count).2) % Limbs.radix <
                    (MachineState.readWord memory (modulus + 32 * count)).toNat +
                      (fusedDiffs memory dst src modulus count).2 then 1 else 0) -
              (MachineState.readWord memory (modulus + 32 * count)).toNat -
            (fusedDiffs memory dst src modulus count).2],
        if ((MachineState.readWord memory (dst + 32 * count)).toNat +
              (MachineState.readWord memory (src + 32 * count)).toNat +
              (fusedSums memory dst src count).2) % Limbs.radix <
            (MachineState.readWord memory (modulus + 32 * count)).toNat +
              (fusedDiffs memory dst src modulus count).2 then 1 else 0) := by
  unfold fusedDiffs
  simp only [fusedSums_succ, memoryLimbs_succ]
  rw [Limbs.subDigitLists_append_single (by rw [fusedSums_length]; simp)]

/-- The one-pass loop realises `fusedSums` in the destination and `fusedDiffs`
in the scratch buffer, with the machine words tracking the mathematical carry
and borrow. -/
theorem fusedNatProgress_matches (memory : ByteArray) (activeWords : UInt256)
    (dst src modulus count iter : Nat) (hiter : iter ≤ count)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨ src + 32 * count ≤ dst)
    (hdstModulus : dst + 32 * count ≤ modulus ∨ modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ dst)
    (hsrcCandidate : src + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ src)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus) :
    let progress := fusedNatProgress memory activeWords dst src modulus iter
    Limbs.memoryLimbs progress.memory dst iter =
        (fusedSums memory dst src iter).1 ∧
      progress.carry.toNat = (fusedSums memory dst src iter).2 ∧
      Limbs.memoryLimbs progress.memory 5120 iter =
        (fusedDiffs memory dst src modulus iter).1 ∧
      progress.borrow.toNat = (fusedDiffs memory dst src modulus iter).2 := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [fusedNatProgress, fusedSums, fusedDiffs, Limbs.memoryLimbs,
        Limbs.addDigitLists, Limbs.subDigitLists, hzero]
  | succ iter ih =>
      have hi : iter < count := by omega
      have hprefix := ih (by omega)
      have hmemD : Limbs.memoryLimbs
          (fusedNatProgress memory activeWords dst src modulus iter).memory dst
          iter = (fusedSums memory dst src iter).1 := hprefix.1
      have hcarryEq :
          (fusedNatProgress memory activeWords dst src modulus iter).carry.toNat =
            (fusedSums memory dst src iter).2 := hprefix.2.1
      have hmemC : Limbs.memoryLimbs
          (fusedNatProgress memory activeWords dst src modulus iter).memory 5120
          iter = (fusedDiffs memory dst src modulus iter).1 := hprefix.2.2.1
      have hborrowEq :
          (fusedNatProgress memory activeWords dst src modulus iter).borrow.toNat =
            (fusedDiffs memory dst src modulus iter).2 := hprefix.2.2.2
      have hcarryLe :
          (fusedNatProgress memory activeWords dst src modulus iter).carry.toNat
            ≤ 1 := by
        rw [hcarryEq]
        exact fusedSums_carry_le_one memory dst src iter
      have hborrowLe :
          (fusedNatProgress memory activeWords dst src modulus iter).borrow.toNat
            ≤ 1 := by
        rw [hborrowEq]
        exact fusedDiffs_borrow_le_one memory dst src modulus iter
      have hx : MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (dst + 32 * iter) =
            MachineState.readWord memory (dst + 32 * iter) :=
        readWord_fusedNatProgress_stable memory activeWords dst src modulus iter
          (dst + 32 * iter) (by omega)
          (by rcases hdstCandidate with h | h
              · left; omega
              · right; omega)
      have hy : MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (src + 32 * iter) =
            MachineState.readWord memory (src + 32 * iter) :=
        readWord_fusedNatProgress_stable memory activeWords dst src modulus iter
          (src + 32 * iter)
          (by rcases halias with h | h | h
              · right; omega
              · right; omega
              · left; omega)
          (by rcases hsrcCandidate with h | h
              · left; omega
              · right; omega)
      have hm : MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (modulus + 32 * iter) =
            MachineState.readWord memory (modulus + 32 * iter) :=
        readWord_fusedNatProgress_stable memory activeWords dst src modulus iter
          (modulus + 32 * iter)
          (by rcases hdstModulus with h | h
              · right; omega
              · left; omega)
          (by rcases hmodulusCandidate with h | h
              · left; omega
              · right; omega)
      have hstepAdd := addLimbStep_fused
        (MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (dst + 32 * iter))
        (MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (src + 32 * iter))
        (fusedNatProgress memory activeWords dst src modulus iter).carry hcarryLe
      have hstepSub := subLimbStep_fused
        (MachineState.readWord
            (fusedNatProgress memory activeWords dst src modulus iter).memory
            (dst + 32 * iter) +
          MachineState.readWord
            (fusedNatProgress memory activeWords dst src modulus iter).memory
            (src + 32 * iter) +
          (fusedNatProgress memory activeWords dst src modulus iter).carry)
        (MachineState.readWord
          (fusedNatProgress memory activeWords dst src modulus iter).memory
          (modulus + 32 * iter))
        (fusedNatProgress memory activeWords dst src modulus iter).borrow hborrowLe
      have hdisjWrite : dst + 32 * iter ≤ 5120 + 32 * iter ∨
          5120 + 32 * iter + 32 ≤ dst := by
        rcases hdstCandidate with h | h
        · left; omega
        · right; omega
      have hdisjWrite' : 5120 + 32 * (iter + 1) ≤ dst + 32 * iter ∨
          dst + 32 * iter + 32 ≤ 5120 := by
        rcases hdstCandidate with h | h
        · right; omega
        · left; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [fusedNatProgress]
        rw [memoryLimbs_write_next,
          memoryLimbs_write_disjoint _ _ _ _ _ hdisjWrite, hmemD, fusedSums_succ]
        congr 2
        rw [hstepAdd.1, hx, hy, hcarryEq]
      · simp only [fusedNatProgress]
        rw [fusedSums_succ, hstepAdd.2, hx, hy, hcarryEq]
      · simp only [fusedNatProgress]
        rw [memoryLimbs_write_disjoint _ _ _ _ _ hdisjWrite',
          memoryLimbs_write_next, hmemC, fusedDiffs_succ]
        congr 2
        rw [hstepSub.1, hstepAdd.1, hx, hy, hcarryEq, hm, hborrowEq]
      · simp only [fusedNatProgress]
        rw [fusedDiffs_succ, hstepSub.2, hstepAdd.1, hx, hy, hcarryEq, hm,
          hborrowEq]

/-! ### Values carried by one fused pass -/

theorem fusedSums_digits_lt (memory : ByteArray) (dst src count : Nat)
    {digit : Nat} (hdigit : digit ∈ (fusedSums memory dst src count).1) :
    digit < Limbs.radix :=
  Limbs.addDigitLists_digits_lt hdigit

theorem fusedSums_value (memory : ByteArray) (dst src count x y : Nat)
    (hdst : Limbs.Represents memory dst count x)
    (hsrc : Limbs.Represents memory src count y) :
    Nat.ofDigits Limbs.radix (fusedSums memory dst src count).1 +
        Limbs.radix ^ count * (fusedSums memory dst src count).2 = x + y := by
  have hvalue := Limbs.addDigitLists_value (carry := 0)
    (xs := Limbs.memoryLimbs memory dst count)
    (ys := Limbs.memoryLimbs memory src count) (by simp)
  rw [Limbs.value_of_represents hdst, Limbs.value_of_represents hsrc,
    Nat.add_zero] at hvalue
  simpa [fusedSums] using hvalue

theorem fusedSums_lt (memory : ByteArray) (dst src count : Nat) :
    Nat.ofDigits Limbs.radix (fusedSums memory dst src count).1 <
      Limbs.radix ^ count := by
  have hlt := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one
    (fun digit hdigit => fusedSums_digits_lt memory dst src count hdigit)
  simpa [fusedSums_length] using hlt

theorem fusedSums_wrapped (memory : ByteArray) (dst src count x y : Nat)
    (hdst : Limbs.Represents memory dst count x)
    (hsrc : Limbs.Represents memory src count y) :
    Nat.ofDigits Limbs.radix (fusedSums memory dst src count).1 =
      (x + y) % Limbs.radix ^ count := by
  have hvalue := fusedSums_value memory dst src count x y hdst hsrc
  rw [← hvalue, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (fusedSums_lt memory dst src count)]

theorem fusedDiffs_value (memory : ByteArray)
    (dst src modulus count modulusValue : Nat)
    (hmodulus : Limbs.Represents memory modulus count modulusValue) :
    Nat.ofDigits Limbs.radix (fusedDiffs memory dst src modulus count).1 +
        modulusValue =
      Nat.ofDigits Limbs.radix (fusedSums memory dst src count).1 +
        Limbs.radix ^ count * (fusedDiffs memory dst src modulus count).2 := by
  have hvalue := Limbs.subDigitLists_value (borrow := 0)
    (xs := (fusedSums memory dst src count).1)
    (ys := Limbs.memoryLimbs memory modulus count)
    (by rw [fusedSums_length]; simp)
    (fun digit hdigit => fusedSums_digits_lt memory dst src count hdigit)
    (fun digit hdigit => Limbs.memoryLimb_lt memory modulus count hdigit)
    (by omega)
  rw [Limbs.value_of_represents hmodulus, Nat.add_zero, fusedSums_length]
    at hvalue
  simpa [fusedDiffs] using hvalue

/-! ### The conditional-copy selector -/

theorem carry_eq_one_iff {wrapped bound carry total : Nat}
    (hwrapped : wrapped < bound) (hcarry : carry ≤ 1)
    (hvalue : wrapped + bound * carry = total) :
    carry = 1 ↔ bound ≤ total := by
  interval_cases carry <;> omega

theorem borrow_eq_zero_iff {candidate modulus wrapped bound borrow : Nat}
    (hcandidate : candidate < bound) (_hmodulus : modulus < bound)
    (hborrow : borrow ≤ 1)
    (hvalue : candidate + modulus = wrapped + bound * borrow) :
    borrow = 0 ↔ modulus ≤ wrapped := by
  interval_cases borrow <;> omega

/-- The exit block computes `skip = borrow & iszero carry` and jumps past the
copy when it is set; the copy therefore runs exactly on
`carry = 1 ∨ borrow = 0`. -/
theorem skip_eq_zero_iff (carry borrow : UInt256)
    (hcarry : carry.toNat ≤ 1) (hborrow : borrow.toNat ≤ 1) :
    (UInt256.land borrow (UInt256.isZero carry)).toNat = 0 ↔
      (carry.toNat = 1 ∨ borrow.toNat = 0) := by
  simp only [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_isZero]
  interval_cases carry.toNat <;> interval_cases borrow.toNat <;> decide

/-! ### The `MCOPY` selection -/

/-- The `MCOPY` size word the exit block computes: `count << 5`. -/
def copySize (count : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 5)

theorem copySize_toNat (count : Nat) (hfit : 32 * count < 2 ^ 256) :
    (copySize count).toNat = 32 * count := by
  have h32 : (2 : Nat) ^ 5 = 32 := by norm_num
  have hcount : count < 2 ^ 256 := by omega
  have hres : count * 2 ^ 5 < 2 ^ 256 := by rw [h32]; omega
  rw [copySize,
    Challenge.EvmProof.Word.shiftLeft_ofNat hcount (by norm_num) hres,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hres, h32]
  omega

/-- Whole-buffer selection: on `useSub` the wrapped difference at `0x1400`
replaces the sum in `dst`; otherwise memory is untouched. -/
def selectedMemory (memory : ByteArray) (dst : UInt256) (count : Nat)
    (useSub : UInt256) : ByteArray :=
  if useSub.toNat = 0 then memory
  else MachineState.writeBytes memory
    (MachineState.readPadded memory 5120 (copySize count).toNat) dst.toNat

/-- The active-word high-water mark after the conditional `MCOPY`. -/
def selectedActiveWords (activeWords dst : UInt256) (count : Nat)
    (useSub : UInt256) : UInt256 :=
  if useSub.toNat = 0 then activeWords
  else UInt256.ofNat (MachineState.activeWordsAfter
    (MachineState.activeWordsAfter activeWords.toNat dst.toNat
      (copySize count).toNat) 5120 (copySize count).toNat)

/-- The `skip` word the exit block tests: `borrow & iszero carry`. -/
def addSkip (memory : ByteArray) (activeWords dst src modulus : UInt256)
    (count : Nat) : UInt256 :=
  let progress := fusedProgress memory activeWords dst src modulus count
  UInt256.land progress.borrow (UInt256.isZero progress.carry)

/-- `useSub` is the negation of `skip`; the copy runs exactly when it is set. -/
def addUseSub (memory : ByteArray) (activeWords dst src modulus : UInt256)
    (count : Nat) : UInt256 :=
  UInt256.isZero (addSkip memory activeWords dst src modulus count)

/-! ### Choosing between the sum and the wrapped difference -/

/-- When the selector fires the scratch buffer already holds `total % modulus`. -/
theorem selected_value_eq {total modulusValue bound wrapped candidate carry
    borrow : Nat}
    (htotalLt : total < 2 * modulusValue)
    (hmodulusBound : modulusValue < bound)
    (hwrappedLt : wrapped < bound) (hcandidateLt : candidate < bound)
    (hcarryLe : carry ≤ 1) (hborrowLe : borrow ≤ 1)
    (hcarryValue : wrapped + bound * carry = total)
    (hborrowValue : candidate + modulusValue = wrapped + bound * borrow)
    (huse : carry = 1 ∨ borrow = 0) :
    candidate = total % modulusValue := by
  have hcases : (carry = 0 ∨ carry = 1) ∧ (borrow = 0 ∨ borrow = 1) := by
    omega
  obtain ⟨hc, hb⟩ := hcases
  have hge : modulusValue ≤ total := by
    rcases huse with h | h
    · subst h
      omega
    · subst h
      rcases hc with hc | hc <;> subst hc <;> omega
  rw [Limbs.mod_eq_cond_sub htotalLt, if_neg (by omega)]
  rcases hc with hc | hc <;> rcases hb with hb | hb <;> subst hc <;> subst hb <;>
    omega

/-- When the selector does not fire the destination already holds
`total % modulus`. -/
theorem unselected_value_eq {total modulusValue bound wrapped candidate carry
    borrow : Nat}
    (htotalLt : total < 2 * modulusValue)
    (_hmodulusBound : modulusValue < bound)
    (_hwrappedLt : wrapped < bound) (hcandidateLt : candidate < bound)
    (hcarryLe : carry ≤ 1) (hborrowLe : borrow ≤ 1)
    (hcarryValue : wrapped + bound * carry = total)
    (hborrowValue : candidate + modulusValue = wrapped + bound * borrow)
    (huse : ¬ (carry = 1 ∨ borrow = 0)) :
    wrapped = total % modulusValue := by
  have hc : carry = 0 := by omega
  have hb : borrow = 1 := by omega
  subst hc
  subst hb
  rw [Limbs.mod_eq_cond_sub htotalLt, if_pos (by omega)]
  omega

/-! ### The helper's exit state -/

/-- Memory after the routine.  On the `take * count = 0` fast path nothing is
written at all.  Phrased over the caller's memory and active-word count rather
than its whole state, so that the record updates the callers stack up
normalise away. -/
def addFinalMemory (memory : ByteArray)
    (activeWords dst src take modulus : UInt256) (count : Nat) : ByteArray :=
  if (take * UInt256.ofNat count).toNat = 0 then memory
  else
    selectedMemory
      (fusedProgress memory activeWords dst src modulus count).memory dst
      count (addUseSub memory activeWords dst src modulus count)

def addFinalActiveWords (memory : ByteArray)
    (activeWords dst src take modulus : UInt256) (count : Nat) : UInt256 :=
  if (take * UInt256.ofNat count).toNat = 0 then activeWords
  else
    selectedActiveWords
      (fusedProgress memory activeWords dst src modulus count).activeWords
      dst count (addUseSub memory activeWords dst src modulus count)

def addReturned (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rest
           memory := addFinalMemory s.memory s.activeWords dst src take modulus
             count
           activeWords := addFinalActiveWords s.memory s.activeWords dst src take
             modulus count }

/-! ### Functional contract for `addMaskedMod`

`addReturned_represents_mod` and `addReturned_preserves_region` are the only
two facts the callers use.  Their statements are unchanged apart from the
trailing `hsrcCandidate` hypothesis, which is discharged automatically at every
call site: the fused routine reads `src` limb `i` *after* it has written
scratch limbs `0 … i-1`, so the source region must be disjoint from the private
`0x1400` buffer (clause three of the routine's precondition P3).  The
three-pass helper it replaces read all of `src` before touching the scratch and
so did not need it. -/

theorem addReturned_represents_mod (s : State)
    (dst src modulus count take x y modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (htake : take ≤ 1)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hsrcFit : src + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus)
    (hdst : Limbs.Represents s.memory dst count x)
    (hsrc : Limbs.Represents s.memory src count y)
    (hmodulus : Limbs.Represents s.memory modulus count modulusValue)
    (hx : x < modulusValue) (hy : y ≤ modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hsrcCandidate : src + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ src := by omega) :
    Limbs.Represents
      (addReturned s (UInt256.ofNat dst) (UInt256.ofNat src)
        (UInt256.ofNat take) (UInt256.ofNat modulus) count returnDest rest).memory
      dst count ((x + take * y) % modulusValue) := by
  have hmodulusPos : 0 < modulusValue := by omega
  have hcountPos : 0 < count := by
    rcases Nat.eq_zero_or_pos count with hzero | hpos
    · subst hzero
      rw [pow_zero] at hmodulusBound
      omega
    · exact hpos
  have hcountFit : count < 2 ^ 256 := by omega
  interval_cases take
  · have hguard : ((UInt256.ofNat 0) * UInt256.ofNat count).toNat = 0 := by
      rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat]
      simp
    rw [show (x + 0 * y) % modulusValue = x by
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hx]]
    simpa [addReturned, addFinalMemory, hguard] using hdst
  · have hguard : ¬ ((UInt256.ofNat 1) * UInt256.ofNat count).toNat = 0 := by
      rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hcountFit,
        Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256), Nat.one_mul,
        Nat.mod_eq_of_lt hcountFit]
      omega
    have hnat : fusedProgress s.memory s.activeWords (UInt256.ofNat dst)
        (UInt256.ofNat src) (UInt256.ofNat modulus) count =
          fusedNatProgress s.memory s.activeWords dst src modulus count :=
      fusedProgress_eq_nat s.memory s.activeWords dst src modulus count hdstFit
        hsrcFit hmodulusFit hcandidateFit
    obtain ⟨hmemD, hcarryEq, hmemC, hborrowEq⟩ :=
      fusedNatProgress_matches s.memory s.activeWords dst src modulus count count
        (by omega) halias hdstModulus hdstCandidate hsrcCandidate
        hmodulusCandidate
    have hwrappedLt : (x + y) % Limbs.radix ^ count < Limbs.radix ^ count :=
      Nat.mod_lt _ (pow_pos Limbs.radix_pos _)
    have hcandidateLt :
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).memory 5120 count) < Limbs.radix ^ count :=
      memoryLimbs_value_lt _ 5120 count
    have hcarryLe :
        (fusedNatProgress s.memory s.activeWords dst src modulus
          count).carry.toNat ≤ 1 := by
      rw [hcarryEq]
      exact fusedSums_carry_le_one s.memory dst src count
    have hborrowLe :
        (fusedNatProgress s.memory s.activeWords dst src modulus
          count).borrow.toNat ≤ 1 := by
      rw [hborrowEq]
      exact fusedDiffs_borrow_le_one s.memory dst src modulus count
    have hcarryValue : (x + y) % Limbs.radix ^ count +
        Limbs.radix ^ count *
          (fusedNatProgress s.memory s.activeWords dst src modulus
            count).carry.toNat = x + y := by
      rw [hcarryEq, ← fusedSums_wrapped s.memory dst src count x y hdst hsrc]
      exact fusedSums_value s.memory dst src count x y hdst hsrc
    have hborrowValue :
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).memory 5120 count) + modulusValue =
          (x + y) % Limbs.radix ^ count +
            Limbs.radix ^ count *
              (fusedNatProgress s.memory s.activeWords dst src modulus
                count).borrow.toNat := by
      rw [hmemC, hborrowEq, ← fusedSums_wrapped s.memory dst src count x y hdst
        hsrc]
      exact fusedDiffs_value s.memory dst src modulus count modulusValue hmodulus
    have htotalLt : x + y < 2 * modulusValue := by omega
    have hsumRep : Limbs.Represents
        (fusedNatProgress s.memory s.activeWords dst src modulus count).memory
        dst count ((x + y) % Limbs.radix ^ count) := by
      rw [Limbs.represents_iff_value hwrappedLt, hmemD]
      exact fusedSums_wrapped s.memory dst src count x y hdst hsrc
    have hcandidateRep : Limbs.Represents
        (fusedNatProgress s.memory s.activeWords dst src modulus count).memory
        5120 count
        (Nat.ofDigits Limbs.radix (Limbs.memoryLimbs
          (fusedNatProgress s.memory s.activeWords dst src modulus
            count).memory 5120 count)) :=
      represents_memoryLimbs_value _ 5120 count
    have hdstNat : (UInt256.ofNat dst).toNat = dst := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsize : (copySize count).toNat = 32 * count :=
      copySize_toNat count (by omega)
    have hgoal : Limbs.Represents
        (selectedMemory
          (fusedNatProgress s.memory s.activeWords dst src modulus count).memory
          (UInt256.ofNat dst) count
          (UInt256.isZero (UInt256.land
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).borrow
            (UInt256.isZero (fusedNatProgress s.memory s.activeWords dst src
              modulus count).carry))))
        dst count ((x + y) % modulusValue) := by
      by_cases hskip : (UInt256.land
          (fusedNatProgress s.memory s.activeWords dst src modulus count).borrow
          (UInt256.isZero (fusedNatProgress s.memory s.activeWords dst src
            modulus count).carry)).toNat = 0
      · have huse := (skip_eq_zero_iff _ _ hcarryLe hborrowLe).mp hskip
        have hnotZero : ¬ (UInt256.isZero (UInt256.land
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).borrow
            (UInt256.isZero (fusedNatProgress s.memory s.activeWords dst src
              modulus count).carry))).toNat = 0 := by
          rw [Challenge.EvmProof.Word.word_toNat_isZero, if_pos hskip]
          omega
        have hcandidateEq :
            Nat.ofDigits Limbs.radix (Limbs.memoryLimbs
              (fusedNatProgress s.memory s.activeWords dst src modulus
                count).memory 5120 count) = (x + y) % modulusValue :=
          selected_value_eq htotalLt hmodulusBound hwrappedLt hcandidateLt
            hcarryLe hborrowLe hcarryValue hborrowValue huse
        have hmc := Mcopy.represents_mcopy
          (fusedNatProgress s.memory s.activeWords dst src modulus count).memory
          dst 5120 count _ hcandidateRep
        rw [hcandidateEq] at hmc
        unfold selectedMemory
        rw [if_neg hnotZero, hsize, hdstNat]
        exact hmc
      · have huse := hskip
        have hzeroEq : (UInt256.isZero (UInt256.land
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).borrow
            (UInt256.isZero (fusedNatProgress s.memory s.activeWords dst src
              modulus count).carry))).toNat = 0 := by
          rw [Challenge.EvmProof.Word.word_toNat_isZero, if_neg hskip]
        have hwrappedEq : (x + y) % Limbs.radix ^ count = (x + y) % modulusValue :=
          unselected_value_eq htotalLt hmodulusBound hwrappedLt hcandidateLt
            hcarryLe hborrowLe hcarryValue hborrowValue
            (fun h => huse ((skip_eq_zero_iff _ _ hcarryLe hborrowLe).mpr h))
        rw [← hwrappedEq]
        unfold selectedMemory
        rw [if_pos hzeroEq]
        exact hsumRep
    have hmem : (addReturned s (UInt256.ofNat dst) (UInt256.ofNat src)
        (UInt256.ofNat 1) (UInt256.ofNat modulus) count returnDest rest).memory =
        selectedMemory
          (fusedNatProgress s.memory s.activeWords dst src modulus count).memory
          (UInt256.ofNat dst) count
          (UInt256.isZero (UInt256.land
            (fusedNatProgress s.memory s.activeWords dst src modulus
              count).borrow
            (UInt256.isZero (fusedNatProgress s.memory s.activeWords dst src
              modulus count).carry))) := by
      simp only [addReturned, addFinalMemory, addUseSub, addSkip, if_neg hguard,
        hnat]
    rw [Nat.one_mul, hmem]
    exact hgoal

theorem addReturned_preserves_region (s : State)
    (dst src take modulus ptr count value : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (addReturned s (UInt256.ofNat dst) (UInt256.ofNat src)
        (UInt256.ofNat take) (UInt256.ofNat modulus) count returnDest rest).memory
      ptr count value := by
  by_cases hguard : ((UInt256.ofNat take) * UInt256.ofNat count).toNat = 0
  · simpa [addReturned, addFinalMemory, hguard] using hrep
  · set progress := fusedProgress s.memory s.activeWords (UInt256.ofNat dst)
      (UInt256.ofNat src) (UInt256.ofNat modulus) count with hprogressDef
    have hpass : Limbs.Represents progress.memory ptr count value :=
      represents_fusedProgress_frame s.memory s.activeWords (UInt256.ofNat src)
        (UInt256.ofNat modulus) dst count ptr count value hdstFit hcandidateFit
        (by omega) (by omega) hrep
    have hdstNat : (UInt256.ofNat dst).toNat = dst := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsize : (copySize count).toNat = 32 * count :=
      copySize_toNat count (by omega)
    have hgoal : Limbs.Represents
        (selectedMemory progress.memory (UInt256.ofNat dst) count
          (addUseSub s.memory s.activeWords (UInt256.ofNat dst)
            (UInt256.ofNat src) (UInt256.ofNat modulus) count))
        ptr count value := by
      by_cases hzero : (addUseSub s.memory s.activeWords (UInt256.ofNat dst)
          (UInt256.ofNat src) (UInt256.ofNat modulus) count).toNat = 0
      · simpa [selectedMemory, hzero] using hpass
      · have hmc := Mcopy.represents_mcopy_disjoint_region progress.memory dst
          5120 count ptr count value
          (by rcases hptrDst with h | h
              · exact Or.inr h
              · exact Or.inl h)
          hpass
        simpa [selectedMemory, hzero, hsize, hdstNat] using hmc
    simpa [addReturned, addFinalMemory, hguard, hprogressDef] using hgoal

/-! ### Symbolic states of the routine -/

def addEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1448
           stack := [dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

/-- After `DUP5 ; DUP4 ; MUL`: the guard word `take * count` sits on top of the
argument frame, one block before the `JUMPI` that tests it. -/
def addTested (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1452
           stack := [take * UInt256.ofNat count, dst, src, take, modulus,
             UInt256.ofNat count, returnDest] ++ rest }

/-- The fall-through of the entry guard: nothing to do, drop the frame. -/
def addZeroEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1456
           stack := [dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

/-- The taken branch of the entry guard: build the loop frame. -/
def addGoEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1462
           stack := [dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

/-- The ten frame slots below the loop's three working registers. -/
def fusedTail (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [src - dst, modulus - dst, UInt256.ofNat 5120 - dst, dst + copySize count,
   dst, src, take, modulus, UInt256.ofNat count, returnDest] ++ rest

/-- Loop head after `i` limbs. -/
def fusedLoop (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fusedProgress s.memory s.activeWords dst src modulus i
  { s with pc := UInt256.ofNat 1483
           stack := [UInt256.ofNat (32 * i) + dst, progress.carry,
               progress.borrow] ++
             fusedTail dst src take modulus count returnDest rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-- End of the loop body: the continuation flag is computed here, one block
before the `JUMPI` that tests it. -/
def fusedTested (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fusedProgress s.memory s.activeWords dst src modulus (i + 1)
  { s with pc := UInt256.ofNat 1534
           stack := [UInt256.lt (UInt256.ofNat (32 * (i + 1)) + dst)
                 (dst + copySize count),
               UInt256.ofNat (32 * (i + 1)) + dst, progress.carry,
               progress.borrow] ++
             fusedTail dst src take modulus count returnDest rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-- Entry to the selection block. -/
def fusedSelEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { fusedLoop s dst src take modulus count count returnDest rest with
      pc := UInt256.ofNat 1538 }

/-- After `DUP2 ; ISZERO ; DUP4 ; AND`: the `skip` word is on top. -/
def fusedSkipTested (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fusedProgress s.memory s.activeWords dst src modulus count
  { s with pc := UInt256.ofNat 1542
           stack := [addSkip s.memory s.activeWords dst src modulus count,
               UInt256.ofNat (32 * count) + dst, progress.carry,
               progress.borrow] ++
             fusedTail dst src take modulus count returnDest rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-- The not-taken branch of the selector: the `MCOPY` runs. -/
def fusedCopyEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { fusedLoop s dst src take modulus count count returnDest rest with
      pc := UInt256.ofNat 1546 }

/-- The join point at pc 1555, reached either by skipping or by copying. -/
def fusedFinEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fusedProgress s.memory s.activeWords dst src modulus count
  { s with pc := UInt256.ofNat 1555
           stack := [UInt256.ofNat (32 * count) + dst, progress.carry,
               progress.borrow] ++
             fusedTail dst src take modulus count returnDest rest
           memory := selectedMemory progress.memory dst count
             (addUseSub s.memory s.activeWords dst src modulus count)
           activeWords := selectedActiveWords progress.activeWords dst count
             (addUseSub s.memory s.activeWords dst src modulus count) }

@[simp] theorem fusedLoop_executionEnv (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (fusedLoop s dst src take modulus count i returnDest rest).executionEnv =
      s.executionEnv := rfl

@[simp] theorem fusedLoop_halt (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (fusedLoop s dst src take modulus count i returnDest rest).halt = s.halt := rfl

@[simp] theorem fusedTested_executionEnv (s : State)
    (dst src take modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (fusedTested s dst src take modulus count i returnDest rest).executionEnv =
      s.executionEnv := rfl

@[simp] theorem fusedTested_halt (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (fusedTested s dst src take modulus count i returnDest rest).halt =
      s.halt := rfl

@[simp] theorem fusedSkipTested_executionEnv (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (fusedSkipTested s dst src take modulus count returnDest rest).executionEnv =
      s.executionEnv := rfl

@[simp] theorem fusedSkipTested_halt (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (fusedSkipTested s dst src take modulus count returnDest rest).halt =
      s.halt := rfl

@[simp] theorem fusedFinEntry_executionEnv (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (fusedFinEntry s dst src take modulus count returnDest rest).executionEnv =
      s.executionEnv := rfl

@[simp] theorem fusedFinEntry_halt (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (fusedFinEntry s dst src take modulus count returnDest rest).halt =
      s.halt := rfl

/-! ### Located paths -/

def ammEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1071 .JUMPDEST, opAt 1072 (.Dup ⟨4, by decide⟩),
   opAt 1073 (.Dup ⟨3, by decide⟩), opAt 1074 .MUL]

def ammTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1075 2 1462, opAt 1076 .JUMPI]

def ammZeroPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1077 .POP, opAt 1078 .POP, opAt 1079 .POP, opAt 1080 .POP,
   opAt 1081 .POP, opAt 1082 .JUMP]

def ammGoPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1083 .JUMPDEST, opAt 1084 (.Dup ⟨4, by decide⟩), pushAt 1085 1 5,
   opAt 1086 .SHL, opAt 1087 (.Dup ⟨1, by decide⟩), opAt 1088 .ADD,
   opAt 1089 (.Dup ⟨1, by decide⟩), pushAt 1090 2 5120, opAt 1091 .SUB,
   opAt 1092 (.Dup ⟨2, by decide⟩), opAt 1093 (.Dup ⟨6, by decide⟩),
   opAt 1094 .SUB, opAt 1095 (.Dup ⟨3, by decide⟩),
   opAt 1096 (.Dup ⟨5, by decide⟩), opAt 1097 .SUB, pushAt 1098 0 0,
   pushAt 1099 0 0, opAt 1100 (.Dup ⟨6, by decide⟩)]

def fusedBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1101 .JUMPDEST, opAt 1102 (.Dup ⟨0, by decide⟩), opAt 1103 .MLOAD,
   opAt 1104 (.Dup ⟨4, by decide⟩), opAt 1105 (.Dup ⟨2, by decide⟩),
   opAt 1106 .ADD, opAt 1107 .MLOAD, opAt 1108 (.Dup ⟨1, by decide⟩),
   opAt 1109 .ADD, opAt 1110 (.Dup ⟨0, by decide⟩),
   opAt 1111 (.Swap ⟨1, by decide⟩), opAt 1112 .GT,
   opAt 1113 (.Dup ⟨3, by decide⟩), opAt 1114 (.Dup ⟨2, by decide⟩),
   opAt 1115 .ADD, opAt 1116 (.Dup ⟨0, by decide⟩),
   opAt 1117 (.Swap ⟨2, by decide⟩), opAt 1118 .GT, opAt 1119 .OR,
   opAt 1120 (.Swap ⟨2, by decide⟩), opAt 1121 .POP,
   opAt 1122 (.Dup ⟨5, by decide⟩), opAt 1123 (.Dup ⟨2, by decide⟩),
   opAt 1124 .ADD, opAt 1125 .MLOAD, opAt 1126 (.Dup ⟨1, by decide⟩),
   opAt 1127 .SUB, opAt 1128 (.Dup ⟨0, by decide⟩),
   opAt 1129 (.Dup ⟨2, by decide⟩), opAt 1130 .LT,
   opAt 1131 (.Dup ⟨5, by decide⟩), opAt 1132 (.Dup ⟨2, by decide⟩),
   opAt 1133 .SUB, opAt 1134 (.Dup ⟨0, by decide⟩),
   opAt 1135 (.Swap ⟨2, by decide⟩), opAt 1136 .LT, opAt 1137 .OR,
   opAt 1138 (.Swap ⟨4, by decide⟩), opAt 1139 .POP,
   opAt 1140 (.Dup ⟨7, by decide⟩), opAt 1141 (.Dup ⟨3, by decide⟩),
   opAt 1142 .ADD, opAt 1143 .MSTORE, opAt 1144 (.Dup ⟨1, by decide⟩),
   opAt 1145 .MSTORE, pushAt 1146 1 32, opAt 1147 .ADD,
   opAt 1148 (.Dup ⟨6, by decide⟩), opAt 1149 (.Dup ⟨1, by decide⟩),
   opAt 1150 .LT]

def fusedTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1151 2 1483, opAt 1152 .JUMPI]

def selectTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1153 (.Dup ⟨1, by decide⟩), opAt 1154 .ISZERO,
   opAt 1155 (.Dup ⟨3, by decide⟩), opAt 1156 .AND]

def selectJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1157 2 1555, opAt 1158 .JUMPI]

def selectCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1159 (.Dup ⟨11, by decide⟩), pushAt 1160 1 5, opAt 1161 .SHL,
   pushAt 1162 2 5120, opAt 1163 (.Dup ⟨9, by decide⟩), opAt 1164 .MCOPY]

def finishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1165 .JUMPDEST, opAt 1166 .POP, opAt 1167 .POP, opAt 1168 .POP,
   opAt 1169 .POP, opAt 1170 .POP, opAt 1171 .POP, opAt 1172 .POP,
   opAt 1173 .POP, opAt 1174 .POP, opAt 1175 .POP, opAt 1176 .POP,
   opAt 1177 .POP, opAt 1178 .JUMP]

@[simp] private theorem fusedPCs (i : Nat) (hi : 1071 ≤ i) (hii : i ≤ 1178) :
    Artifact.submissionArtifact.instructionPC i =
      ([1448,1449,1450,1451,1452,1455,1456,1457,1458,1459,1460,1461,1462,
       1463,1464,1466,1467,1468,1469,1470,1473,1474,1475,1476,1477,1478,
       1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,
       1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,
       1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,
       1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1530,1531,
       1532,1533,1534,1537,1538,1539,1540,1541,1542,1545,1546,1547,1549,
       1550,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,
       1565,1566,1567,1568])[i - 1071]! := by
  interval_cases i <;> decide

@[simp] private theorem jump1462 :
    Decode.isValidJumpDest submissionBytecode 1462 = true :=
  Artifact.isValidJumpDest_index 1083 (by rfl)

@[simp] private theorem jump1483 :
    Decode.isValidJumpDest submissionBytecode 1483 = true :=
  Artifact.isValidJumpDest_index 1101 (by rfl)

@[simp] private theorem jump1555 :
    Decode.isValidJumpDest submissionBytecode 1555 = true :=
  Artifact.isValidJumpDest_index 1165 (by rfl)

/-! ### Block certificates -/

set_option linter.unusedSimpArgs false in
theorem run_addEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammEntryPath
      (addEntry s dst src take modulus count returnDest rest) =
        some (addTested s dst src take modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [ammEntryPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addEntry, addTested, fusedPCs, hc6, hc7, hc8, hc9, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_addTestZero (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hguard : (take * UInt256.ofNat count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammTestPath
      (addTested s dst src take modulus count returnDest rest) =
        some (addZeroEntry s dst src take modulus count returnDest rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [ammTestPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addTested, addZeroEntry, fusedPCs, hc7, hc8, hrun, UInt256.isTrue, hguard,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_addTestGo (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hguard : ¬ (take * UInt256.ofNat count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammTestPath
      (addTested s dst src take modulus count returnDest rest) =
        some (addGoEntry s dst src take modulus count returnDest rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdest : (1462 : UInt256) = UInt256.ofNat 1462 := by decide
  have hdestNat : (1462 : UInt256).toNat = 1462 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (1462 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump1462
  simp [ammTestPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addTested, addGoEntry, fusedPCs, hc7, hc8, hcode, hrun, UInt256.isTrue,
    hguard, hdest, hdestNat, hjump, jump1462,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_addZero (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hguard : (take * UInt256.ofNat count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammZeroPath
      (addZeroEntry s dst src take modulus count returnDest rest) =
        some (addReturned s dst src take modulus count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [ammZeroPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addZeroEntry, addReturned, addFinalMemory, addFinalActiveWords, fusedPCs,
    hc1, hc2, hc3, hc4, hc5, hc6, hcode, hvalid, hrun, hguard,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_addGo (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammGoPath
      (addGoEntry s dst src take modulus count returnDest rest) =
        some (fusedLoop s dst src take modulus count 0 returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hzero : ({ val := 0 } : UInt256) = (0 : UInt256) := by decide
  have hzeroAdd : UInt256.ofNat 0 + dst = dst := by
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.zero_add]
    exact Nat.mod_eq_of_lt dst.val.isLt
  simp [ammGoPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addGoEntry, fusedLoop, fusedTail, fusedProgress, copySize, fusedPCs,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hrun, hfive, hfiveK, hzero,
    hzeroAdd,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_fusedBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedBodyPath
      (fusedLoop s dst src take modulus count i returnDest rest) =
        some (fusedTested s dst src take modulus count i returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hsp := word_shift_sub_cancel (UInt256.ofNat (32 * i)) dst src
  have hmp := word_shift_sub_cancel (UInt256.ofNat (32 * i)) dst modulus
  have hcp := word_shift_sub_cancel (UInt256.ofNat (32 * i)) dst
    (UInt256.ofNat 5120)
  have hnext : (32 : UInt256) + (UInt256.ofNat (32 * i) + dst) =
      UInt256.ofNat (32 * (i + 1)) + dst := by
    rw [← word_add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      show 32 + 32 * i = 32 * (i + 1) by omega]
  simp (config := { maxSteps := 1200000 })
    [fusedBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      fusedLoop, fusedTested, fusedTail, fusedProgress, fusedPCs,
      hc13, hc14, hc15, hc16, hc17, hc18, hc19, hrun,
      hsp, hmp, hcp, hnext, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_fusedNext (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hcond : (UInt256.lt (UInt256.ofNat (32 * (i + 1)) + dst)
      (dst + copySize count)).toNat = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedTestPath
      (fusedTested s dst src take modulus count i returnDest rest) =
        some (fusedLoop s dst src take modulus count (i + 1) returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : (1483 : UInt256) = UInt256.ofNat 1483 := by decide
  have hdestNat : (1483 : UInt256).toNat = 1483 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (1483 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump1483
  simp [fusedTestPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedTested, fusedLoop, fusedTail, fusedPCs, hc13, hc14, hc15, hcode, hrun,
    UInt256.isTrue, hcond, hdest, hdestNat, hjump, jump1483,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_fusedExit (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hlast : i + 1 = count)
    (hrun : s.halt = .Running)
    (hcond : (UInt256.lt (UInt256.ofNat (32 * (i + 1)) + dst)
      (dst + copySize count)).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedTestPath
      (fusedTested s dst src take modulus count i returnDest rest) =
        some (fusedSelEntry s dst src take modulus count returnDest rest) := by
  subst hlast
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [fusedTestPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedTested, fusedSelEntry, fusedLoop, fusedTail, fusedPCs, hc13, hc14, hc15,
    hrun, UInt256.isTrue, hcond,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_selectTest (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectTestPath
      (fusedSelEntry s dst src take modulus count returnDest rest) =
        some (fusedSkipTested s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [selectTestPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedSelEntry, fusedLoop, fusedSkipTested, fusedTail, addSkip, fusedPCs,
    hc13, hc14, hc15, hc16, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_selectSkip (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hskip : ¬ (addSkip s.memory s.activeWords dst src modulus count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectJumpPath
      (fusedSkipTested s dst src take modulus count returnDest rest) =
        some (fusedFinEntry s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : (1555 : UInt256) = UInt256.ofNat 1555 := by decide
  have hdestNat : (1555 : UInt256).toNat = 1555 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (1555 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump1555
  have huse : (addUseSub s.memory s.activeWords dst src modulus count).toNat = 0 := by
    rw [addUseSub, Challenge.EvmProof.Word.word_toNat_isZero, if_neg hskip]
  simp [selectJumpPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedSkipTested, fusedFinEntry, fusedTail, selectedMemory,
    selectedActiveWords, fusedPCs, hc13, hc14, hc15, hcode, hrun,
    UInt256.isTrue, hskip, huse, hdest, hdestNat, hjump, jump1555,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_selectFall (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hskip : (addSkip s.memory s.activeWords dst src modulus count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectJumpPath
      (fusedSkipTested s dst src take modulus count returnDest rest) =
        some (fusedCopyEntry s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [selectJumpPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedSkipTested, fusedCopyEntry, fusedLoop, fusedTail, fusedPCs,
    hc13, hc14, hc15, hrun, UInt256.isTrue, hskip,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_selectCopy (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running)
    (hskip : (addSkip s.memory s.activeWords dst src modulus count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectCopyPath
      (fusedCopyEntry s dst src take modulus count returnDest rest) =
        some (fusedFinEntry s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hfiveKNat : (5120 : UInt256).toNat = 5120 := by decide
  have huse : ¬ (addUseSub s.memory s.activeWords dst src modulus count).toNat = 0 := by
    rw [addUseSub, Challenge.EvmProof.Word.word_toNat_isZero, if_pos hskip]
    omega
  simp [selectCopyPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedCopyEntry, fusedLoop, fusedFinEntry, fusedTail, selectedMemory,
    selectedActiveWords, copySize, fusedPCs, hc13, hc14, hc15, hc16, hc17, hrun,
    huse, hfive, hfiveK, hfiveKNat, State.activeWordsAfterUInt256_2,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_finish (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hguard : ¬ (take * UInt256.ofNat count).toNat = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath
      (fusedFinEntry s dst src take modulus count returnDest rest) =
        some (addReturned s dst src take modulus count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [finishPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedFinEntry, fusedTail, addReturned, addFinalMemory, addFinalActiveWords,
    fusedPCs, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12,
    hc13, hcode, hvalid, hrun, hguard,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ### Loop-bound arithmetic -/

theorem copySize_eq_ofNat (count : Nat) (hfit : 32 * count < 2 ^ 256) :
    copySize count = UInt256.ofNat (32 * count) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [copySize_toNat count hfit, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hfit]

/-- The loop's continuation test compares the advanced pointer with
`dst + 32 * count`; with no wrap-around it is exactly `j < count`. -/
theorem fusedCond_toNat (dst : UInt256) (count j : Nat)
    (hfit : dst.toNat + 32 * count < 2 ^ 256) (hj : j ≤ count) :
    (UInt256.lt (UInt256.ofNat (32 * j) + dst) (dst + copySize count)).toNat =
      if j < count then 1 else 0 := by
  have hdp : (UInt256.ofNat (32 * j) + dst).toNat = 32 * j + dst.toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 32 * j < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : 32 * j + dst.toNat < 2 ^ 256)]
  have hend : (dst + copySize count).toNat = dst.toNat + 32 * count := by
    rw [Challenge.EvmProof.Word.word_toNat_add, copySize_toNat count (by omega),
      Nat.mod_eq_of_lt (by omega : dst.toNat + 32 * count < 2 ^ 256)]
  rw [Challenge.EvmProof.Word.word_toNat_lt, hdp, hend]
  split_ifs <;> omega

/-! ### Whole-helper execution certificate -/

def gasSteps_addEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (addTested s dst src take modulus count returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka ammEntryPath
      (by simpa [addEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [addEntry, State.fork] using hfork)
      (run_addEntry s dst src take modulus count returnDest rest hcap hrun)
      (by simpa [addEntry] using hrun)
      (by simpa [addEntry, State.fork] using hnp)

def gasSteps_fusedIteration (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < count)
    (hfit : dst.toNat + 32 * count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedLoop s dst src take modulus count i returnDest rest)
      (fusedLoop s dst src take modulus count (i + 1) returnDest rest) :=
  have hcond : (UInt256.lt (UInt256.ofNat (32 * (i + 1)) + dst)
      (dst + copySize count)).toNat = 1 := by
    rw [fusedCond_toNat dst count (i + 1) hfit (by omega), if_pos hi]
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedBodyPath
        (by simpa [fusedLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedLoop, State.fork] using hfork)
        (run_fusedBody s dst src take modulus count i returnDest rest hcap hrun)
        (by simpa [fusedLoop] using hrun)
        (by simpa [fusedLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedTestPath
        (by simpa [fusedTested, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedTested, State.fork] using hfork)
        (run_fusedNext s dst src take modulus count i returnDest rest hcap hcode
          hrun hcond)
        (by simpa [fusedTested] using hrun)
        (by simpa [fusedTested, State.fork] using hnp))

def gasSteps_fusedLoop (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : 0 < count)
    (hfit : dst.toNat + 32 * count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedLoop s dst src take modulus count 0 returnDest rest)
      (fusedSelEntry s dst src take modulus count returnDest rest) := by
  cases count with
  | zero => exact absurd hcount (by omega)
  | succ k =>
  have hcond : (UInt256.lt (UInt256.ofNat (32 * (k + 1)) + dst)
      (dst + copySize (k + 1))).toNat = 0 := by
    rw [fusedCond_toNat dst (k + 1) (k + 1) hfit (by omega), if_neg (by omega)]
  refine (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => fusedLoop s dst src take modulus (k + 1) i returnDest rest)
      k fun i hi =>
    gasSteps_fusedIteration s dst src take modulus (k + 1) i returnDest rest hcap
      (by omega) hfit hcode hfork hrun hnp).trans ?_
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedBodyPath
        (by simpa [fusedLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedLoop, State.fork] using hfork)
        (run_fusedBody s dst src take modulus (k + 1) k returnDest rest hcap hrun)
        (by simpa [fusedLoop] using hrun)
        (by simpa [fusedLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedTestPath
        (by simpa [fusedTested, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedTested, State.fork] using hfork)
        (run_fusedExit s dst src take modulus (k + 1) k returnDest rest hcap rfl
          hrun hcond)
        (by simpa [fusedTested] using hrun)
        (by simpa [fusedTested, State.fork] using hnp))

def gasSteps_addSelect (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedSelEntry s dst src take modulus count returnDest rest)
      (fusedFinEntry s dst src take modulus count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectTestPath
        (by simpa [fusedSelEntry, fusedLoop, Artifact.submissionArtifact]
          using hcode)
        (by simpa [fusedSelEntry, fusedLoop, State.fork] using hfork)
        (run_selectTest s dst src take modulus count returnDest rest hcap
          (by simpa [fusedSelEntry, fusedLoop] using hrun))
        (by simpa [fusedSelEntry, fusedLoop] using hrun)
        (by simpa [fusedSelEntry, fusedLoop, State.fork] using hnp)).trans
    (if hskip : (addSkip s.memory s.activeWords dst src modulus count).toNat = 0 then
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka selectJumpPath
            (by simpa [fusedSkipTested, Artifact.submissionArtifact] using hcode)
            (by simpa [fusedSkipTested, State.fork] using hfork)
            (run_selectFall s dst src take modulus count returnDest rest hcap
              hrun hskip)
            (by simpa [fusedSkipTested] using hrun)
            (by simpa [fusedSkipTested, State.fork] using hnp)).trans
        (Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka selectCopyPath
            (by simpa [fusedCopyEntry, fusedLoop, Artifact.submissionArtifact]
              using hcode)
            (by simpa [fusedCopyEntry, fusedLoop, State.fork] using hfork)
            (run_selectCopy s dst src take modulus count returnDest rest hcap
              hrun hskip)
            (by simpa [fusedCopyEntry, fusedLoop] using hrun)
            (by simpa [fusedCopyEntry, fusedLoop, State.fork] using hnp))
    else
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka selectJumpPath
          (by simpa [fusedSkipTested, Artifact.submissionArtifact] using hcode)
          (by simpa [fusedSkipTested, State.fork] using hfork)
          (run_selectSkip s dst src take modulus count returnDest rest hcap hcode
            hrun hskip)
          (by simpa [fusedSkipTested] using hrun)
          (by simpa [fusedSkipTested, State.fork] using hnp))

/-- The helper's execution certificate.  `hdstFit` is new relative to the
three-pass helper: the fused loop terminates by comparing its running pointer
with `dst + 32 * count`, so that sum must not wrap. -/
def gasSteps_addMaskedMod (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hdstFit : dst.toNat + 32 * count < 2 ^ 256 := by
      first
        | omega
        | (simp only [Challenge.EvmProof.Word.literal_eq_ofNat,
            Challenge.EvmProof.Word.word_toNat_ofNat]; omega)) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (addReturned s dst src take modulus count returnDest rest) :=
  (gasSteps_addEntry s dst src take modulus count returnDest rest hcap hcode
    hfork hrun hnp).trans
  (if hguard : (take * UInt256.ofNat count).toNat = 0 then
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammTestPath
          (by simpa [addTested, Artifact.submissionArtifact] using hcode)
          (by simpa [addTested, State.fork] using hfork)
          (run_addTestZero s dst src take modulus count returnDest rest hcap hrun
            hguard)
          (by simpa [addTested] using hrun)
          (by simpa [addTested, State.fork] using hnp)).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammZeroPath
          (by simpa [addZeroEntry, Artifact.submissionArtifact] using hcode)
          (by simpa [addZeroEntry, State.fork] using hfork)
          (run_addZero s dst src take modulus count returnDest rest hcap hcode
            hvalid hrun hguard)
          (by simpa [addZeroEntry] using hrun)
          (by simpa [addZeroEntry, State.fork] using hnp))
  else
    have hcountPos : 0 < count := by
      rcases Nat.eq_zero_or_pos count with hzero | hpos
      · exact absurd (by
          subst hzero
          rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat]
          simp) hguard
      · exact hpos
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammTestPath
          (by simpa [addTested, Artifact.submissionArtifact] using hcode)
          (by simpa [addTested, State.fork] using hfork)
          (run_addTestGo s dst src take modulus count returnDest rest hcap hcode
            hrun hguard)
          (by simpa [addTested] using hrun)
          (by simpa [addTested, State.fork] using hnp)).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammGoPath
          (by simpa [addGoEntry, Artifact.submissionArtifact] using hcode)
          (by simpa [addGoEntry, State.fork] using hfork)
          (run_addGo s dst src take modulus count returnDest rest hcap hrun)
          (by simpa [addGoEntry] using hrun)
          (by simpa [addGoEntry, State.fork] using hnp)).trans
    ((gasSteps_fusedLoop s dst src take modulus count returnDest rest hcap
        hcountPos hdstFit hcode hfork hrun hnp).trans
    ((gasSteps_addSelect s dst src take modulus count returnDest rest hcap hcode
        hfork hrun hnp).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka finishPath
          (by simpa [fusedFinEntry, Artifact.submissionArtifact] using hcode)
          (by simpa [fusedFinEntry, State.fork] using hfork)
          (run_finish s dst src take modulus count returnDest rest hcap hcode
            hvalid hrun hguard)
          (by simpa [fusedFinEntry] using hrun)
          (by simpa [fusedFinEntry, State.fork] using hnp))))))

end Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
