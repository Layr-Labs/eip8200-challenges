import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpersPC
import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.EvmProof.Meter
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
   opAt 19 (.Dup ⟨1, by decide⟩), opAt 20 .LT, opAt 21 .ISZERO,
   pushAt 22 2 48, opAt 23 .JUMPI]

def clearBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 24 0 0, opAt 25 (.Dup ⟨1, by decide⟩), pushAt 26 1 5,
   opAt 27 .SHL, opAt 28 (.Dup ⟨3, by decide⟩), opAt 29 .ADD,
   opAt 30 .MSTORE, pushAt 31 1 1, opAt 32 .ADD, pushAt 33 2 21,
   opAt 34 .JUMP]

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
      ([19,20,21,22,23,24,25,26,29,30,31,32,34,35,36,37,38,40,41,44,45,
       46,47,48,49,50,51,52])[i - 15]! := by
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
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 26 + UInt256.ofNat 3 = UInt256.ofNat 29 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [clearGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    clearLoop, clearBodyEntry, clearPCs, hc4, hc5, hc6, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    himod, hnmod, hlt, hltLiteral, honeIsZero, hpc]

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
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
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
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hnmod, hzeroFalse, hfortyEight, hfortyEightNat, hjump, jump48, hpc]

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

def copySetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 46 .JUMPDEST, pushAt 47 0 0]

def copyGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 48 .JUMPDEST, opAt 49 (.Dup ⟨3, by decide⟩),
   opAt 50 (.Dup ⟨1, by decide⟩), opAt 51 .LT, opAt 52 .ISZERO,
   pushAt 53 2 93, opAt 54 .JUMPI]

def copyBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 55 (.Dup ⟨0, by decide⟩), pushAt 56 1 5, opAt 57 .SHL,
   opAt 58 (.Dup ⟨3, by decide⟩), opAt 59 .ADD, opAt 60 .MLOAD,
   opAt 61 (.Dup ⟨1, by decide⟩), pushAt 62 1 5, opAt 63 .SHL,
   opAt 64 (.Dup ⟨3, by decide⟩), opAt 65 .ADD, opAt 66 .MSTORE,
   pushAt 67 1 1, opAt 68 .ADD, pushAt 69 2 60, opAt 70 .JUMP]

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
      ([58,59,60,61,62,63,64,65,68,69,70,72,73,74,75,76,77,79,80,81,82,
       83,85,86,89,90,91,92,93,94,95,96,97,98])[i - 46]! := by
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
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 65 + UInt256.ofNat 3 = UInt256.ofNat 68 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [copyGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyLoop, copyBodyEntry, copyPCs, hc5, hc6, hc7, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

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
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
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
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hninetyThree, hninetyThreeNat, hjump, jump93, hpc]

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

/-! ### Limb arithmetic shared by both passes -/

structure AddProgress where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256

theorem land_sub_zero_take_toNat (word : UInt256) {take : Nat}
    (htake : take ≤ 1) :
    (UInt256.land word (0 - UInt256.ofNat take)).toNat = take * word.toNat := by
  interval_cases take
  · simp only [UInt256.land, UInt256.toNat, Nat.zero_mul]
    change (word.val &&& ((0 : UInt256).val - (UInt256.ofNat 0).val)).val = 0
    rw [Fin.and_val, Fin.val_sub]
    have hzeroVal : (0 : UInt256).val.val = 0 := by decide
    rw [hzeroVal]
    norm_num [UInt256.ofNat, UInt256.size]
  · simp only [UInt256.land, UInt256.toNat, Nat.one_mul]
    change (word.val &&& ((0 : UInt256).val - (UInt256.ofNat 1).val)).val =
      word.val
    rw [Fin.and_val, Fin.val_sub]
    change word.toNat &&& (2 ^ 256 - 1) = word.toNat
    exact Nat.and_two_pow_sub_one_eq_mod word.toNat 256 |>.trans
      (Nat.mod_eq_of_lt word.val.isLt)

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

def addProgress (memory : ByteArray) (activeWords dst src mask : UInt256) :
    Nat → AddProgress
  | 0 => ⟨memory, activeWords, 0⟩
  | i + 1 =>
      let before := addProgress memory activeWords dst src mask i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let dstAt := dst + off
      let srcAt := src + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let y := UInt256.land
        (MachineState.readWord before.memory srcAt.toNat) mask
      let sum := x + y
      let z := sum + before.carry
      let carry := UInt256.lor (UInt256.lt sum x) (UInt256.lt z sum)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let loadedSrc := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat srcAt.toNat 32)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedSrc.toNat dstAt.toNat 32)
      ⟨MachineState.writeBytes before.memory
          (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat,
        stored, carry⟩

theorem addOffset_toNat (ptr i : Nat) (hfit : ptr + 32 * i < 2 ^ 256) :
    (UInt256.ofNat ptr +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat =
        ptr + 32 * i := by
  rw [Challenge.EvmProof.Word.word_add_comm]
  exact clearOffset_toNat ptr i hfit

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

/-- Earlier destination writes cannot affect a destination limb that has not
yet been processed. -/
theorem readWord_addProgress_future_dest (memory : ByteArray)
    (activeWords mask : UInt256) (dst src iter j : Nat)
    (hiter : iter ≤ j) (hfit : dst + 32 * (j + 1) < 2 ^ 256) :
    MachineState.readWord
        (addProgress memory activeWords (UInt256.ofNat dst)
          (UInt256.ofNat src) mask iter).memory
        (dst + 32 * j) =
      MachineState.readWord memory (dst + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [addProgress, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · right
        have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        omega

/-- Under the aliasing patterns used by the submission (identical regions or
disjoint regions), earlier destination writes also leave the next source limb
unchanged. -/
theorem readWord_addProgress_source (memory : ByteArray)
    (activeWords mask : UInt256) (dst src count iter j : Nat)
    (hiter : iter ≤ j) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst) :
    MachineState.readWord
        (addProgress memory activeWords (UInt256.ofNat dst)
          (UInt256.ofNat src) mask iter).memory
        (src + 32 * j) =
      MachineState.readWord memory (src + 32 * j) := by
  rcases halias with rfl | hdisjoint
  · exact readWord_addProgress_future_dest memory activeWords mask dst dst
      iter j hiter (by omega)
  · induction iter with
    | zero => rfl
    | succ iter ih =>
        rw [addProgress, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · have hsize (value : Nat) :
              (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, addOffset_toNat dst iter (by omega)]
          rcases hdisjoint with hbefore | hafter
          · right; omega
          · left; omega

theorem readWord_addProgress_disjoint_region (memory : ByteArray)
    (activeWords src mask : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst) :
    MachineState.readWord
        (addProgress memory activeWords (UInt256.ofNat dst) src mask iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [addProgress, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem memoryLimbs_addProgress_disjoint_region (memory : ByteArray)
    (activeWords src mask : UInt256) (dst ptr count iter : Nat)
    (hiter : iter ≤ count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst) :
    Limbs.memoryLimbs
        (addProgress memory activeWords (UInt256.ofNat dst) src mask iter).memory
        ptr count = Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [readWord_addProgress_disjoint_region memory activeWords src mask dst ptr
    count iter j hiter (by simpa using hj) hdstfit hdisjoint]

theorem represents_addProgress_disjoint_region (memory : ByteArray)
    (activeWords src mask : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (addProgress memory activeWords (UInt256.ofNat dst) src mask iter).memory
      ptr count value := by
  exact ⟨hrep.1, (memoryLimbs_addProgress_disjoint_region memory activeWords
    src mask dst ptr count iter hiter hdstfit hdisjoint).trans hrep.2⟩

structure AddNatProgress where
  digits : List Nat
  carry : Nat

/-- Mathematical prefix computation driven by the original memory limbs. -/
def addNatProgress (memory : ByteArray) (dst src take : Nat) :
    Nat → AddNatProgress
  | 0 => ⟨[], 0⟩
  | i + 1 =>
      let before := addNatProgress memory dst src take i
      let x := (MachineState.readWord memory (dst + 32 * i)).toNat
      let y := (MachineState.readWord memory (src + 32 * i)).toNat
      let total := x + take * y + before.carry
      ⟨before.digits ++ [total % Limbs.radix], total / Limbs.radix⟩

theorem memoryLimbs_succ (memory : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs memory ptr (count + 1) =
      Limbs.memoryLimbs memory ptr count ++
        [(MachineState.readWord memory (ptr + 32 * count)).toNat] := by
  simp [Limbs.memoryLimbs, List.range_succ]

theorem addNatProgress_eq_addDigitLists (memory : ByteArray)
    (dst src take count : Nat) :
    let natural := addNatProgress memory dst src take count
    let result := Limbs.addDigitLists
      (Limbs.memoryLimbs memory dst count)
      ((Limbs.memoryLimbs memory src count).map (take * ·)) 0
    natural.digits = result.1 ∧ natural.carry = result.2 := by
  induction count with
  | zero => simp [addNatProgress, Limbs.memoryLimbs, Limbs.addDigitLists]
  | succ count ih =>
      rw [addNatProgress, memoryLimbs_succ, memoryLimbs_succ,
        List.map_append, List.map_singleton]
      rw [Limbs.addDigitLists_append_single (by
        simp [Limbs.memoryLimbs])]
      rcases ih with ⟨hdigits, hcarry⟩
      simp only
      rw [hdigits, hcarry]
      exact ⟨rfl, rfl⟩

theorem addProgress_matches_nat (memory : ByteArray) (activeWords : UInt256)
    (dst src count iter take : Nat) (hiter : iter ≤ count)
    (htake : take ≤ 1) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst) :
    let progress := addProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat src) (0 - UInt256.ofNat take) iter
    let natural := addNatProgress memory dst src take iter
    Limbs.memoryLimbs progress.memory dst iter = natural.digits ∧
      progress.carry.toNat = natural.carry ∧ natural.carry ≤ 1 := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [addProgress, addNatProgress, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hi : iter < count := by omega
      have hprefix := ih (by omega)
      let before := addProgress memory activeWords (UInt256.ofNat dst)
        (UInt256.ofNat src) (0 - UInt256.ofNat take) iter
      let naturalBefore := addNatProgress memory dst src take iter
      have hbeforeMemory :
          Limbs.memoryLimbs before.memory dst iter = naturalBefore.digits :=
        hprefix.1
      have hbeforeCarry : before.carry.toNat = naturalBefore.carry :=
        hprefix.2.1
      have hbeforeCarryLe : naturalBefore.carry ≤ 1 := hprefix.2.2
      let x := MachineState.readWord before.memory (dst + 32 * iter)
      let source := MachineState.readWord before.memory (src + 32 * iter)
      let y := UInt256.land source (0 - UInt256.ofNat take)
      have hx : x = MachineState.readWord memory (dst + 32 * iter) := by
        exact readWord_addProgress_future_dest memory activeWords
          (0 - UInt256.ofNat take) dst src iter iter (by omega) (by omega)
      have hsource : source =
          MachineState.readWord memory (src + 32 * iter) := by
        exact readWord_addProgress_source memory activeWords
          (0 - UInt256.ofNat take) dst src count iter iter (by omega) hi
          hdstfit hsrcfit halias
      have hy : y.toNat = take *
          (MachineState.readWord memory (src + 32 * iter)).toNat := by
        change (UInt256.land source (0 - UInt256.ofNat take)).toNat = _
        rw [land_sub_zero_take_toNat source htake, hsource]
      have hstep := addLimbStep_toNat x y before.carry (by
        rw [hbeforeCarry]
        exact hbeforeCarryLe)
      have hoff :
          (UInt256.ofNat dst + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = dst + 32 * iter :=
        addOffset_toNat dst iter (by omega)
      have hoffSource :
          (UInt256.ofNat src + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = src + 32 * iter :=
        addOffset_toNat src iter (by omega)
      dsimp only [addProgress, addNatProgress]
      rw [hoff, hoffSource, memoryLimbs_write_next]
      constructor
      · rw [hbeforeMemory]
        congr 2
        simpa [x, y, source, before, naturalBefore, hx, hy, hbeforeCarry]
          using hstep.1
      · constructor
        · simpa [x, y, source, before, naturalBefore, hx, hy, hbeforeCarry]
            using hstep.2
        · rw [Nat.div_le_iff_le_mul Limbs.radix_pos]
          rw [← hx, ← hy, ← hbeforeCarry]
          have hxLt : x.toNat < Limbs.radix := by
            change x.val.val < UInt256.size
            exact x.val.isLt
          have hyLt : y.toNat < Limbs.radix := by
            change y.val.val < UInt256.size
            exact y.val.isLt
          omega

theorem addProgress_value_carry (memory : ByteArray) (activeWords : UInt256)
    (dst src count take x y : Nat) (htake : take ≤ 1)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdst : Limbs.Represents memory dst count x)
    (hsrc : Limbs.Represents memory src count y) :
    let progress := addProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat src) (0 - UInt256.ofNat take) count
    Nat.ofDigits Limbs.radix
        (Limbs.memoryLimbs progress.memory dst count) +
          Limbs.radix ^ count * progress.carry.toNat = x + take * y ∧
      progress.carry.toNat ≤ 1 := by
  let progress := addProgress memory activeWords (UInt256.ofNat dst)
    (UInt256.ofNat src) (0 - UInt256.ofNat take) count
  let natural := addNatProgress memory dst src take count
  let result := Limbs.addDigitLists
    (Limbs.memoryLimbs memory dst count)
    ((Limbs.memoryLimbs memory src count).map (take * ·)) 0
  have hmatch := addProgress_matches_nat memory activeWords dst src count count
    take (by omega) htake hdstfit hsrcfit halias
  have hcanonical := addNatProgress_eq_addDigitLists memory dst src take count
  have hlength :
      (Limbs.memoryLimbs memory dst count).length =
        ((Limbs.memoryLimbs memory src count).map (take * ·)).length := by
    simp
  have hvalue := Limbs.addDigitLists_value (carry := 0) hlength
  rw [Limbs.ofDigits_map_mul, Nat.add_zero,
    Limbs.value_of_represents hdst, Limbs.value_of_represents hsrc] at hvalue
  dsimp only [progress, natural, result] at hmatch hcanonical ⊢
  rw [hmatch.1, hcanonical.1, hmatch.2.1, hcanonical.2]
  constructor
  · simpa using hvalue
  · simpa [← hcanonical.2] using hmatch.2.2

theorem addProgress_represents_wrapped (memory : ByteArray)
    (activeWords : UInt256) (dst src count take x y : Nat)
    (htake : take ≤ 1) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hsrcfit : src + 32 * count < 2 ^ 256)
    (halias : dst = src ∨ dst + 32 * count ≤ src ∨
      src + 32 * count ≤ dst)
    (hdst : Limbs.Represents memory dst count x)
    (hsrc : Limbs.Represents memory src count y) :
    Limbs.Represents
      (addProgress memory activeWords (UInt256.ofNat dst)
        (UInt256.ofNat src) (0 - UInt256.ofNat take) count).memory
      dst count ((x + take * y) % Limbs.radix ^ count) := by
  have hmatch := addProgress_matches_nat memory activeWords dst src count count
    take (by omega) htake hdstfit hsrcfit halias
  have hcanonical := addNatProgress_eq_addDigitLists memory dst src take count
  have hmod := Limbs.addDigitLists_masked_value_mod
    (xs := Limbs.memoryLimbs memory dst count)
    (ys := Limbs.memoryLimbs memory src count) (take := take) (by simp)
  rw [Limbs.value_of_represents hdst, Limbs.value_of_represents hsrc] at hmod
  rw [Limbs.represents_iff_value (Nat.mod_lt _ (pow_pos Limbs.radix_pos _))]
  rw [hmatch.1, hcanonical.1]
  simpa using hmod

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

theorem useSub_eq_one_iff (carry borrow : UInt256)
    {total modulus bound wrapped : Nat}
    (hmodulus : modulus < bound) (hwrapped : wrapped = total % bound)
    (hcarryLe : carry.toNat ≤ 1) (hborrowLe : borrow.toNat ≤ 1)
    (hcarry : carry.toNat = 1 ↔ bound ≤ total)
    (hborrow : borrow.toNat = 0 ↔ modulus ≤ wrapped) :
    (UInt256.lor carry (UInt256.isZero borrow)).toNat = 1 ↔
      modulus ≤ total := by
  simp only [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_isZero]
  have hor :
      (carry.toNat ||| if borrow.toNat = 0 then 1 else 0) = 1 ↔
        carry.toNat = 1 ∨ borrow.toNat = 0 := by
    interval_cases carry.toNat <;> interval_cases borrow.toNat <;> norm_num
  rw [hor, hcarry, hborrow, hwrapped]
  exact Limbs.useSub_iff hmodulus

theorem useSub_toNat_le_one (carry borrow : UInt256)
    (hcarry : carry.toNat ≤ 1) (hborrow : borrow.toNat ≤ 1) :
    (UInt256.lor carry (UInt256.isZero borrow)).toNat ≤ 1 := by
  simp only [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_isZero]
  interval_cases carry.toNat <;> interval_cases borrow.toNat <;> norm_num
/-! ### Word-level algebra for the fused helper

The replacement carries a *pointer* `p` through the loop rather than an index,
and derives the source and modulus addresses from it by adding the constant
displacements `ds = src - dst` and `dm = modulus - dst`.  These lemmas move
between that machine form and the indexed form `ptr + 32 * i` the limb layer
already speaks. -/

/-- Byte displacement of limb `i`, in the exact form both `addProgress` and the
replacement build it.  Spelled out rather than abbreviated so that the two
memory models share syntactically identical subterms. -/
abbrev ammOffset (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)

/-- The loop pointer at iteration `i`.  The replacement threads this word
through the loop instead of the index the reference used. -/
def ammPtr (dst : UInt256) (i : Nat) : UInt256 := dst + ammOffset i

theorem ammPtr_eq (dst : UInt256) (i : Nat) :
    ammPtr dst i =
      dst + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) := rfl

theorem word_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem word_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_lor, Nat.or_comm]

theorem word_toNat_gt (a b : UInt256) :
    (UInt256.gt a b).toNat = if b.toNat < a.toNat then 1 else 0 := by
  simp only [UInt256.gt]
  split <;> norm_num [UInt256.ofNat, UInt256.toNat, UInt256.size]

theorem word_toNat_eq (a b : UInt256) :
    (UInt256.eq a b).toNat = if a.toNat = b.toNat then 1 else 0 := by
  simp only [UInt256.eq]
  split <;> norm_num [UInt256.ofNat, UInt256.toNat, UInt256.size]

/-- `(dst + off) + (src - dst) = src + off`: the machine's pointer-plus-
displacement addressing agrees with indexed addressing, with no side condition
because every step is exact modulo `2 ^ 256`. -/
theorem word_add_sub_add (dst src off : UInt256) :
    dst + off + (src - dst) = src + off := by
  apply Challenge.EvmProof.Word.word_ext
  have hd : dst.toNat < 2 ^ 256 := dst.val.isLt
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add,
    ← Nat.add_mod]
  have hrearrange :
      dst.toNat + off.toNat + (2 ^ 256 + src.toNat - dst.toNat) =
        2 ^ 256 + (src.toNat + off.toNat) := by omega
  rw [hrearrange, Nat.add_mod_left]

theorem ammSrcAt (dst src : UInt256) (i : Nat) :
    ammPtr dst i + (src - dst) = src + ammOffset i :=
  word_add_sub_add dst src (ammOffset i)

theorem ammOffset_toNat (i : Nat) (hi : 32 * i < 2 ^ 256) :
    (ammOffset i).toNat = 32 * i := by
  have hshift := Challenge.EvmProof.Word.shiftLeft_ofNat
    (value := i) (shift := 5) (by omega) (by norm_num) (by omega)
  rw [ammOffset, hshift, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem ammPtr_toNat (dst i : Nat) (hfit : dst + 32 * i < 2 ^ 256) :
    (ammPtr (UInt256.ofNat dst) i).toNat = dst + 32 * i :=
  addOffset_toNat dst i hfit

theorem ammPtr_zero (dst : UInt256) : ammPtr dst 0 = dst := by
  apply Challenge.EvmProof.Word.word_ext
  have hd : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hoff : (ammOffset 0).toNat = 0 := ammOffset_toNat 0 (by norm_num)
  rw [ammPtr, Challenge.EvmProof.Word.word_toNat_add, hoff, Nat.add_zero,
    Nat.mod_eq_of_lt hd]

/-- The loop increment `p := 32 + p`. -/
theorem ammPtr_succ (dst : UInt256) (i : Nat) (hi : 32 * (i + 1) < 2 ^ 256) :
    (32 : UInt256) + ammPtr dst i = ammPtr dst (i + 1) := by
  apply Challenge.EvmProof.Word.word_ext
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hoi : (ammOffset i).toNat = 32 * i := ammOffset_toNat i (by omega)
  have hoi1 : (ammOffset (i + 1)).toNat = 32 * (i + 1) :=
    ammOffset_toNat (i + 1) (by omega)
  rw [ammPtr, ammPtr, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add, h32, hoi, hoi1,
    Nat.add_mod_mod]
  congr 1
  omega

/-- The loop bound `end = dst + 32 * n`, in the form `DUP; PUSH1 5; SHL; ADD`
builds it. -/
def ammEnd (dst : UInt256) (count : Nat) : UInt256 :=
  dst + UInt256.shiftLeft (UInt256.ofNat count) (UInt256.ofNat 5)

/-- **The number of iterations the pointer loop actually performs.**

The reference counted with an index and compared `i < n`, so `n < 2 ^ 256` was
enough.  The replacement compares *addresses* -- `p < dst + 32 * n` -- which is
a different predicate as soon as that sum wraps, and the gas layer's callers
carry only `count < 2 ^ 256`, so a no-wrap hypothesis cannot be supplied there.
Rather than change any signature, the model is made **exact**: `ammCount` is the
iteration count for every `dst` and `count`, wrapped or not, and
`ammCount_eq_count` retires it in the correctness layer, which already carries
`hdstFit`.  (`end - dst` truncates to `0` in `Nat` exactly when the loop is
skipped, which is why no `if` is needed.) -/
def ammCount (dst : UInt256) (count : Nat) : Nat :=
  ((ammEnd dst count).toNat - dst.toNat) / 32

theorem ammOffset_toNat_mod (i : Nat) : (ammOffset i).toNat = (32 * i) % 2 ^ 256 := by
  have hshift : (UInt256.ofNat 5).toNat = 5 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rw [ammOffset, UInt256.shiftLeft, if_neg (by rw [hshift]; omega), hshift,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftLeft_eq, hsize,
    Nat.mod_mod_of_dvd _ dvd_rfl]
  conv_rhs => rw [Nat.mul_mod]
  norm_num
  rw [Nat.mul_comm]

private theorem dvd32_mod (i : Nat) : 32 ∣ (32 * i) % 2 ^ 256 := by
  have h : (2 : Nat) ^ 256 = 32 * 2 ^ 251 := by
    rw [show (32 : Nat) = 2 ^ 5 by norm_num, ← pow_add]
  rw [h, Nat.mul_mod_mul_left]
  exact Nat.dvd_mul_right 32 (i % 2 ^ 251)

theorem ammEnd_toNat_mod (dst : UInt256) (count : Nat) :
    (ammEnd dst count).toNat = (dst.toNat + (32 * count) % 2 ^ 256) % 2 ^ 256 := by
  rw [ammEnd, Challenge.EvmProof.Word.word_toNat_add]
  exact congrArg (fun z => (dst.toNat + z) % 2 ^ 256) (ammOffset_toNat_mod count)

theorem ammEnd_sub_dvd (dst : UInt256) (count : Nat) :
    32 ∣ ((ammEnd dst count).toNat - dst.toNat) := by
  have hd : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hq : (32 * count) % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by positivity)
  have hdvdq : 32 ∣ (32 * count) % 2 ^ 256 := dvd32_mod count
  rw [ammEnd_toNat_mod]
  by_cases h : dst.toNat + (32 * count) % 2 ^ 256 < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    simpa using hdvdq
  · have hw : (dst.toNat + (32 * count) % 2 ^ 256) % 2 ^ 256 =
        dst.toNat + (32 * count) % 2 ^ 256 - 2 ^ 256 := by
      rw [show dst.toNat + (32 * count) % 2 ^ 256 =
        (dst.toNat + (32 * count) % 2 ^ 256 - 2 ^ 256) + 2 ^ 256 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hw, show dst.toNat + (32 * count) % 2 ^ 256 - 2 ^ 256 - dst.toNat = 0 by omega]
    exact Nat.dvd_zero 32

theorem ammCount_mul (dst : UInt256) (count : Nat) :
    32 * ammCount dst count = (ammEnd dst count).toNat - dst.toNat := by
  obtain ⟨k, hk⟩ := ammEnd_sub_dvd dst count
  rw [ammCount, hk, Nat.mul_div_cancel_left k (by norm_num)]

/-- Every pointer the loop actually reaches is inside the address space. -/
theorem ammCount_fits (dst : UInt256) (count i : Nat)
    (hi : i ≤ ammCount dst count) : dst.toNat + 32 * i < 2 ^ 256 := by
  have hd : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hend : (ammEnd dst count).toNat < 2 ^ 256 := (ammEnd dst count).val.isLt
  have h := ammCount_mul dst count
  have hmul : 32 * i ≤ 32 * ammCount dst count := Nat.mul_le_mul_left _ hi
  omega

theorem ammPtr_toNat' (dst : UInt256) (i : Nat)
    (hfit : dst.toNat + 32 * i < 2 ^ 256) :
    (ammPtr dst i).toNat = dst.toNat + 32 * i := by
  rw [ammPtr, Challenge.EvmProof.Word.word_toNat_add, ammOffset_toNat_mod,
    Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (show 32 * i < 2 ^ 256 by omega)]

/-- **The address guard is the counter guard**, for every `dst` and `count`. -/
theorem ammPtr_lt_end_iff (dst : UInt256) (count i : Nat)
    (hi : i ≤ ammCount dst count) :
    ((ammPtr dst i).toNat < (ammEnd dst count).toNat ↔ i < ammCount dst count) := by
  have hd : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hp := ammPtr_toNat' dst i (ammCount_fits dst count i hi)
  have h := ammCount_mul dst count
  rw [hp]
  omega

/-- Under the no-wrap hypothesis the correctness layer already carries, the
exact iteration count is the caller's `count`. -/
theorem ammCount_eq_count (dst : UInt256) (count : Nat)
    (hfit : dst.toNat + 32 * count < 2 ^ 256) : ammCount dst count = count := by
  have hq : (32 * count) % 2 ^ 256 = 32 * count := Nat.mod_eq_of_lt (by omega)
  have hend : (ammEnd dst count).toNat = dst.toNat + 32 * count := by
    rw [ammEnd_toNat_mod, hq, Nat.mod_eq_of_lt hfit]
  rw [ammCount, hend]
  omega
/-! ### Pass A: the fused add-and-compare loop

The reference made three passes over the limbs: add with carry, subtract with
borrow into a `0x1400` scratch buffer, then a branchless limbwise blend.  The
replacement fuses passes one and two -- the borrow of `sum - modulus` is
produced by the *same* iteration that produces the sum limb, from the value
still in a register -- and then **branches** on `useSub` instead of blending.

Fusing is sound because pass A reads `modulus[i]` after having written
`dst[0..i-1]`.  That read is unaffected exactly when the modulus region is
disjoint from the destination region, which is `hdstModulus` below and holds at
every call site (`modulus = 0x0000`, `dst ∈ {0x0400, 0x0800, 0x1000}`,
`count ≤ 32`).  Reading `src` is *not* subject to the same condition, because
pass A reads `src[i]` in exactly the order the reference's first pass did. -/

private theorem or_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

private theorem or_eq_one_iff {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a ||| b) = 1 ↔ (a = 1 ∨ b = 1) := by
  interval_cases a <;> interval_cases b <;> decide

private theorem and_eq_one_iff {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a &&& b) = 1 ↔ (a = 1 ∧ b = 1) := by
  interval_cases a <;> interval_cases b <;> decide

private theorem and_le_one {a b : Nat} (hb : b ≤ 1) : a &&& b ≤ 1 :=
  le_trans (Nat.and_le_right) hb

private theorem eq_of_le_one_iff {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a = 1 ↔ b = 1) : a = b := by omega

/-- The word `or(gt(x, z), and(carry, eq(z, x)))` the replacement evaluates is
the carry out of `x + y + carry`.  (The reference evaluated
`or(lt(sum, x), lt(z, sum))`; both compute `(x + y + carry) / 2 ^ 256`.) -/
theorem carryOut_word (B x y cin : Nat) (hB : 0 < B)
    (hx : x < B) (hy : y < B) (hcin : cin ≤ 1) :
    ((x + y + cin) / B = 1 ↔
      ((x + y + cin) % B < x ∨ ((x + y + cin) % B = x ∧ cin = 1))) ∧
    (x + y + cin) / B ≤ 1 := by
  rcases Nat.lt_or_ge (x + y + cin) B with h | h
  · have hdiv : (x + y + cin) / B = 0 := Nat.div_eq_of_lt h
    have hmod : (x + y + cin) % B = x + y + cin := Nat.mod_eq_of_lt h
    refine ⟨?_, by omega⟩
    rw [hdiv, hmod]
    constructor
    · intro hc; exact absurd hc (by omega)
    · intro hc; rcases hc with hc | ⟨hc1, hc2⟩ <;> omega
  · have hlt2 : x + y + cin - B < B := by omega
    have hsum : x + y + cin = (x + y + cin - B) + B := by omega
    have hdiv : (x + y + cin) / B = 1 := by
      rw [hsum, Nat.add_div_right _ hB, Nat.div_eq_of_lt hlt2]
    have hmod : (x + y + cin) % B = x + y + cin - B := by
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      omega
    refine ⟨?_, by omega⟩
    rw [hdiv, hmod]
    constructor
    · intro _
      by_cases hc : x + y + cin - B < x
      · exact Or.inl hc
      · exact Or.inr ⟨by omega, by omega⟩
    · intro _; rfl

theorem fuseSum_toNat (x y c : UInt256) :
    (c + (x + y)).toNat = (x.toNat + y.toNat + c.toNat) % Limbs.radix := by
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add, Nat.add_mod_mod, Limbs.radix]
  congr 1
  omega

theorem fuseCarry_toNat (x y c : UInt256) (hc : c.toNat ≤ 1) :
    (UInt256.lor (UInt256.gt x (c + (x + y)))
        (UInt256.land c (UInt256.eq (c + (x + y)) x))).toNat =
      (x.toNat + y.toNat + c.toNat) / Limbs.radix := by
  have hx : x.toNat < Limbs.radix := x.val.isLt
  have hy : y.toNat < Limbs.radix := y.val.isLt
  have hz : (c + (x + y)).toNat = (x.toNat + y.toNat + c.toNat) % Limbs.radix :=
    fuseSum_toNat x y c
  obtain ⟨hiff, hle⟩ :=
    carryOut_word Limbs.radix x.toNat y.toNat c.toNat Limbs.radix_pos hx hy hc
  have hgt : (UInt256.gt x (c + (x + y))).toNat ≤ 1 := by
    rw [word_toNat_gt]; split <;> omega
  have heq : (UInt256.eq (c + (x + y)) x).toNat ≤ 1 := by
    rw [word_toNat_eq]; split <;> omega
  have hand : (UInt256.land c (UInt256.eq (c + (x + y)) x)).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_land]; exact and_le_one heq
  have hlorLe :
      (UInt256.lor (UInt256.gt x (c + (x + y)))
        (UInt256.land c (UInt256.eq (c + (x + y)) x))).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lor]; exact or_le_one hgt hand
  have hlorIff :
      (UInt256.lor (UInt256.gt x (c + (x + y)))
        (UInt256.land c (UInt256.eq (c + (x + y)) x))).toNat = 1 ↔
      ((x.toNat + y.toNat + c.toNat) % Limbs.radix < x.toNat ∨
        ((x.toNat + y.toNat + c.toNat) % Limbs.radix = x.toNat ∧
          c.toNat = 1)) := by
    rw [Challenge.EvmProof.Word.word_toNat_lor, or_eq_one_iff hgt hand,
      Challenge.EvmProof.Word.word_toNat_land, and_eq_one_iff hc heq,
      word_toNat_gt, word_toNat_eq, hz]
    constructor
    · rintro (hgv | ⟨hc1, hev⟩)
      · exact Or.inl (by by_contra hne; rw [if_neg hne] at hgv; omega)
      · exact Or.inr ⟨by by_contra hne; rw [if_neg hne] at hev; omega, hc1⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by rw [if_pos h])
      · exact Or.inr ⟨h2, by rw [if_pos h1]⟩
  exact eq_of_le_one_iff hlorLe hle (hlorIff.trans hiff.symm)

/-- Word form of the borrow step: `or(and(borrow, eq(z, m)), lt(z, m))` is
`z < m + borrow`. -/
theorem borrowOut_word (z m b : UInt256) (hb : b.toNat ≤ 1) :
    (UInt256.lor (UInt256.land b (UInt256.eq z m)) (UInt256.lt z m)).toNat ≤ 1 ∧
    ((UInt256.lor (UInt256.land b (UInt256.eq z m)) (UInt256.lt z m)).toNat = 1 ↔
      z.toNat < m.toNat + b.toNat) := by
  have heq : (UInt256.eq z m).toNat ≤ 1 := by
    rw [word_toNat_eq]; split <;> omega
  have hlt : (UInt256.lt z m).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]; split <;> omega
  have hand : (UInt256.land b (UInt256.eq z m)).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_land]; exact and_le_one heq
  refine ⟨by rw [Challenge.EvmProof.Word.word_toNat_lor]; exact or_le_one hand hlt,
    ?_⟩
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_eq_one_iff hand hlt,
    Challenge.EvmProof.Word.word_toNat_land, and_eq_one_iff hb heq,
    word_toNat_eq, Challenge.EvmProof.Word.word_toNat_lt]
  constructor
  · rintro (⟨hb1, hev⟩ | hlv)
    · have hzm : z.toNat = m.toNat := by
        by_contra hne; rw [if_neg hne] at hev; omega
      omega
    · have hzm : z.toNat < m.toNat := by
        by_contra hne; rw [if_neg hne] at hlv; omega
      omega
  · intro h
    by_cases hzm : z.toNat < m.toNat
    · exact Or.inr (by rw [if_pos hzm])
    · exact Or.inl ⟨by omega, by rw [if_pos (by omega : z.toNat = m.toNat)]⟩

structure FuseProgress where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256
  borrow : UInt256

/-- Pass A.  One iteration loads `dst[i]`, `src[i]` and `modulus[i]`, stores the
sum limb back to `dst[i]`, and threads both a carry and a borrow. -/
def fuseProgress (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) : Nat → FuseProgress
  | 0 => ⟨memory, activeWords, 0, 0⟩
  | i + 1 =>
      let before := fuseProgress memory activeWords dst src modulus mask i
      let off := ammOffset i
      let dstAt := dst + off
      let srcAt := src + off
      let modulusAt := modulus + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let y := UInt256.land mask
        (MachineState.readWord before.memory srcAt.toNat)
      let z := before.carry + (x + y)
      let carry := UInt256.lor (UInt256.gt x z)
        (UInt256.land before.carry (UInt256.eq z x))
      let m := MachineState.readWord before.memory modulusAt.toNat
      let borrow := UInt256.lor (UInt256.land before.borrow (UInt256.eq z m))
        (UInt256.lt z m)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let loadedSrc := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat srcAt.toNat 32)
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedSrc.toNat modulusAt.toNat 32)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat dstAt.toNat 32)
      ⟨MachineState.writeBytes before.memory
          (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat,
        stored, carry, borrow⟩

theorem fuseProgress_carry_le_one (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) (i : Nat) :
    (fuseProgress memory activeWords dst src modulus mask i).carry.toNat ≤ 1 := by
  cases i with
  | zero =>
      have h0 : (fuseProgress memory activeWords dst src modulus mask 0).carry
          = 0 := rfl
      rw [h0]; decide
  | succ i =>
      rw [fuseProgress]
      dsimp only
      rw [Challenge.EvmProof.Word.word_toNat_lor]
      refine or_le_one ?_ ?_
      · rw [word_toNat_gt]; split <;> omega
      · rw [Challenge.EvmProof.Word.word_toNat_land]
        exact and_le_one (by rw [word_toNat_eq]; split <;> omega)

theorem fuseProgress_borrow_le_one (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) (i : Nat) :
    (fuseProgress memory activeWords dst src modulus mask i).borrow.toNat ≤ 1 := by
  cases i with
  | zero =>
      have h0 : (fuseProgress memory activeWords dst src modulus mask 0).borrow
          = 0 := rfl
      rw [h0]; decide
  | succ i =>
      rw [fuseProgress]
      dsimp only
      rw [Challenge.EvmProof.Word.word_toNat_lor]
      refine or_le_one ?_ ?_
      · rw [Challenge.EvmProof.Word.word_toNat_land]
        exact and_le_one (by rw [word_toNat_eq]; split <;> omega)
      · rw [Challenge.EvmProof.Word.word_toNat_lt]; split <;> omega

private theorem fuseStep_z (x s mask c : UInt256) :
    c + (x + UInt256.land mask s) = x + UInt256.land s mask + c := by
  rw [word_land_comm mask s,
    Challenge.EvmProof.Word.word_add_comm c (x + UInt256.land s mask)]

private theorem fuseStep_carry (x s mask c : UInt256) (hc : c.toNat ≤ 1) :
    UInt256.lor (UInt256.gt x (c + (x + UInt256.land mask s)))
        (UInt256.land c (UInt256.eq (c + (x + UInt256.land mask s)) x)) =
      UInt256.lor (UInt256.lt (x + UInt256.land s mask) x)
        (UInt256.lt (x + UInt256.land s mask + c) (x + UInt256.land s mask)) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [fuseCarry_toNat x (UInt256.land mask s) c hc,
    (addLimbStep_toNat x (UInt256.land s mask) c hc).2, word_land_comm mask s]

/-- **The fusion is memory-equivalent to the reference's first pass.**  The
extra modulus load changes only `activeWords`, and the differently-spelled
carry computes the same word, so every lemma already proved about
`addProgress` transfers verbatim. -/
theorem fuseProgress_agrees (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) (i : Nat) :
    (fuseProgress memory activeWords dst src modulus mask i).memory =
        (addProgress memory activeWords dst src mask i).memory ∧
      (fuseProgress memory activeWords dst src modulus mask i).carry =
        (addProgress memory activeWords dst src mask i).carry := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
      obtain ⟨hmem, hcarry⟩ := ih
      have hcle :
          (fuseProgress memory activeWords dst src modulus mask i).carry.toNat ≤ 1 :=
        fuseProgress_carry_le_one memory activeWords dst src modulus mask i
      have hcleAdd : (addProgress memory activeWords dst src mask i).carry.toNat ≤ 1 := by
        rw [← hcarry]; exact hcle
      constructor
      · rw [fuseProgress, addProgress]
        dsimp only
        rw [hmem, hcarry, fuseStep_z]
      · rw [fuseProgress, addProgress]
        dsimp only
        rw [hmem, hcarry]
        exact fuseStep_carry _ _ mask _ hcleAdd

theorem fuseProgress_memory (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) (i : Nat) :
    (fuseProgress memory activeWords dst src modulus mask i).memory =
      (addProgress memory activeWords dst src mask i).memory :=
  (fuseProgress_agrees memory activeWords dst src modulus mask i).1

theorem fuseProgress_carry (memory : ByteArray)
    (activeWords dst src modulus mask : UInt256) (i : Nat) :
    (fuseProgress memory activeWords dst src modulus mask i).carry =
      (addProgress memory activeWords dst src mask i).carry :=
  (fuseProgress_agrees memory activeWords dst src modulus mask i).2

theorem readWord_fuseProgress_disjoint_region (memory : ByteArray)
    (activeWords src modulus mask : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst) :
    MachineState.readWord
        (fuseProgress memory activeWords (UInt256.ofNat dst) src modulus mask
          iter).memory (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  rw [fuseProgress_memory]
  exact readWord_addProgress_disjoint_region memory activeWords src mask dst ptr
    count iter j hiter hj hdstfit hdisjoint

theorem represents_fuseProgress_disjoint_region (memory : ByteArray)
    (activeWords src modulus mask : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (fuseProgress memory activeWords (UInt256.ofNat dst) src modulus mask
        iter).memory ptr count value := by
  rw [fuseProgress_memory]
  exact represents_addProgress_disjoint_region memory activeWords src mask dst
    ptr count iter value hiter hdstfit hdisjoint hrep

/-- The lexicographic step of the borrow chain, in the *forward* (low-to-high)
direction the memory model builds limbs in: appending `z` and `m` above
prefixes `Z, M < B` flips the comparison exactly as the word-level borrow
formula does. -/
private theorem lex_high (B Z M z m b : Nat) (hZ : Z < B) (hM : M < B)
    (hb : b ≤ 1) (hbiff : b = 1 ↔ Z < M) :
    (z < m + b ↔ Z + B * z < M + B * m) := by
  rcases Nat.lt_trichotomy z m with h | h | h
  · have hstep : B * z + B ≤ B * m := by
      have hmul : B * (z + 1) ≤ B * m := Nat.mul_le_mul (Nat.le_refl B) h
      simpa [Nat.mul_add] using hmul
    exact ⟨fun _ => by omega, fun _ => by omega⟩
  · subst h
    constructor
    · intro hc
      have hb1 : b = 1 := by omega
      have := hbiff.mp hb1
      omega
    · intro hc
      have : Z < M := by omega
      have := hbiff.mpr this
      omega
  · have hstep : B * m + B ≤ B * z := by
      have hmul : B * (m + 1) ≤ B * z := Nat.mul_le_mul (Nat.le_refl B) h
      simpa [Nat.mul_add] using hmul
    exact ⟨fun hc => by omega, fun hc => by omega⟩

/-- **The fused borrow decides the comparison.**  After `iter` iterations the
borrow is `1` exactly when the sum limbs written so far are strictly below the
corresponding modulus limbs -- the fact the reference obtained from a separate
subtraction pass over the freshly written words. -/
theorem fuseProgress_borrow_iff (memory : ByteArray)
    (activeWords src mask : UInt256) (dst modulus count iter : Nat)
    (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ modulus ∨ modulus + 32 * count ≤ dst) :
    ((fuseProgress memory activeWords (UInt256.ofNat dst) src
        (UInt256.ofNat modulus) mask iter).borrow.toNat = 1 ↔
      Nat.ofDigits Limbs.radix
          (Limbs.memoryLimbs
            (fuseProgress memory activeWords (UInt256.ofNat dst) src
              (UInt256.ofNat modulus) mask iter).memory dst iter) <
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory modulus iter)) := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [fuseProgress, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hlt : iter < count := by omega
      have hprev := ih (by omega)
      have hoffDst :
          ((UInt256.ofNat dst) + ammOffset iter).toNat = dst + 32 * iter :=
        addOffset_toNat dst iter (by omega)
      have hoffMod :
          ((UInt256.ofNat modulus) + ammOffset iter).toNat = modulus + 32 * iter :=
        addOffset_toNat modulus iter (by omega)
      have hm :
          MachineState.readWord
              (fuseProgress memory activeWords (UInt256.ofNat dst) src
                (UInt256.ofNat modulus) mask iter).memory (modulus + 32 * iter) =
            MachineState.readWord memory (modulus + 32 * iter) :=
        readWord_fuseProgress_disjoint_region memory activeWords src
          (UInt256.ofNat modulus) mask dst modulus count iter iter (by omega) hlt
          hdstFit hdisjoint
      have hbLe :
          (fuseProgress memory activeWords (UInt256.ofNat dst) src
            (UInt256.ofNat modulus) mask iter).borrow.toNat ≤ 1 :=
        fuseProgress_borrow_le_one memory activeWords (UInt256.ofNat dst) src
          (UInt256.ofNat modulus) mask iter
      rw [fuseProgress]
      dsimp only
      rw [hoffDst, hoffMod, hm, memoryLimbs_write_next, memoryLimbs_succ,
        Nat.ofDigits_append, Nat.ofDigits_append, Limbs.length_memoryLimbs,
        Limbs.length_memoryLimbs]
      rw [(borrowOut_word _ _ _ hbLe).2]
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.mul_zero, Nat.add_zero]
      exact lex_high (Limbs.radix ^ iter) _ _ _ _ _
        (memoryLimbs_value_lt _ dst iter) (memoryLimbs_value_lt _ modulus iter)
        hbLe hprev
/-! ### Pass B: the in-place subtraction

The reference materialised `sum - modulus` in a `0x1400` scratch buffer during
its second pass and then blended limbwise.  Because pass A already decided
`useSub`, the replacement can simply *not run* pass B when `useSub` is false,
and when it is true it recomputes `dst -= modulus` in place — so the scratch
buffer is never written at all and `0x1400` is free. -/

structure SubPassProgress where
  memory : ByteArray
  activeWords : UInt256
  borrow : UInt256

def subPass (memory : ByteArray) (activeWords dst modulus : UInt256) :
    Nat → SubPassProgress
  | 0 => ⟨memory, activeWords, 0⟩
  | i + 1 =>
      let before := subPass memory activeWords dst modulus i
      let off := ammOffset i
      let dstAt := dst + off
      let modulusAt := modulus + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let m := MachineState.readWord before.memory modulusAt.toNat
      let difference := x - m
      let z := difference - before.borrow
      let borrow := UInt256.lor (UInt256.lt difference before.borrow)
        (UInt256.lt x m)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat modulusAt.toNat 32)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat dstAt.toNat 32)
      ⟨MachineState.writeBytes before.memory
          (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat,
        stored, borrow⟩

theorem subPass_borrow_le_one (memory : ByteArray)
    (activeWords dst modulus : UInt256) (i : Nat) :
    (subPass memory activeWords dst modulus i).borrow.toNat ≤ 1 := by
  cases i with
  | zero =>
      have h0 : (subPass memory activeWords dst modulus 0).borrow = 0 := rfl
      rw [h0]; decide
  | succ i =>
      rw [subPass]
      dsimp only
      rw [Challenge.EvmProof.Word.word_toNat_lor]
      refine or_le_one ?_ ?_ <;>
        rw [Challenge.EvmProof.Word.word_toNat_lt] <;> split <;> omega

/-- Earlier in-place writes cannot affect a destination limb the pass has not
reached yet. -/
theorem readWord_subPass_future_dest (memory : ByteArray)
    (activeWords modulus : UInt256) (dst iter j : Nat)
    (hiter : iter ≤ j) (hfit : dst + 32 * (j + 1) < 2 ^ 256) :
    MachineState.readWord
        (subPass memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (dst + 32 * j) =
      MachineState.readWord memory (dst + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [subPass, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · right
        have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        omega

theorem readWord_subPass_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst) :
    MachineState.readWord
        (subPass memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [subPass, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem memoryLimbs_subPass_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter : Nat)
    (hiter : iter ≤ count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst) :
    Limbs.memoryLimbs
        (subPass memory activeWords (UInt256.ofNat dst) modulus iter).memory
        ptr count = Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [readWord_subPass_disjoint_region memory activeWords modulus dst ptr count
    iter j hiter (by simpa using hj) hdstfit hdisjoint]

theorem represents_subPass_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count) (hdstfit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (subPass memory activeWords (UInt256.ofNat dst) modulus iter).memory
      ptr count value :=
  ⟨hrep.1, (memoryLimbs_subPass_disjoint_region memory activeWords modulus dst
    ptr count iter hiter hdstfit hdisjoint).trans hrep.2⟩

private theorem subPass_step_arith (P D M X z m x b nb R : Nat)
    (hih : D + M = X + P * b) (hstep : z + m + b = x + R * nb) :
    D + P * z + (M + P * m) = X + P * x + P * R * nb := by
  have h1 : D + P * z + (M + P * m) = D + M + P * (z + m) := by ring
  rw [h1, hih]
  have h2 : X + P * b + P * (z + m) = X + P * (z + m + b) := by ring
  rw [h2, hstep]
  ring

/-- **Pass B computes `dst - modulus` in place.**  Exactly the reference's
subtraction pass, except that the difference lands back in `dst` rather than in
the `0x1400` scratch buffer — which is sound because the pass reads `dst[i]`
before writing it and never revisits a limb. -/
theorem subPass_value (memory : ByteArray) (activeWords : UInt256)
    (dst modulus count iter : Nat) (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ modulus ∨ modulus + 32 * count ≤ dst) :
    Nat.ofDigits Limbs.radix
        (Limbs.memoryLimbs
          (subPass memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) iter).memory dst iter) +
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory modulus iter) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory dst iter) +
        Limbs.radix ^ iter *
          (subPass memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) iter).borrow.toNat := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [subPass, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hlt : iter < count := by omega
      have hprev := ih (by omega)
      have hbLe :
          (subPass memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) iter).borrow.toNat ≤ 1 :=
        subPass_borrow_le_one memory activeWords _ _ iter
      have hoffDst :
          ((UInt256.ofNat dst) + ammOffset iter).toNat = dst + 32 * iter :=
        addOffset_toNat dst iter (by omega)
      have hoffMod :
          ((UInt256.ofNat modulus) + ammOffset iter).toNat = modulus + 32 * iter :=
        addOffset_toNat modulus iter (by omega)
      have hx :
          MachineState.readWord
              (subPass memory activeWords (UInt256.ofNat dst)
                (UInt256.ofNat modulus) iter).memory (dst + 32 * iter) =
            MachineState.readWord memory (dst + 32 * iter) :=
        readWord_subPass_future_dest memory activeWords (UInt256.ofNat modulus)
          dst iter iter (by omega) (by omega)
      have hm :
          MachineState.readWord
              (subPass memory activeWords (UInt256.ofNat dst)
                (UInt256.ofNat modulus) iter).memory (modulus + 32 * iter) =
            MachineState.readWord memory (modulus + 32 * iter) :=
        readWord_subPass_disjoint_region memory activeWords (UInt256.ofNat modulus)
          dst modulus count iter iter (by omega) hlt hdstFit hdisjoint
      have hstep := subLimbStep_toNat
        (MachineState.readWord memory (dst + 32 * iter))
        (MachineState.readWord memory (modulus + 32 * iter))
        (subPass memory activeWords (UInt256.ofNat dst)
          (UInt256.ofNat modulus) iter).borrow hbLe
      rw [subPass]
      dsimp only
      rw [hoffDst, hoffMod, hx, hm, memoryLimbs_write_next, memoryLimbs_succ,
        memoryLimbs_succ, Nat.ofDigits_append, Nat.ofDigits_append,
        Nat.ofDigits_append, Limbs.length_memoryLimbs, Limbs.length_memoryLimbs,
        Limbs.length_memoryLimbs]
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.mul_zero, Nat.add_zero]
      rw [word_lor_comm, hstep.2, pow_succ]
      refine subPass_step_arith (Limbs.radix ^ iter) _ _ _ _ _ _ _ _ Limbs.radix
        hprev ?_
      have hxlt : (MachineState.readWord memory (dst + 32 * iter)).toNat <
          Limbs.radix := (MachineState.readWord memory (dst + 32 * iter)).val.isLt
      have hmlt : (MachineState.readWord memory (modulus + 32 * iter)).toNat <
          Limbs.radix :=
        (MachineState.readWord memory (modulus + 32 * iter)).val.isLt
      rw [hstep.1]
      split <;> omega
/-! ### States of the `addMaskedMod` region

The in-place region at `0x0068` is now a trampoline
(`JUMPDEST; PUSH2 0x074b; JUMP`) into the appended body, so `addEntry` keeps its
old program counter and every caller is unaffected.

The body's working frame is, top first,
`[p, carry, borrow, end, ds, dm, mask] ++ [dst, src, take, modulus, n, ret]`,
with `ds = src - dst`, `dm = modulus - dst`, `mask = 0 - take` and
`end = dst + 32 * n`.  Peak stack depth inside the region is 17 words above
`rest`, so `rest.length < 1000` is comfortably sufficient. -/

def ammFrame (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [dst, src, take, modulus, UInt256.ofNat count, returnDest] ++ rest

def ammWork (p carry borrow : UInt256) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [p, carry, borrow, ammEnd dst count, src - dst, modulus - dst, 0 - take] ++
    ammFrame dst src take modulus count returnDest rest

def addEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 104
           stack := [dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

/-- Top of pass A's body (`AMM_LOOP`, byte `0x0766`). -/
def ammLoop (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fuseProgress s.memory s.activeWords dst src modulus (0 - take) i
  { s with pc := UInt256.ofNat 1894
           stack := ammWork (ammPtr dst i) progress.carry progress.borrow
             dst src take modulus count returnDest rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-- The entry guard, reached once from the frame setup (byte `0x075e`). -/
def ammGuardEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { ammLoop s dst src take modulus count 0 returnDest rest with
      pc := UInt256.ofNat 1886 }

/-- `AMM_DECIDE` (byte `0x079b`): pass A is complete. -/
def ammDecide (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { ammLoop s dst src take modulus count (ammCount dst count) returnDest rest with
      pc := UInt256.ofNat 1947 }

/-- `useSub := carry ||| (borrow == 0)`.  This is the one bit that decides
whether pass B runs at all; it is a `UInt256`-valued `def` so the `JUMPI`
certificate can be split off and resolved on its own. -/
def ammUseSub (carry borrow : UInt256) : UInt256 :=
  UInt256.lor carry (UInt256.isZero borrow)

/-- The state immediately before the `useSub` `JUMPI` (byte `0x07a4`), with the
jump target and the negated condition on top. -/
def ammDecideTest (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fuseProgress s.memory s.activeWords dst src modulus (0 - take)
    (ammCount dst count)
  { ammDecide s dst src take modulus count returnDest rest with
      pc := UInt256.ofNat 1956
      stack := [UInt256.ofNat 2005,
        UInt256.isZero (ammUseSub progress.carry progress.borrow)] ++
        ammWork (ammPtr dst (ammCount dst count)) progress.carry progress.borrow
          dst src take modulus count returnDest rest }

/-- Fall-through of that `JUMPI`: pass B is going to run (byte `0x07a5`). -/
def ammSubEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { ammDecide s dst src take modulus count returnDest rest with
      pc := UInt256.ofNat 1957 }

/-- Top of pass B's body (`AMM_SUB`, byte `0x07b3`). -/
def ammSubLoop (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let a := fuseProgress s.memory s.activeWords dst src modulus (0 - take)
    (ammCount dst count)
  let b := subPass a.memory a.activeWords dst modulus i
  { s with pc := UInt256.ofNat 1971
           stack := ammWork (ammPtr dst i) a.carry b.borrow
             dst src take modulus count returnDest rest
           memory := b.memory
           activeWords := b.activeWords }

/-- Final memory of the helper: pass A always, pass B only when `useSub`. -/
def ammFinal (memory : ByteArray) (activeWords dst src modulus mask : UInt256)
    (count : Nat) : SubPassProgress :=
  let a := fuseProgress memory activeWords dst src modulus mask (ammCount dst count)
  if (ammUseSub a.carry a.borrow).toNat = 0 then
    ⟨a.memory, a.activeWords, 0⟩
  else subPass a.memory a.activeWords dst modulus (ammCount dst count)

/-- `AMM_EXIT` (byte `0x07d5`).  Three different predecessors reach it with
three different working frames, but all twelve words are discarded, so the
certificate is stated for an arbitrary frame. -/
def ammExitState (s : State) (memory : ByteArray) (activeWords : UInt256)
    (p carry borrow : UInt256) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2005
           stack := ammWork p carry borrow dst src take modulus count
             returnDest rest
           memory := memory
           activeWords := activeWords }

def addReturned (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let final := ammFinal s.memory s.activeWords dst src modulus (0 - take) count
  { s with pc := returnDest
           stack := rest
           memory := final.memory
           activeWords := final.activeWords }

/-! ### Located paths -/

def ammSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 83 .JUMPDEST, pushAt 84 2 1867, opAt 85 .JUMP, opAt 1356 .JUMPDEST,
   opAt 1357 (.Dup ⟨2, by decide⟩), pushAt 1358 0 0, opAt 1359 .SUB,
   opAt 1360 (.Dup ⟨1, by decide⟩), opAt 1361 (.Dup ⟨5, by decide⟩),
   opAt 1362 .SUB, opAt 1363 (.Dup ⟨2, by decide⟩),
   opAt 1364 (.Dup ⟨4, by decide⟩), opAt 1365 .SUB,
   opAt 1366 (.Dup ⟨7, by decide⟩), pushAt 1367 1 5, opAt 1368 .SHL,
   opAt 1369 (.Dup ⟨4, by decide⟩), opAt 1370 .ADD, pushAt 1371 0 0,
   pushAt 1372 0 0, opAt 1373 (.Dup ⟨6, by decide⟩)]

def ammGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1374 (.Dup ⟨3, by decide⟩), opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 .LT, opAt 1377 .ISZERO, pushAt 1378 2 1947, opAt 1379 .JUMPI]

def ammBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1380 .JUMPDEST, opAt 1381 (.Dup ⟨0, by decide⟩), opAt 1382 .MLOAD,
   opAt 1383 (.Dup ⟨5, by decide⟩), opAt 1384 (.Dup ⟨2, by decide⟩),
   opAt 1385 .ADD, opAt 1386 .MLOAD, opAt 1387 (.Dup ⟨8, by decide⟩),
   opAt 1388 .AND, opAt 1389 (.Dup ⟨1, by decide⟩), opAt 1390 .ADD,
   opAt 1391 (.Dup ⟨3, by decide⟩), opAt 1392 .ADD,
   opAt 1393 (.Dup ⟨0, by decide⟩), opAt 1394 (.Dup ⟨2, by decide⟩),
   opAt 1395 .GT, opAt 1396 (.Swap ⟨1, by decide⟩),
   opAt 1397 (.Dup ⟨1, by decide⟩), opAt 1398 .EQ,
   opAt 1399 (.Dup ⟨4, by decide⟩), opAt 1400 .AND,
   opAt 1401 (.Swap ⟨0, by decide⟩), opAt 1402 (.Swap ⟨1, by decide⟩),
   opAt 1403 .OR, opAt 1404 (.Swap ⟨2, by decide⟩), opAt 1405 .POP,
   opAt 1406 (.Dup ⟨6, by decide⟩), opAt 1407 (.Dup ⟨2, by decide⟩),
   opAt 1408 .ADD, opAt 1409 .MLOAD, opAt 1410 (.Dup ⟨0, by decide⟩),
   opAt 1411 (.Dup ⟨2, by decide⟩), opAt 1412 .LT,
   opAt 1413 (.Swap ⟨0, by decide⟩), opAt 1414 (.Dup ⟨2, by decide⟩),
   opAt 1415 .EQ, opAt 1416 (.Dup ⟨5, by decide⟩), opAt 1417 .AND,
   opAt 1418 .OR, opAt 1419 (.Swap ⟨3, by decide⟩), opAt 1420 .POP,
   opAt 1421 (.Dup ⟨1, by decide⟩), opAt 1422 .MSTORE, pushAt 1423 1 32,
   opAt 1424 .ADD, opAt 1425 (.Dup ⟨3, by decide⟩),
   opAt 1426 (.Dup ⟨1, by decide⟩), opAt 1427 .LT, pushAt 1428 2 1894,
   opAt 1429 .JUMPI]

def ammDecidePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1430 .JUMPDEST, opAt 1431 (.Dup ⟨2, by decide⟩), opAt 1432 .ISZERO,
   opAt 1433 (.Dup ⟨2, by decide⟩), opAt 1434 .OR, opAt 1435 .ISZERO,
   pushAt 1436 2 2005]

def ammDecideJumpiPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1437 .JUMPI]

def ammSubSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1438 (.Dup ⟨7, by decide⟩), opAt 1439 (.Swap ⟨0, by decide⟩),
   opAt 1440 .POP, pushAt 1441 0 0, opAt 1442 (.Swap ⟨2, by decide⟩),
   opAt 1443 .POP, opAt 1444 (.Dup ⟨3, by decide⟩),
   opAt 1445 (.Dup ⟨1, by decide⟩), opAt 1446 .LT, opAt 1447 .ISZERO,
   pushAt 1448 2 2005, opAt 1449 .JUMPI]

def ammSubBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1450 .JUMPDEST, opAt 1451 (.Dup ⟨0, by decide⟩), opAt 1452 .MLOAD,
   opAt 1453 (.Dup ⟨6, by decide⟩), opAt 1454 (.Dup ⟨2, by decide⟩),
   opAt 1455 .ADD, opAt 1456 .MLOAD, opAt 1457 (.Dup ⟨0, by decide⟩),
   opAt 1458 (.Dup ⟨2, by decide⟩), opAt 1459 .LT,
   opAt 1460 (.Swap ⟨1, by decide⟩), opAt 1461 .SUB,
   opAt 1462 (.Dup ⟨4, by decide⟩), opAt 1463 (.Dup ⟨1, by decide⟩),
   opAt 1464 .LT, opAt 1465 (.Swap ⟨0, by decide⟩),
   opAt 1466 (.Dup ⟨5, by decide⟩), opAt 1467 (.Swap ⟨0, by decide⟩),
   opAt 1468 .SUB, opAt 1469 (.Dup ⟨3, by decide⟩), opAt 1470 .MSTORE,
   opAt 1471 .OR, opAt 1472 (.Swap ⟨2, by decide⟩), opAt 1473 .POP,
   pushAt 1474 1 32, opAt 1475 .ADD, opAt 1476 (.Dup ⟨3, by decide⟩),
   opAt 1477 (.Dup ⟨1, by decide⟩), opAt 1478 .LT, pushAt 1479 2 1971,
   opAt 1480 .JUMPI]

def ammExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1481 .JUMPDEST, opAt 1482 .POP, opAt 1483 .POP, opAt 1484 .POP,
   opAt 1485 .POP, opAt 1486 .POP, opAt 1487 .POP, opAt 1488 .POP,
   opAt 1489 .POP, opAt 1490 .POP, opAt 1491 .POP, opAt 1492 .POP,
   opAt 1493 .POP, opAt 1494 .JUMP]

/-! ### Block certificates -/

set_option linter.unusedSimpArgs false in
theorem run_ammSetup (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammSetupPath
      (addEntry s dst src take modulus count returnDest rest) =
        some (ammGuardEntry s dst src take modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hentryW : (1867 : UInt256) = UInt256.ofNat 1867 := by decide
  have hentry : (UInt256.ofNat 1867).toNat = 1867 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 1867).toNat = true := by
    rw [hentry]; exact jumpAMM
  simp [ammSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addEntry, ammGuardEntry, ammLoop, ammWork, ammFrame, ammEnd, fuseProgress,
    ammPtr_zero,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hcode, hrun, hzero, hzero',
    hfive, hentryW, hentry, hjump, jumpAMM,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammGuardBody (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : 0 < ammCount dst count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammGuardPath
      (ammGuardEntry s dst src take modulus count returnDest rest) =
        some (ammLoop s dst src take modulus count 0 returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hlt : (ammPtr dst 0).toNat < (ammEnd dst count).toNat :=
    (ammPtr_lt_end_iff dst count 0 (by omega)).mpr hcount
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [ammGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammGuardEntry, ammLoop, ammWork, ammFrame, hc13, hc14, hc15, hrun,
    UInt256.lt, UInt256.isTrue, hlt, honeIsZero,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammGuardSkip (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : ammCount dst count = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammGuardPath
      (ammGuardEntry s dst src take modulus count returnDest rest) =
        some (ammDecide s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hnlt : ¬ ((ammPtr dst 0).toNat < (ammEnd dst count).toNat) := by
    intro h
    exact absurd ((ammPtr_lt_end_iff dst count 0 (by omega)).mp h) (by omega)
  have hzeroIsZero : (UInt256.ofNat 0).isZero.toNat = 1 := by decide
  have hdecW : (1947 : UInt256) = UInt256.ofNat 1947 := by decide
  have hdecN : (UInt256.ofNat 1947).toNat = 1947 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 1947).toNat = true := by
    rw [hdecN]; exact jumpAMM_DECIDE
  simp [ammGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammGuardEntry, ammDecide, ammLoop, ammWork, ammFrame, hcount, hc13, hc14,
    hc15, hcode, hrun, UInt256.lt, UInt256.isTrue, hnlt, hzeroIsZero, hdecW, hdecN,
    hjump, jumpAMM_DECIDE,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < ammCount dst count)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammBodyPath
      (ammLoop s dst src take modulus count i returnDest rest) =
        some (ammLoop s dst src take modulus count (i + 1) returnDest rest) := by
  have hfits : dst.toNat + 32 * (i + 1) < 2 ^ 256 :=
    ammCount_fits dst count (i + 1) (by omega)
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hsucc : (32 : UInt256) + (dst + ammOffset i) = dst + ammOffset (i + 1) :=
    ammPtr_succ dst i (by omega)
  have hsrcAt : dst + ammOffset i + (src - dst) = src + ammOffset i :=
    word_add_sub_add dst src (ammOffset i)
  have hmodAt : dst + ammOffset i + (modulus - dst) = modulus + ammOffset i :=
    word_add_sub_add dst modulus (ammOffset i)
  have hlt : (dst + ammOffset (i + 1)).toNat < (ammEnd dst count).toNat :=
    (ammPtr_lt_end_iff dst count (i + 1) (by omega)).mpr hi
  have hltWord :
      UInt256.lt (dst + ammOffset (i + 1)) (ammEnd dst count) = UInt256.ofNat 1 := by
    rw [UInt256.lt, if_pos hlt]
  have honeNat : (UInt256.ofNat 1).toNat = 1 := by decide
  have hloopW : (1894 : UInt256) = UInt256.ofNat 1894 := by decide
  have hloopN : (UInt256.ofNat 1894).toNat = 1894 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 1894).toNat = true := by
    rw [hloopN]; exact jumpAMM_LOOP
  simp (config := { maxSteps := 2000000 })
    [ammBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      ammLoop, ammWork, ammFrame, fuseProgress, ammPtr,
      hc13, hc14, hc15, hc16, hc17, hc18, hcode, hrun,
      hsucc, hsrcAt, hmodAt, hltWord, honeNat, hloopW, hloopN, hjump, jumpAMM_LOOP,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.isTrue, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammBodyLast (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 = ammCount dst count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammBodyPath
      (ammLoop s dst src take modulus count i returnDest rest) =
        some (ammDecide s dst src take modulus count returnDest rest) := by
  have hfits : dst.toNat + 32 * (i + 1) < 2 ^ 256 :=
    ammCount_fits dst count (i + 1) (by omega)
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hsucc : (32 : UInt256) + (dst + ammOffset i) = dst + ammOffset (i + 1) :=
    ammPtr_succ dst i (by omega)
  have hsrcAt : dst + ammOffset i + (src - dst) = src + ammOffset i :=
    word_add_sub_add dst src (ammOffset i)
  have hmodAt : dst + ammOffset i + (modulus - dst) = modulus + ammOffset i :=
    word_add_sub_add dst modulus (ammOffset i)
  have hnlt : ¬ ((dst + ammOffset (i + 1)).toNat < (ammEnd dst count).toNat) := by
    intro h
    exact absurd ((ammPtr_lt_end_iff dst count (i + 1) (by omega)).mp h) (by omega)
  have hltWord :
      UInt256.lt (dst + ammOffset (i + 1)) (ammEnd dst count) = UInt256.ofNat 0 := by
    rw [UInt256.lt, if_neg hnlt]
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  simp (config := { maxSteps := 2000000 })
    [ammBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      ammLoop, ammDecide, ammWork, ammFrame, fuseProgress, ammPtr, ← hi,
      hc13, hc14, hc15, hc16, hc17, hc18, hrun,
      hsucc, hsrcAt, hmodAt, hltWord, hzeroNat,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.isTrue, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammDecide (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammDecidePath
      (ammDecide s dst src take modulus count returnDest rest) =
        some (ammDecideTest s dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hexitW : (2005 : UInt256) = UInt256.ofNat 2005 := by decide
  simp [ammDecidePath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammDecide, ammDecideTest, ammLoop, ammWork, ammFrame, ammUseSub,
    hc13, hc14, hc15, hrun, hexitW,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammDecideSkip (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (huse : (ammUseSub
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow).toNat
        = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammDecideJumpiPath
      (ammDecideTest s dst src take modulus count returnDest rest) =
        some (ammExitState s
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).memory
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).activeWords
          (ammPtr dst (ammCount dst count))
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow
          dst src take modulus count returnDest rest) := by
  have hc15 : rest.length + 15 < 1024 := by omega
  have hisZero : (UInt256.isZero (ammUseSub
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow)).toNat
        = 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero, if_pos huse]
  have hexitN : (UInt256.ofNat 2005).toNat = 2005 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 2005).toNat = true := by
    rw [hexitN]; exact jumpAMM_EXIT
  simp [ammDecideJumpiPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammDecideTest, ammDecide, ammLoop, ammExitState, ammWork, ammFrame,
    hc15, hcode, hrun, UInt256.isTrue, hisZero, hexitN, hjump, jumpAMM_EXIT,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammDecideSub (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (huse : (ammUseSub
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow).toNat
        ≠ 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammDecideJumpiPath
      (ammDecideTest s dst src take modulus count returnDest rest) =
        some (ammSubEntry s dst src take modulus count returnDest rest) := by
  have hc15 : rest.length + 15 < 1024 := by omega
  have hisZero : (UInt256.isZero (ammUseSub
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow)).toNat
        = 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero, if_neg huse]
  simp [ammDecideJumpiPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammDecideTest, ammDecide, ammSubEntry, ammLoop, ammWork, ammFrame,
    hc15, hrun, UInt256.isTrue, hisZero,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_ammSubSetup (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : 0 < ammCount dst count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammSubSetupPath
      (ammSubEntry s dst src take modulus count returnDest rest) =
        some (ammSubLoop s dst src take modulus count 0 returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hzeroLit : ({ val := 0 } : UInt256) = (0 : UInt256) := by decide
  have hlt : dst.toNat < (ammEnd dst count).toNat := by
    have h := (ammPtr_lt_end_iff dst count 0 (by omega)).mpr hcount
    rwa [ammPtr_zero] at h
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [ammSubSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammSubEntry, ammDecide, ammLoop, ammSubLoop, ammWork, ammFrame, subPass,
    ammPtr_zero, hc13, hc14, hc15, hrun, hzeroLit,
    UInt256.lt, UInt256.isTrue, hlt, honeIsZero,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammSubSetupEmpty (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : ammCount dst count = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammSubSetupPath
      (ammSubEntry s dst src take modulus count returnDest rest) =
        some (ammExitState s
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
            (ammCount dst count)).memory
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
            (ammCount dst count)).activeWords
          dst
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
            (ammCount dst count)).carry
          0 dst src take modulus count returnDest rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hzeroLit : ({ val := 0 } : UInt256) = (0 : UInt256) := by decide
  have hnlt : ¬ (dst.toNat < (ammEnd dst count).toNat) := by
    intro h
    have h0 : (ammPtr dst 0).toNat < (ammEnd dst count).toNat := by
      rwa [ammPtr_zero]
    exact absurd ((ammPtr_lt_end_iff dst count 0 (by omega)).mp h0) (by omega)
  have hzeroIsZero : (UInt256.ofNat 0).isZero.toNat = 1 := by decide
  have hexitW : (2005 : UInt256) = UInt256.ofNat 2005 := by decide
  have hexitN : (UInt256.ofNat 2005).toNat = 2005 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 2005).toNat = true := by
    rw [hexitN]; exact jumpAMM_EXIT
  simp [ammSubSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammSubEntry, ammDecide, ammLoop, ammExitState, ammWork, ammFrame,
    hcount, hc13, hc14, hc15, hcode, hrun, hzeroLit,
    UInt256.lt, UInt256.isTrue, hnlt, hzeroIsZero, hexitW, hexitN, hjump,
    jumpAMM_EXIT,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammSubBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < ammCount dst count)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammSubBodyPath
      (ammSubLoop s dst src take modulus count i returnDest rest) =
        some (ammSubLoop s dst src take modulus count (i + 1) returnDest rest) := by
  have hfits : dst.toNat + 32 * (i + 1) < 2 ^ 256 :=
    ammCount_fits dst count (i + 1) (by omega)
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hsucc : (32 : UInt256) + (dst + ammOffset i) = dst + ammOffset (i + 1) :=
    ammPtr_succ dst i (by omega)
  have hmodAt : dst + ammOffset i + (modulus - dst) = modulus + ammOffset i :=
    word_add_sub_add dst modulus (ammOffset i)
  have hlt : (dst + ammOffset (i + 1)).toNat < (ammEnd dst count).toNat :=
    (ammPtr_lt_end_iff dst count (i + 1) (by omega)).mpr hi
  have hltWord :
      UInt256.lt (dst + ammOffset (i + 1)) (ammEnd dst count) = UInt256.ofNat 1 := by
    rw [UInt256.lt, if_pos hlt]
  have honeNat : (UInt256.ofNat 1).toNat = 1 := by decide
  have hsubW : (1971 : UInt256) = UInt256.ofNat 1971 := by decide
  have hsubN : (UInt256.ofNat 1971).toNat = 1971 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat 1971).toNat = true := by
    rw [hsubN]; exact jumpAMM_SUB
  simp (config := { maxSteps := 2000000 })
    [ammSubBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      ammSubLoop, ammWork, ammFrame, subPass, ammPtr,
      hc13, hc14, hc15, hc16, hc17, hc18, hcode, hrun,
      hsucc, hmodAt, hltWord, honeNat, hsubW, hsubN, hjump, jumpAMM_SUB,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.isTrue, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammSubBodyLast (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 = ammCount dst count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammSubBodyPath
      (ammSubLoop s dst src take modulus count i returnDest rest) =
        some (ammExitState s
          (subPass (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).memory
            (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).activeWords dst modulus
            (ammCount dst count)).memory
          (subPass (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).memory
            (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).activeWords dst modulus
            (ammCount dst count)).activeWords
          (ammPtr dst (ammCount dst count))
          (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).carry
          (subPass (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).memory
            (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
              (ammCount dst count)).activeWords dst modulus
            (ammCount dst count)).borrow
          dst src take modulus count returnDest rest) := by
  have hfits : dst.toNat + 32 * (i + 1) < 2 ^ 256 :=
    ammCount_fits dst count (i + 1) (by omega)
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hsucc : (32 : UInt256) + (dst + ammOffset i) = dst + ammOffset (i + 1) :=
    ammPtr_succ dst i (by omega)
  have hmodAt : dst + ammOffset i + (modulus - dst) = modulus + ammOffset i :=
    word_add_sub_add dst modulus (ammOffset i)
  have hnlt : ¬ ((dst + ammOffset (i + 1)).toNat < (ammEnd dst count).toNat) := by
    intro h
    exact absurd ((ammPtr_lt_end_iff dst count (i + 1) (by omega)).mp h) (by omega)
  have hltWord :
      UInt256.lt (dst + ammOffset (i + 1)) (ammEnd dst count) = UInt256.ofNat 0 := by
    rw [UInt256.lt, if_neg hnlt]
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  simp (config := { maxSteps := 2000000 })
    [ammSubBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      ammSubLoop, ammExitState, ammWork, ammFrame, subPass, ammPtr, ← hi,
      hc13, hc14, hc15, hc16, hc17, hc18, hrun,
      hsucc, hmodAt, hltWord, hzeroNat,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.isTrue, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_ammExit (s : State) (memory : ByteArray)
    (activeWords p carry borrow : UInt256) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock ammExitPath
      (ammExitState s memory activeWords p carry borrow dst src take modulus
        count returnDest rest) =
        some { s with pc := returnDest
                      stack := rest
                      memory := memory
                      activeWords := activeWords } := by
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
  simp [ammExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    ammExitState, ammWork, ammFrame, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ### Whole-helper execution certificate

`gasSteps_addMaskedMod` keeps the reference's signature exactly.  The
replacement compares addresses rather than an index, which would ordinarily
need a no-wrap hypothesis the gas layer's callers cannot supply; instead the
model counts iterations with `ammCount`, which is exact for every `dst` and
`count`.  Nothing here requires `dst + 32 * count` not to wrap — that is needed
only by the correctness layer, which already carries it as `hdstFit`. -/

def gasSteps_ammSetup (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (ammGuardEntry s dst src take modulus count returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka ammSetupPath
      (by simpa [addEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [addEntry, State.fork] using hfork)
      (run_ammSetup s dst src take modulus count returnDest rest hcap hcode hrun)
      (by simpa [addEntry] using hrun)
      (by simpa [addEntry, State.fork] using hnp)

def gasSteps_ammBodyStep (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < ammCount dst count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ammLoop s dst src take modulus count i returnDest rest)
      (ammLoop s dst src take modulus count (i + 1) returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka ammBodyPath
      (by simpa [ammLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [ammLoop, State.fork] using hfork)
      (run_ammBody s dst src take modulus count i returnDest rest hcap hi
        hcode hrun)
      (by simpa [ammLoop] using hrun)
      (by simpa [ammLoop, State.fork] using hnp)

def gasSteps_ammSubStep (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < ammCount dst count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ammSubLoop s dst src take modulus count i returnDest rest)
      (ammSubLoop s dst src take modulus count (i + 1) returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka ammSubBodyPath
      (by simpa [ammSubLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [ammSubLoop, State.fork] using hfork)
      (run_ammSubBody s dst src take modulus count i returnDest rest hcap hi
        hcode hrun)
      (by simpa [ammSubLoop] using hrun)
      (by simpa [ammSubLoop, State.fork] using hnp)

/-- `addEntry` through the whole of pass A, ending at `AMM_DECIDE`. -/
def gasSteps_ammPassA (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (ammDecide s dst src take modulus count returnDest rest) := by
  refine (gasSteps_ammSetup s dst src take modulus count returnDest rest hcap
    hcode hfork hrun hnp).trans ?_
  cases hcnt : ammCount dst count with
  | zero =>
      exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammGuardPath
          (by simpa [ammGuardEntry, ammLoop, Artifact.submissionArtifact] using hcode)
          (by simpa [ammGuardEntry, ammLoop, State.fork] using hfork)
          (run_ammGuardSkip s dst src take modulus count returnDest rest hcap hcnt
            hcode hrun)
          (by simpa [ammGuardEntry, ammLoop] using hrun)
          (by simpa [ammGuardEntry, ammLoop, State.fork] using hnp)
  | succ k =>
      refine (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammGuardPath
          (by simpa [ammGuardEntry, ammLoop, Artifact.submissionArtifact] using hcode)
          (by simpa [ammGuardEntry, ammLoop, State.fork] using hfork)
          (run_ammGuardBody s dst src take modulus count returnDest rest hcap
            (by omega) hrun)
          (by simpa [ammGuardEntry, ammLoop] using hrun)
          (by simpa [ammGuardEntry, ammLoop, State.fork] using hnp)).trans ?_
      refine (Challenge.EvmProof.GasSteps.iterateBounded k (fun i hi =>
        gasSteps_ammBodyStep s dst src take modulus count i returnDest rest
          hcap (by omega) hcode hfork hrun hnp)).trans ?_
      exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammBodyPath
          (by simpa [ammLoop, Artifact.submissionArtifact] using hcode)
          (by simpa [ammLoop, State.fork] using hfork)
          (run_ammBodyLast s dst src take modulus count k returnDest rest hcap
            (by omega) hrun)
          (by simpa [ammLoop] using hrun)
          (by simpa [ammLoop, State.fork] using hnp)

/-- Pass B, from the fall-through of the `useSub` test to `AMM_EXIT`.  The exit
frame is irrelevant, so only the memory and `activeWords` are pinned. -/
def gasSteps_ammPassB (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (ammSubEntry s dst src take modulus count returnDest rest)
      { s with pc := UInt256.ofNat 2005
               stack := ammWork (ammPtr dst (ammCount dst count))
                 (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).carry
                 (subPass
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).memory
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).activeWords dst modulus (ammCount dst count)).borrow
                 dst src take modulus count returnDest rest
               memory := (subPass
                 (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).memory
                 (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).activeWords dst modulus (ammCount dst count)).memory
               activeWords := (subPass
                 (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).memory
                 (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).activeWords dst modulus (ammCount dst count)).activeWords } := by
  cases hcnt : ammCount dst count with
  | zero =>
      have hstep := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammSubSetupPath
          (by simpa [ammSubEntry, ammDecide, ammLoop,
            Artifact.submissionArtifact] using hcode)
          (by simpa [ammSubEntry, ammDecide, ammLoop, State.fork] using hfork)
          (run_ammSubSetupEmpty s dst src take modulus count returnDest rest hcap
            hcnt hcode hrun)
          (by simpa [ammSubEntry, ammDecide, ammLoop] using hrun)
          (by simpa [ammSubEntry, ammDecide, ammLoop, State.fork] using hnp)
      simpa [ammExitState, ammWork, hcnt, ammPtr_zero, subPass] using hstep
  | succ k =>
      refine (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammSubSetupPath
          (by simpa [ammSubEntry, ammDecide, ammLoop,
            Artifact.submissionArtifact] using hcode)
          (by simpa [ammSubEntry, ammDecide, ammLoop, State.fork] using hfork)
          (run_ammSubSetup s dst src take modulus count returnDest rest hcap
            (by omega) hrun)
          (by simpa [ammSubEntry, ammDecide, ammLoop] using hrun)
          (by simpa [ammSubEntry, ammDecide, ammLoop, State.fork] using hnp)).trans ?_
      refine (Challenge.EvmProof.GasSteps.iterateBounded k (fun i hi =>
        gasSteps_ammSubStep s dst src take modulus count i returnDest rest
          hcap (by omega) hcode hfork hrun hnp)).trans ?_
      have hlast := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka ammSubBodyPath
          (by simpa [ammSubLoop, Artifact.submissionArtifact] using hcode)
          (by simpa [ammSubLoop, State.fork] using hfork)
          (run_ammSubBodyLast s dst src take modulus count k returnDest rest
            hcap (by omega) hrun)
          (by simpa [ammSubLoop] using hrun)
          (by simpa [ammSubLoop, State.fork] using hnp)
      simpa [ammExitState, hcnt] using hlast

set_option linter.unusedVariables false in
def gasSteps_addMaskedMod (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (addReturned s dst src take modulus count returnDest rest) := by
  refine (gasSteps_ammPassA s dst src take modulus count returnDest rest hcap
    hcode hfork hrun hnp).trans ?_
  refine (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka ammDecidePath
      (by simpa [ammDecide, ammLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [ammDecide, ammLoop, State.fork] using hfork)
      (run_ammDecide s dst src take modulus count returnDest rest hcap hrun)
      (by simpa [ammDecide, ammLoop] using hrun)
      (by simpa [ammDecide, ammLoop, State.fork] using hnp)).trans ?_
  by_cases huse : (ammUseSub
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).carry
      (fuseProgress s.memory s.activeWords dst src modulus (0 - take)
        (ammCount dst count)).borrow).toNat
        = 0
  · have hfinal : addReturned s dst src take modulus count returnDest rest =
        { s with pc := returnDest
                 stack := rest
                 memory := (fuseProgress s.memory s.activeWords dst src modulus
                   (0 - take) (ammCount dst count)).memory
                 activeWords := (fuseProgress s.memory s.activeWords dst src
                   modulus (0 - take) (ammCount dst count)).activeWords } := by
      simp only [addReturned, ammFinal]
      rw [if_pos huse]
    rw [hfinal]
    refine (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka ammDecideJumpiPath
        (by simpa [ammDecideTest, ammDecide, ammLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [ammDecideTest, ammDecide, ammLoop, State.fork] using hfork)
        (run_ammDecideSkip s dst src take modulus count returnDest rest hcap huse
          hcode hrun)
        (by simpa [ammDecideTest, ammDecide, ammLoop] using hrun)
        (by simpa [ammDecideTest, ammDecide, ammLoop, State.fork] using hnp)).trans ?_
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka ammExitPath
        (by simpa [ammExitState, Artifact.submissionArtifact] using hcode)
        (by simpa [ammExitState, State.fork] using hfork)
        (run_ammExit s _ _ _ _ _ dst src take modulus count returnDest rest hcap
          hcode hvalid hrun)
        (by simpa [ammExitState] using hrun)
        (by simpa [ammExitState, State.fork] using hnp)
  · have hfinal : addReturned s dst src take modulus count returnDest rest =
        { s with pc := returnDest
                 stack := rest
                 memory := (subPass
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).memory
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).activeWords dst modulus (ammCount dst count)).memory
                 activeWords := (subPass
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).memory
                   (fuseProgress s.memory s.activeWords dst src modulus
                     (0 - take) (ammCount dst count)).activeWords dst modulus (ammCount dst count)).activeWords } := by
      simp only [addReturned, ammFinal]
      rw [if_neg huse]
    rw [hfinal]
    refine (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka ammDecideJumpiPath
        (by simpa [ammDecideTest, ammDecide, ammLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [ammDecideTest, ammDecide, ammLoop, State.fork] using hfork)
        (run_ammDecideSub s dst src take modulus count returnDest rest hcap huse
          hrun)
        (by simpa [ammDecideTest, ammDecide, ammLoop] using hrun)
        (by simpa [ammDecideTest, ammDecide, ammLoop, State.fork] using hnp)).trans ?_
    refine (gasSteps_ammPassB s dst src take modulus count returnDest rest hcap
      hcode hfork hrun hnp).trans ?_
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka ammExitPath
        (by simpa [Artifact.submissionArtifact] using hcode)
        (by simpa [State.fork] using hfork)
        (run_ammExit s _ _ (ammPtr dst (ammCount dst count)) _ _ dst src take
          modulus count returnDest rest hcap hcode hvalid hrun)
        (by simpa using hrun)
        (by simpa [State.fork] using hnp)

/-! ### Functional contract for `addMaskedMod`

`hcandidateFit`, `hdstCandidate` and `hmodulusCandidate` are retained for source
compatibility and are no longer needed: the replacement never writes the
`0x1400` scratch buffer.  `hdstModulus`, by contrast, is now **load-bearing** —
pass A reads `modulus[i]` after writing `dst[0..i-1]`, so the fused loop agrees
with the reference exactly when those regions are disjoint. -/

set_option linter.unusedVariables false in
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
    (hmodulusBound : modulusValue < Limbs.radix ^ count) :
    Limbs.Represents
      (addReturned s (UInt256.ofNat dst) (UInt256.ofNat src)
        (UInt256.ofNat take) (UInt256.ofNat modulus) count returnDest rest).memory
      dst count ((x + take * y) % modulusValue) := by
  have hdstNat : (UInt256.ofNat dst).toNat = dst := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAmmCount : ammCount (UInt256.ofNat dst) count = count :=
    ammCount_eq_count _ _ (by rw [hdstNat]; omega)
  simp only [addReturned, ammFinal, hAmmCount]
  set mask : UInt256 := 0 - UInt256.ofNat take with hmask
  set A := fuseProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat src) (UInt256.ofNat modulus) mask count with hA
  set total := x + take * y with htotal
  set bound := Limbs.radix ^ count with hbound
  set wrapped := total % bound with hwrapped
  have hM0 : 0 < modulusValue := by omega
  have htotalLt : total < 2 * modulusValue :=
    Limbs.masked_sum_lt_twice_of_le hx hy htake
  have hwrappedLt : wrapped < bound := Nat.mod_lt _ (pow_pos Limbs.radix_pos _)
  -- pass A is memory-identical to the reference's first pass
  have hAmem : A.memory = (addProgress s.memory s.activeWords (UInt256.ofNat dst)
      (UInt256.ofNat src) mask count).memory :=
    fuseProgress_memory _ _ _ _ _ _ _
  have hAcarry : A.carry = (addProgress s.memory s.activeWords (UInt256.ofNat dst)
      (UInt256.ofNat src) mask count).carry :=
    fuseProgress_carry _ _ _ _ _ _ _
  have hadded : Limbs.Represents A.memory dst count wrapped := by
    rw [hAmem]
    exact addProgress_represents_wrapped s.memory s.activeWords dst src count
      take x y htake hdstFit hsrcFit halias hdst hsrc
  have haddValue :
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs A.memory dst count) +
          bound * A.carry.toNat = total ∧ A.carry.toNat ≤ 1 := by
    rw [hAmem, hAcarry]
    simpa [bound, total] using
      addProgress_value_carry s.memory s.activeWords dst src count take x y
        htake hdstFit hsrcFit halias hdst hsrc
  have haddedModulus : Limbs.Represents A.memory modulus count modulusValue :=
    represents_fuseProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat src) (UInt256.ofNat modulus) mask dst modulus count count
      modulusValue (by omega) hdstFit hdstModulus hmodulus
  -- the fused borrow decides `wrapped < modulusValue`
  have hborrowIff : A.borrow.toNat = 1 ↔ wrapped < modulusValue := by
    have h := fuseProgress_borrow_iff s.memory s.activeWords (UInt256.ofNat src)
      mask dst modulus count count (by omega) hdstFit hmodulusFit hdstModulus
    rw [Limbs.value_of_represents hadded, Limbs.value_of_represents hmodulus] at h
    exact h
  have hborrowLe : A.borrow.toNat ≤ 1 :=
    fuseProgress_borrow_le_one _ _ _ _ _ _ _
  have hcarryIff : A.carry.toNat = 1 ↔ bound ≤ total := by
    apply carry_eq_one_iff hwrappedLt haddValue.2
    simpa [Limbs.value_of_represents hadded] using haddValue.1
  have hborrowZero : A.borrow.toNat = 0 ↔ modulusValue ≤ wrapped := by
    constructor
    · intro h0
      by_contra hlt
      exact absurd (hborrowIff.mpr (by omega)) (by omega)
    · intro hge
      by_contra hne
      exact absurd (hborrowIff.mp (by omega)) (by omega)
  have huseSubLe : (ammUseSub A.carry A.borrow).toNat ≤ 1 :=
    useSub_toNat_le_one A.carry A.borrow haddValue.2 hborrowLe
  have huseSubIff : (ammUseSub A.carry A.borrow).toNat = 1 ↔
      modulusValue ≤ total :=
    useSub_eq_one_iff A.carry A.borrow hmodulusBound rfl haddValue.2 hborrowLe
      hcarryIff hborrowZero
  by_cases huse : (ammUseSub A.carry A.borrow).toNat = 0
  · -- pass B does not run: the wrapped sum is already the residue
    rw [if_pos huse]
    have hlt : total < modulusValue := by
      by_contra hge
      exact absurd (huseSubIff.mpr (by omega)) (by omega)
    have hmod : total % modulusValue = wrapped := by
      rw [hwrapped, Nat.mod_eq_of_lt (by omega : total < bound),
        Nat.mod_eq_of_lt hlt]
    rw [hmod]
    exact hadded
  · -- pass B runs in place, and its borrow mirrors pass A's carry
    rw [if_neg huse]
    have hge : modulusValue ≤ total := huseSubIff.mp (by omega)
    set B := subPass A.memory A.activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) count with hB
    have hsub :
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs B.memory dst count) +
            Nat.ofDigits Limbs.radix (Limbs.memoryLimbs A.memory modulus count) =
          Nat.ofDigits Limbs.radix (Limbs.memoryLimbs A.memory dst count) +
            Limbs.radix ^ count * B.borrow.toNat :=
      subPass_value A.memory A.activeWords dst modulus count count (by omega)
        hdstFit hmodulusFit hdstModulus
    rw [Limbs.value_of_represents haddedModulus,
      Limbs.value_of_represents hadded] at hsub
    have hBlt : Nat.ofDigits Limbs.radix (Limbs.memoryLimbs B.memory dst count) <
        bound := memoryLimbs_value_lt B.memory dst count
    have hBborrowLe : B.borrow.toNat ≤ 1 := subPass_borrow_le_one _ _ _ _ _
    have haddEq : wrapped + bound * A.carry.toNat = total := by
      simpa [Limbs.value_of_represents hadded] using haddValue.1
    have hvalue :
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs B.memory dst count) =
          total % modulusValue := by
      rw [Limbs.mod_eq_cond_sub htotalLt, if_neg (by omega)]
      set v := Nat.ofDigits Limbs.radix (Limbs.memoryLimbs B.memory dst count)
        with hv
      set c := A.carry.toNat with hc
      set b := B.borrow.toNat with hb
      have hcLe : c ≤ 1 := haddValue.2
      interval_cases c <;> interval_cases b <;> omega
    have hfit : total % modulusValue < bound :=
      (Nat.mod_lt total (by omega)).trans hmodulusBound
    rw [Limbs.represents_iff_value hfit, hvalue]

set_option linter.unusedVariables false in
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
  have hdstNat : (UInt256.ofNat dst).toNat = dst := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAmmCount : ammCount (UInt256.ofNat dst) count = count :=
    ammCount_eq_count _ _ (by rw [hdstNat]; omega)
  have hA : Limbs.Represents
      (fuseProgress s.memory s.activeWords (UInt256.ofNat dst)
        (UInt256.ofNat src) (UInt256.ofNat modulus)
        (0 - UInt256.ofNat take) count).memory ptr count value :=
    represents_fuseProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat src) (UInt256.ofNat modulus) (0 - UInt256.ofNat take) dst
      ptr count count value (by omega) hdstFit hptrDst hrep
  simp only [addReturned, ammFinal, hAmmCount]
  split
  · exact hA
  · exact represents_subPass_disjoint_region _ _ (UInt256.ofNat modulus) dst ptr
      count count value (by omega) hdstFit hptrDst hA
end Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
