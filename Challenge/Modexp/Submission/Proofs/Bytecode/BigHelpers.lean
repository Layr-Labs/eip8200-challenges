import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
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
  [opAt 14 .JUMPDEST,
   pushAt 15 0 0]

def clearGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 16 .JUMPDEST,
   opAt 17 (.Dup ⟨2, by decide⟩),
   opAt 18 (.Dup ⟨1, by decide⟩),
   opAt 19 .LT,
   opAt 20 .ISZERO,
   pushAt 21 2 47,
   opAt 22 .JUMPI]

def clearBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 23 0 0,
   opAt 24 (.Dup ⟨1, by decide⟩),
   pushAt 25 1 5,
   opAt 26 .SHL,
   opAt 27 (.Dup ⟨3, by decide⟩),
   opAt 28 .ADD,
   opAt 29 .MSTORE,
   pushAt 30 1 1,
   opAt 31 (.Dup ⟨1, by decide⟩),
   opAt 32 .ADD,
   opAt 33 (.Swap ⟨0, by decide⟩),
   opAt 34 .POP,
   pushAt 35 2 20,
   opAt 36 .JUMP]

def clearExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 37 .JUMPDEST,
   opAt 38 .POP,
   opAt 39 .POP,
   opAt 40 .POP,
   opAt 41 .JUMP]

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
  { s with pc := UInt256.ofNat 18
           stack := [ptr, UInt256.ofNat count, returnDest] ++ rest }

def clearLoop (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 20
           stack := [UInt256.ofNat i, ptr, UInt256.ofNat count, returnDest] ++ rest
           memory := clearMemory s.memory ptr i
           activeWords := clearWords s.activeWords ptr i }

def clearExit (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { clearLoop s ptr count count returnDest rest with pc := UInt256.ofNat 47 }

def clearBodyEntry (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { clearLoop s ptr count i returnDest rest with pc := UInt256.ofNat 29 }

def clearReturned (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rest
           memory := clearMemory s.memory ptr count
           activeWords := clearWords s.activeWords ptr count }

@[simp] private theorem clearPCs (i : Nat)
    (hi : 14 ≤ i) (hii : i ≤ 41) :
    Artifact.submissionArtifact.instructionPC i =
      ([18,19,20,21,22,23,24,25,28,29,30,31,33,34,35,36,37,39,40,41,42,43,46,47,48,49,50,51] : List Nat)[i - 14]! := by
  interval_cases i <;> decide

@[simp] private theorem jump21 :
    Decode.isValidJumpDest submissionBytecode 20 = true :=
  Artifact.isValidJumpDest_index 16 (by rfl)

@[simp] private theorem jump48 :
    Decode.isValidJumpDest submissionBytecode 47 = true :=
  Artifact.isValidJumpDest_index 37 (by rfl)

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
  have hpc : UInt256.ofNat 25 + UInt256.ofNat 3 = UInt256.ofNat 28 := by
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
  have htwentyOne : (20 : UInt256) = UInt256.ofNat 20 := by decide
  have htwentyOneNat : (20 : UInt256).toNat = 20 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (20 : UInt256).toNat = true := by
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
  have hfortyEight : (47 : UInt256) = UInt256.ofNat 47 := by decide
  have hfortyEightNat : (47 : UInt256).toNat = 47 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (47 : UInt256).toNat = true := by
    rw [hfortyEightNat]
    exact jump48
  have hpc : UInt256.ofNat 25 + UInt256.ofNat 3 = UInt256.ofNat 28 := by
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
      71 + MachineState.memCost
        (clearLoop s ptr count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearGuardPath 26 (run_clearGuard s ptr count i returnDest rest
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
    26 45 hguard hbody
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
      count * 71 + MachineState.memCost
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
      41 + MachineState.memCost
        (clearReturned s ptr count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearGuardPath 26 (run_clearFinishGuard s ptr count returnDest rest
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
    26 15 hguard hexit
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
      (44 + count * 71) + MachineState.memCost
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
    3 (count * 71) hsetup' hloop
  have htotal := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).trans
      (gasSteps_clearLoop s ptr count returnDest rest hcap hcount hcode hfork hrun hnp))
    (gasSteps_clearFinish s ptr count returnDest rest hcap hcount hcode hfork
      hrun hnp hvalid) (3 + count * 71) 41 hprefix hfinish
  unfold gasSteps_clear
  simp only [Challenge.EvmProof.GasSteps.trans_cost] at htotal ⊢
  have hactive : (clearEntry s ptr count returnDest rest).activeWords =
      s.activeWords := by rfl
  rw [hactive] at htotal
  omega

/-! ## `copyLimbs` -/

def copySetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 45 .JUMPDEST,
   pushAt 46 0 0]

def copyGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 47 .JUMPDEST,
   opAt 48 (.Dup ⟨3, by decide⟩),
   opAt 49 (.Dup ⟨1, by decide⟩),
   opAt 50 .LT,
   opAt 51 .ISZERO,
   pushAt 52 2 92,
   opAt 53 .JUMPI]

def copyBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 54 (.Dup ⟨0, by decide⟩),
   pushAt 55 1 5,
   opAt 56 .SHL,
   opAt 57 (.Dup ⟨3, by decide⟩),
   opAt 58 .ADD,
   opAt 59 .MLOAD,
   opAt 60 (.Dup ⟨1, by decide⟩),
   pushAt 61 1 5,
   opAt 62 .SHL,
   opAt 63 (.Dup ⟨3, by decide⟩),
   opAt 64 .ADD,
   opAt 65 .MSTORE,
   pushAt 66 1 1,
   opAt 67 (.Dup ⟨1, by decide⟩),
   opAt 68 .ADD,
   opAt 69 (.Swap ⟨0, by decide⟩),
   opAt 70 .POP,
   pushAt 71 2 59,
   opAt 72 .JUMP]

def copyExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 73 .JUMPDEST,
   opAt 74 .POP,
   opAt 75 .POP,
   opAt 76 .POP,
   opAt 77 .POP,
   opAt 78 .JUMP]

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
  { s with pc := UInt256.ofNat 57
           stack := [dst, src, UInt256.ofNat count, returnDest] ++ rest }

def copyLoop (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 59
           stack := [UInt256.ofNat i, dst, src, UInt256.ofNat count,
             returnDest] ++ rest
           memory := copyMemory s.memory dst src i
           activeWords := copyWords s.activeWords dst src i }

def copyBodyEntry (s : State) (dst src : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { copyLoop s dst src count i returnDest rest with pc := UInt256.ofNat 68 }

def copyExit (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { copyLoop s dst src count count returnDest rest with pc := UInt256.ofNat 92 }

def copyReturned (s : State) (dst src : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := rest
           memory := copyMemory s.memory dst src count
           activeWords := copyWords s.activeWords dst src count }

@[simp] private theorem copyPCs (i : Nat)
    (hi : 45 ≤ i) (hii : i ≤ 78) :
    Artifact.submissionArtifact.instructionPC i =
      ([57,58,59,60,61,62,63,64,67,68,69,71,72,73,74,75,76,78,79,80,81,82,84,85,86,87,88,91,92,93,94,95,96,97] : List Nat)[i - 45]! := by
  interval_cases i <;> decide

@[simp] private theorem jump60 :
    Decode.isValidJumpDest submissionBytecode 59 = true :=
  Artifact.isValidJumpDest_index 47 (by rfl)

@[simp] private theorem jump93 :
    Decode.isValidJumpDest submissionBytecode 92 = true :=
  Artifact.isValidJumpDest_index 73 (by rfl)

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
  have hpc : UInt256.ofNat 64 + UInt256.ofNat 3 = UInt256.ofNat 67 := by
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
  have hsixty : (59 : UInt256) = UInt256.ofNat 59 := by decide
  have hsixtyNat : (59 : UInt256).toNat = 59 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (59 : UInt256).toNat = true := by
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
  have hninetyThree : (92 : UInt256) = UInt256.ofNat 92 := by decide
  have hninetyThreeNat : (92 : UInt256).toNat = 92 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (92 : UInt256).toNat = true := by
    rw [hninetyThreeNat]
    exact jump93
  have hpc : UInt256.ofNat 64 + UInt256.ofNat 3 = UInt256.ofNat 67 := by
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
      87 + MachineState.memCost
        (copyLoop s dst src count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyGuardPath 26 (run_copyGuard s dst src count i returnDest rest
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
    26 61 hguard hbody
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
      count * 87 + MachineState.memCost
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
      43 + MachineState.memCost
        (copyReturned s dst src count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    copyGuardPath 26 (run_copyFinishGuard s dst src count returnDest rest
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
    26 17 hguard hexit
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
      (46 + count * 87) + MachineState.memCost
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
    3 (count * 87) hsetup' hloop
  have htotal := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((gasSteps_copySetup s dst src count returnDest rest hcap hcode hfork hrun hnp).trans
      (gasSteps_copyLoop s dst src count returnDest rest hcap hcount hcode hfork hrun hnp))
    (gasSteps_copyFinish s dst src count returnDest rest hcap hcode hfork hrun
      hnp hvalid) (3 + count * 87) 43 hprefix hfinish
  unfold gasSteps_copy
  simp only [Challenge.EvmProof.GasSteps.trans_cost] at htotal ⊢
  have hactive : (copyEntry s dst src count returnDest rest).activeWords =
      s.activeWords := by rfl
  rw [hactive] at htotal
  omega

/-! ## `addMaskedMod`: fixed-width addition phase -/

def addSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 82 .JUMPDEST,
   opAt 83 (.Dup ⟨2, by decide⟩),
   pushAt 84 0 0,
   opAt 85 .SUB,
   pushAt 86 0 0,
   pushAt 87 0 0]

def addGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 88 .JUMPDEST,
   opAt 89 (.Dup ⟨7, by decide⟩),
   opAt 90 (.Dup ⟨1, by decide⟩),
   opAt 91 .LT,
   opAt 92 .ISZERO,
   pushAt 93 2 169,
   opAt 94 .JUMPI]

def addBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 95 (.Dup ⟨0, by decide⟩),
   pushAt 96 1 5,
   opAt 97 .SHL,
   opAt 98 (.Dup ⟨0, by decide⟩),
   opAt 99 (.Dup ⟨5, by decide⟩),
   opAt 100 .ADD,
   opAt 101 .MLOAD,
   opAt 102 (.Dup ⟨4, by decide⟩),
   opAt 103 (.Dup ⟨2, by decide⟩),
   opAt 104 (.Dup ⟨8, by decide⟩),
   opAt 105 .ADD,
   opAt 106 .MLOAD,
   opAt 107 .AND,
   opAt 108 (.Dup ⟨1, by decide⟩),
   opAt 109 .ADD,
   opAt 110 (.Dup ⟨1, by decide⟩),
   opAt 111 (.Dup ⟨1, by decide⟩),
   opAt 112 .LT,
   opAt 113 (.Dup ⟨5, by decide⟩),
   opAt 114 (.Dup ⟨2, by decide⟩),
   opAt 115 .ADD,
   opAt 116 (.Dup ⟨2, by decide⟩),
   opAt 117 (.Dup ⟨1, by decide⟩),
   opAt 118 .LT,
   opAt 119 (.Dup ⟨1, by decide⟩),
   opAt 120 (.Dup ⟨6, by decide⟩),
   opAt 121 (.Dup ⟨11, by decide⟩),
   opAt 122 .ADD,
   opAt 123 .MSTORE,
   opAt 124 (.Dup ⟨0, by decide⟩),
   opAt 125 (.Dup ⟨3, by decide⟩),
   opAt 126 .OR,
   opAt 127 (.Swap ⟨7, by decide⟩),
   opAt 128 .POP,
   opAt 129 .POP,
   opAt 130 .POP,
   opAt 131 .POP,
   opAt 132 .POP,
   opAt 133 .POP,
   opAt 134 .POP,
   pushAt 135 1 1,
   opAt 136 (.Dup ⟨1, by decide⟩),
   opAt 137 .ADD,
   opAt 138 (.Swap ⟨0, by decide⟩),
   opAt 139 .POP,
   pushAt 140 2 109,
   opAt 141 .JUMP]

def addToSubtractPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 142 .JUMPDEST,
   opAt 143 .POP,
   pushAt 144 0 0,
   pushAt 145 0 0]

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

def addEntry (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 103
           stack := [dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def addLoop (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let progress := addProgress s.memory s.activeWords dst src mask i
  { s with pc := UInt256.ofNat 109
           stack := [UInt256.ofNat i, progress.carry, mask, dst, src, take,
             modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def addBodyEntry (s : State) (dst src take modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { addLoop s dst src take modulus count i returnDest rest with
      pc := UInt256.ofNat 118 }

def subtractLoopEntry (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let progress := addProgress s.memory s.activeWords dst src mask count
  { s with pc := UInt256.ofNat 173
           stack := [0, 0, progress.carry, mask, dst, src, take, modulus,
             UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

@[simp] private theorem addPCs (i : Nat)
    (hi : 82 ≤ i) (hii : i ≤ 145) :
    Artifact.submissionArtifact.instructionPC i =
      ([103,104,105,106,107,108,109,110,111,112,113,114,117,118,119,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,161,162,163,164,165,168,169,170,171,172] : List Nat)[i - 82]! := by
  interval_cases i <;> decide

@[simp] private theorem jump110 :
    Decode.isValidJumpDest submissionBytecode 109 = true :=
  Artifact.isValidJumpDest_index 88 (by rfl)

@[simp] private theorem jump170 :
    Decode.isValidJumpDest submissionBytecode 169 = true :=
  Artifact.isValidJumpDest_index 142 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_addSetup (s : State) (dst src take modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addSetupPath
      (addEntry s dst src take modulus count returnDest rest) =
        some (addLoop s dst src take modulus count 0 returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [addSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addEntry, addLoop, addProgress, addPCs, hc6, hc7, hc8, hc9, hrun, hzero,
    hzero',
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_addGuard (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addGuardPath
      (addLoop s dst src take modulus count i returnDest rest) =
        some (addBodyEntry s dst src take modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 114 + UInt256.ofNat 3 = UInt256.ofNat 117 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [addGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addLoop, addBodyEntry, addPCs, hc9, hc10, hc11, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

set_option linter.unusedSimpArgs false in
theorem run_addBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addBodyPath
      (addBodyEntry s dst src take modulus count i returnDest rest) =
        some (addLoop s dst src take modulus count (i + 1) returnDest rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have honeTen : (109 : UInt256) = UInt256.ofNat 109 := by decide
  have honeTenNat : (109 : UInt256).toNat = 109 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (109 : UInt256).toNat = true := by
    rw [honeTenNat]
    exact jump110
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  simp (config := { maxSteps := 800000 })
    [addBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      addBodyEntry, addLoop, addProgress,
      addPCs, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18,
      hcode, hrun, hone, hfive, hinc, honeTen, honeTenNat, hjump, jump110,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_addFinishGuard (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addGuardPath
      (addLoop s dst src take modulus count count returnDest rest) =
        some { addLoop s dst src take modulus count count returnDest rest with
          pc := UInt256.ofNat 169 } := by
  have hzeroFalse : ¬(0 : UInt256).isZero.toNat = 0 := by decide
  have hzeroOfNatFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (169 : UInt256) = UInt256.ofNat 169 := by decide
  have hdestNat : (169 : UInt256).toNat = 169 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (169 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump170
  have hpc : UInt256.ofNat 114 + UInt256.ofNat 3 = UInt256.ofNat 117 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [addGuardPath, opAt, pushAt, wfOp, addLoop, addPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc9, hc10, hc11, hcode, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hzeroOfNatFalse, hdest, hdestNat, hjump, jump170, hpc]

set_option linter.unusedSimpArgs false in
theorem run_addToSubtract (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addToSubtractPath
      { addLoop s dst src take modulus count count returnDest rest with
        pc := UInt256.ofNat 169 } =
      some (subtractLoopEntry s dst src take modulus count returnDest rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [addToSubtractPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addLoop, subtractLoopEntry, addPCs, hc8, hc9, hc10, hrun, hzero, hzero',
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

/-! ### Wrapped subtraction phase -/

def subtractGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 146 .JUMPDEST,
   opAt 147 (.Dup ⟨8, by decide⟩),
   opAt 148 (.Dup ⟨1, by decide⟩),
   opAt 149 .LT,
   opAt 150 .ISZERO,
   pushAt 151 2 235,
   opAt 152 .JUMPI]

def subtractBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 153 (.Dup ⟨0, by decide⟩),
   pushAt 154 1 5,
   opAt 155 .SHL,
   opAt 156 (.Dup ⟨0, by decide⟩),
   opAt 157 (.Dup ⟨6, by decide⟩),
   opAt 158 .ADD,
   opAt 159 .MLOAD,
   opAt 160 (.Dup ⟨1, by decide⟩),
   opAt 161 (.Dup ⟨10, by decide⟩),
   opAt 162 .ADD,
   opAt 163 .MLOAD,
   opAt 164 (.Dup ⟨0, by decide⟩),
   opAt 165 (.Dup ⟨2, by decide⟩),
   opAt 166 .SUB,
   opAt 167 (.Dup ⟨1, by decide⟩),
   opAt 168 (.Dup ⟨3, by decide⟩),
   opAt 169 .LT,
   opAt 170 (.Dup ⟨6, by decide⟩),
   opAt 171 (.Dup ⟨2, by decide⟩),
   opAt 172 .SUB,
   opAt 173 (.Dup ⟨7, by decide⟩),
   opAt 174 (.Dup ⟨3, by decide⟩),
   opAt 175 .LT,
   opAt 176 (.Dup ⟨1, by decide⟩),
   opAt 177 (.Dup ⟨7, by decide⟩),
   pushAt 178 2 5120,
   opAt 179 .ADD,
   opAt 180 .MSTORE,
   opAt 181 (.Dup ⟨0, by decide⟩),
   opAt 182 (.Dup ⟨3, by decide⟩),
   opAt 183 .OR,
   opAt 184 (.Swap ⟨8, by decide⟩),
   opAt 185 .POP,
   opAt 186 .POP,
   opAt 187 .POP,
   opAt 188 .POP,
   opAt 189 .POP,
   opAt 190 .POP,
   opAt 191 .POP,
   opAt 192 .POP,
   pushAt 193 1 1,
   opAt 194 (.Dup ⟨1, by decide⟩),
   opAt 195 .ADD,
   opAt 196 (.Swap ⟨0, by decide⟩),
   opAt 197 .POP,
   pushAt 198 2 173,
   opAt 199 .JUMP]

def subtractToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 200 .JUMPDEST,
   opAt 201 .POP,
   opAt 202 (.Dup ⟨0, by decide⟩),
   opAt 203 .ISZERO,
   opAt 204 (.Dup ⟨2, by decide⟩),
   opAt 205 .OR,
   pushAt 206 0 0,
   opAt 207 .SUB,
   pushAt 208 0 0]

structure SubtractProgress where
  memory : ByteArray
  activeWords : UInt256
  borrow : UInt256

def subtractProgress (memory : ByteArray) (activeWords dst modulus : UInt256) :
    Nat → SubtractProgress
  | 0 => ⟨memory, activeWords, 0⟩
  | i + 1 =>
      let before := subtractProgress memory activeWords dst modulus i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let dstAt := dst + off
      let modulusAt := modulus + off
      let candidateAt := UInt256.ofNat 5120 + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let y := MachineState.readWord before.memory modulusAt.toNat
      let difference := x - y
      let z := difference - before.borrow
      let borrow := UInt256.lor (UInt256.lt x y)
        (UInt256.lt difference before.borrow)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat modulusAt.toNat 32)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat candidateAt.toNat 32)
      ⟨MachineState.writeBytes before.memory
          (Data.Bytes.natToBytesPadded z.toNat 32) candidateAt.toNat,
        stored, borrow⟩

/-- Candidate writes preserve an input region that is disjoint from the fixed
`0x1400` candidate buffer. -/
theorem readWord_subtractProgress_input (memory : ByteArray)
    (activeWords dst modulus : UInt256) (ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdisjoint : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr) :
    MachineState.readWord
        (subtractProgress memory activeWords dst modulus iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [subtractProgress,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat 5120 iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · left; omega
        · right; omega

theorem memoryLimbs_subtractProgress_input (memory : ByteArray)
    (activeWords dst modulus : UInt256) (ptr count iter : Nat)
    (hiter : iter ≤ count)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdisjoint : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr) :
    Limbs.memoryLimbs
        (subtractProgress memory activeWords dst modulus iter).memory ptr count =
      Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [readWord_subtractProgress_input memory activeWords dst modulus ptr count
    iter j hiter (by simpa using hj) hcandidateFit hdisjoint]

theorem represents_subtractProgress_input (memory : ByteArray)
    (activeWords dst modulus : UInt256) (ptr count iter value : Nat)
    (hiter : iter ≤ count)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdisjoint : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (subtractProgress memory activeWords dst modulus iter).memory
      ptr count value := by
  exact ⟨hrep.1, (memoryLimbs_subtractProgress_input memory activeWords dst
    modulus ptr count iter hiter hcandidateFit hdisjoint).trans hrep.2⟩

structure SubtractNatProgress where
  digits : List Nat
  borrow : Nat

/-- Mathematical subtraction prefix driven by the unchanged input regions. -/
def subtractNatProgress (memory : ByteArray) (dst modulus : Nat) :
    Nat → SubtractNatProgress
  | 0 => ⟨[], 0⟩
  | i + 1 =>
      let before := subtractNatProgress memory dst modulus i
      let x := (MachineState.readWord memory (dst + 32 * i)).toNat
      let y := (MachineState.readWord memory (modulus + 32 * i)).toNat
      let nextBorrow := if x < y + before.borrow then 1 else 0
      ⟨before.digits ++
          [x + Limbs.radix * nextBorrow - y - before.borrow], nextBorrow⟩

theorem subtractNatProgress_eq_subDigitLists (memory : ByteArray)
    (dst modulus count : Nat) :
    let natural := subtractNatProgress memory dst modulus count
    let result := Limbs.subDigitLists
      (Limbs.memoryLimbs memory dst count)
      (Limbs.memoryLimbs memory modulus count) 0
    natural.digits = result.1 ∧ natural.borrow = result.2 := by
  induction count with
  | zero =>
      simp [subtractNatProgress, Limbs.memoryLimbs, Limbs.subDigitLists]
  | succ count ih =>
      rw [subtractNatProgress, memoryLimbs_succ, memoryLimbs_succ,
        Limbs.subDigitLists_append_single (by simp [Limbs.memoryLimbs])]
      rcases ih with ⟨hdigits, hborrow⟩
      simp only
      rw [hdigits, hborrow]
      exact ⟨rfl, rfl⟩

theorem subtractProgress_matches_nat (memory : ByteArray)
    (activeWords : UInt256) (dst modulus count iter : Nat)
    (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstDisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusDisjoint : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus) :
    let progress := subtractProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) iter
    let natural := subtractNatProgress memory dst modulus iter
    Limbs.memoryLimbs progress.memory 5120 iter = natural.digits ∧
      progress.borrow.toNat = natural.borrow ∧ natural.borrow ≤ 1 := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [subtractProgress, subtractNatProgress, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hi : iter < count := by omega
      have hprefix := ih (by omega)
      let before := subtractProgress memory activeWords (UInt256.ofNat dst)
        (UInt256.ofNat modulus) iter
      let naturalBefore := subtractNatProgress memory dst modulus iter
      have hbeforeMemory :
          Limbs.memoryLimbs before.memory 5120 iter = naturalBefore.digits :=
        hprefix.1
      have hbeforeBorrow : before.borrow.toNat = naturalBefore.borrow :=
        hprefix.2.1
      have hbeforeBorrowLe : naturalBefore.borrow ≤ 1 := hprefix.2.2
      let x := MachineState.readWord before.memory (dst + 32 * iter)
      let y := MachineState.readWord before.memory (modulus + 32 * iter)
      have hx : x = MachineState.readWord memory (dst + 32 * iter) := by
        exact readWord_subtractProgress_input memory activeWords
          (UInt256.ofNat dst) (UInt256.ofNat modulus) dst count iter iter
          (by omega) hi hcandidateFit hdstDisjoint
      have hy : y = MachineState.readWord memory (modulus + 32 * iter) := by
        exact readWord_subtractProgress_input memory activeWords
          (UInt256.ofNat dst) (UInt256.ofNat modulus) modulus count iter iter
          (by omega) hi hcandidateFit hmodulusDisjoint
      have hstep := subLimbStep_toNat x y before.borrow (by
        rw [hbeforeBorrow]
        exact hbeforeBorrowLe)
      have hoffDst :
          (UInt256.ofNat dst + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = dst + 32 * iter :=
        addOffset_toNat dst iter (by omega)
      have hoffModulus :
          (UInt256.ofNat modulus + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = modulus + 32 * iter :=
        addOffset_toNat modulus iter (by omega)
      have hoffCandidate :
          (UInt256.ofNat 5120 + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = 5120 + 32 * iter :=
        addOffset_toNat 5120 iter (by omega)
      dsimp only [subtractProgress, subtractNatProgress]
      rw [hoffDst, hoffModulus, hoffCandidate, memoryLimbs_write_next]
      constructor
      · rw [hbeforeMemory]
        congr 2
        simpa [x, y, before, naturalBefore, hx, hy, hbeforeBorrow]
          using hstep.1
      · constructor
        · simpa [x, y, before, naturalBefore, hx, hy, hbeforeBorrow]
            using hstep.2
        · split <;> omega

theorem subtractProgress_value_borrow (memory : ByteArray)
    (activeWords : UInt256) (dst modulus count wrapped modulusValue : Nat)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstDisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusDisjoint : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus)
    (hdst : Limbs.Represents memory dst count wrapped)
    (hmodulus : Limbs.Represents memory modulus count modulusValue) :
    let progress := subtractProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) count
    Nat.ofDigits Limbs.radix
        (Limbs.memoryLimbs progress.memory 5120 count) + modulusValue =
      wrapped + Limbs.radix ^ count * progress.borrow.toNat ∧
      progress.borrow.toNat ≤ 1 := by
  let progress := subtractProgress memory activeWords (UInt256.ofNat dst)
    (UInt256.ofNat modulus) count
  let natural := subtractNatProgress memory dst modulus count
  let result := Limbs.subDigitLists
    (Limbs.memoryLimbs memory dst count)
    (Limbs.memoryLimbs memory modulus count) 0
  have hmatch := subtractProgress_matches_nat memory activeWords dst modulus
    count count (by omega) hdstFit hmodulusFit hcandidateFit hdstDisjoint
    hmodulusDisjoint
  have hcanonical := subtractNatProgress_eq_subDigitLists memory dst modulus count
  have hvalue := Limbs.subDigitLists_value (borrow := 0)
    (xs := Limbs.memoryLimbs memory dst count)
    (ys := Limbs.memoryLimbs memory modulus count) (by simp)
    (fun digit hdigit => Limbs.memoryLimb_lt memory dst count hdigit)
    (fun digit hdigit => Limbs.memoryLimb_lt memory modulus count hdigit)
    (by omega)
  rw [Nat.add_zero, Limbs.value_of_represents hdst,
    Limbs.value_of_represents hmodulus] at hvalue
  dsimp only [progress, natural, result] at hmatch hcanonical ⊢
  rw [hmatch.1, hcanonical.1, hmatch.2.1, hcanonical.2]
  constructor
  · simpa using hvalue
  · simpa [← hcanonical.2] using hmatch.2.2

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

def subtractLoop (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let added := addProgress s.memory s.activeWords dst src mask count
  let progress := subtractProgress added.memory added.activeWords dst modulus i
  { s with pc := UInt256.ofNat 173
           stack := [UInt256.ofNat i, progress.borrow, added.carry, mask, dst,
             src, take, modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def subtractBodyEntry (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { subtractLoop s dst src take modulus count i returnDest rest with
      pc := UInt256.ofNat 182 }

def selectLoopEntry (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let added := addProgress s.memory s.activeWords dst src mask count
  let subtracted := subtractProgress added.memory added.activeWords dst modulus count
  let useSub := UInt256.lor added.carry (UInt256.isZero subtracted.borrow)
  { s with pc := UInt256.ofNat 244
           stack := [0, 0 - useSub, subtracted.borrow, added.carry, mask, dst,
             src, take, modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := subtracted.memory
           activeWords := subtracted.activeWords }

@[simp] private theorem subtractPCs (i : Nat)
    (hi : 146 ≤ i) (hii : i ≤ 208) :
    Artifact.submissionArtifact.instructionPC i =
      ([173,174,175,176,177,178,181,182,183,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,227,228,229,230,231,234,235,236,237,238,239,240,241,242,243] : List Nat)[i - 146]! := by
  interval_cases i <;> decide

@[simp] private theorem jump174 :
    Decode.isValidJumpDest submissionBytecode 173 = true :=
  Artifact.isValidJumpDest_index 146 (by rfl)

@[simp] private theorem jump236 :
  Decode.isValidJumpDest submissionBytecode 235 = true :=
  Artifact.isValidJumpDest_index 200 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_subtractGuard (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractGuardPath
      (subtractLoop s dst src take modulus count i returnDest rest) =
        some (subtractBodyEntry s dst src take modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 178 + UInt256.ofNat 3 = UInt256.ofNat 181 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [subtractGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    subtractLoop, subtractBodyEntry, subtractPCs, hc10, hc11, hc12, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

set_option linter.unusedSimpArgs false in
theorem run_subtractBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractBodyPath
      (subtractBodyEntry s dst src take modulus count i returnDest rest) =
        some (subtractLoop s dst src take modulus count (i + 1)
          returnDest rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hloop : (173 : UInt256) = UInt256.ofNat 173 := by decide
  have hloopNat : (173 : UInt256).toNat = 173 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (173 : UInt256).toNat = true := by
    rw [hloopNat]
    exact jump174
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  simp (config := { maxSteps := 1000000 })
    [subtractBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      subtractBodyEntry, subtractLoop, subtractProgress,
      subtractPCs, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18,
      hc19, hc20, hcode, hrun, hone, hfive, hfiveK, hinc, hloop, hloopNat,
      hjump, jump174, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_subtractFinishGuard (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractGuardPath
      (subtractLoop s dst src take modulus count count returnDest rest) =
        some { subtractLoop s dst src take modulus count count returnDest rest with
          pc := UInt256.ofNat 235 } := by
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (235 : UInt256) = UInt256.ofNat 235 := by decide
  have hdestNat : (235 : UInt256).toNat = 235 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (235 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump236
  have hpc : UInt256.ofNat 178 + UInt256.ofNat 3 = UInt256.ofNat 181 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [subtractGuardPath, opAt, pushAt, wfOp, subtractLoop, subtractPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, hcode, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hdest, hdestNat, hjump, jump236, hpc]

set_option linter.unusedSimpArgs false in
theorem run_subtractToSelect (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractToSelectPath
      { subtractLoop s dst src take modulus count count returnDest rest with
        pc := UInt256.ofNat 235 } =
      some (selectLoopEntry s dst src take modulus count returnDest rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [subtractToSelectPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    subtractLoop, selectLoopEntry, subtractPCs, hc9, hc10, hc11, hc12,
    hrun, hzero, hzero', Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

/-! ### Branchless selection phase -/

def selectGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 209 .JUMPDEST,
   opAt 210 (.Dup ⟨9, by decide⟩),
   opAt 211 (.Dup ⟨1, by decide⟩),
   opAt 212 .LT,
   opAt 213 .ISZERO,
   pushAt 214 2 292,
   opAt 215 .JUMPI]

def selectBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 216 (.Dup ⟨0, by decide⟩),
   pushAt 217 1 5,
   opAt 218 .SHL,
   opAt 219 (.Dup ⟨0, by decide⟩),
   opAt 220 (.Dup ⟨7, by decide⟩),
   opAt 221 .ADD,
   opAt 222 .MLOAD,
   opAt 223 (.Dup ⟨1, by decide⟩),
   pushAt 224 2 5120,
   opAt 225 .ADD,
   opAt 226 .MLOAD,
   opAt 227 (.Dup ⟨4, by decide⟩),
   opAt 228 .NOT,
   opAt 229 (.Dup ⟨2, by decide⟩),
   opAt 230 .AND,
   opAt 231 (.Dup ⟨5, by decide⟩),
   opAt 232 (.Dup ⟨2, by decide⟩),
   opAt 233 .AND,
   opAt 234 .OR,
   opAt 235 (.Dup ⟨3, by decide⟩),
   opAt 236 (.Dup ⟨10, by decide⟩),
   opAt 237 .ADD,
   opAt 238 .MSTORE,
   opAt 239 .POP,
   opAt 240 .POP,
   opAt 241 .POP,
   pushAt 242 1 1,
   opAt 243 (.Dup ⟨1, by decide⟩),
   opAt 244 .ADD,
   opAt 245 (.Swap ⟨0, by decide⟩),
   opAt 246 .POP,
   pushAt 247 2 244,
   opAt 248 .JUMP]

def selectExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 249 .JUMPDEST,
   opAt 250 .POP,
   opAt 251 .POP,
   opAt 252 .POP,
   opAt 253 .POP,
   opAt 254 .POP,
   opAt 255 .POP,
   opAt 256 .POP,
   opAt 257 .POP,
   opAt 258 .POP,
   opAt 259 .POP,
   opAt 260 .JUMP]

structure SelectProgress where
  memory : ByteArray
  activeWords : UInt256

def selectProgress (memory : ByteArray) (activeWords dst selectMask : UInt256) :
    Nat → SelectProgress
  | 0 => ⟨memory, activeWords⟩
  | i + 1 =>
      let before := selectProgress memory activeWords dst selectMask i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let dstAt := dst + off
      let candidateAt := UInt256.ofNat 5120 + off
      let sum := MachineState.readWord before.memory dstAt.toNat
      let reduced := MachineState.readWord before.memory candidateAt.toNat
      let selected := UInt256.lor (UInt256.land reduced selectMask)
        (UInt256.land sum (UInt256.lnot selectMask))
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let loadedCandidate := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat candidateAt.toNat 32)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedCandidate.toNat dstAt.toNat 32)
      ⟨MachineState.writeBytes before.memory
          (Data.Bytes.natToBytesPadded selected.toNat 32) dstAt.toNat, stored⟩

theorem selectWord_toNat (sum reduced useSub : UInt256)
    (huseSub : useSub.toNat ≤ 1) :
    (UInt256.lor (UInt256.land reduced (0 - useSub))
      (UInt256.land sum (UInt256.lnot (0 - useSub)))).toNat =
        if useSub.toNat = 1 then reduced.toNat else sum.toNat := by
  interval_cases huse : useSub.toNat
  · have hword : useSub = UInt256.ofNat 0 := by
      rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat useSub, huse]
    rw [hword]
    have hnot : UInt256.lnot (0 - UInt256.ofNat 0) =
        0 - UInt256.ofNat 1 := by decide
    rw [Challenge.EvmProof.Word.word_toNat_lor,
      land_sub_zero_take_toNat reduced (by omega), hnot,
      land_sub_zero_take_toNat sum (by omega)]
    norm_num
  · have hword : useSub = UInt256.ofNat 1 := by
      rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat useSub, huse]
    rw [hword]
    have hnot : UInt256.lnot (0 - UInt256.ofNat 1) =
        0 - UInt256.ofNat 0 := by decide
    rw [Challenge.EvmProof.Word.word_toNat_lor,
      land_sub_zero_take_toNat reduced (by omega), hnot,
      land_sub_zero_take_toNat sum (by omega)]
    norm_num

theorem readWord_selectProgress_future_dst (memory : ByteArray)
    (activeWords mask : UInt256) (dst iter j : Nat)
    (hiter : iter ≤ j) (hfit : dst + 32 * (j + 1) < 2 ^ 256) :
    MachineState.readWord
        (selectProgress memory activeWords (UInt256.ofNat dst) mask iter).memory
        (dst + 32 * j) =
      MachineState.readWord memory (dst + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [selectProgress,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        right
        omega

theorem readWord_selectProgress_candidate (memory : ByteArray)
    (activeWords mask : UInt256) (dst count iter j : Nat)
    (hiter : iter ≤ j) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst) :
    MachineState.readWord
        (selectProgress memory activeWords (UInt256.ofNat dst) mask iter).memory
        (5120 + 32 * j) =
      MachineState.readWord memory (5120 + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [selectProgress,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem readWord_selectProgress_disjoint_region (memory : ByteArray)
    (activeWords mask : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst) :
    MachineState.readWord
        (selectProgress memory activeWords (UInt256.ofNat dst) mask iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [selectProgress,
        Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, addOffset_toNat dst iter (by omega)]
        rcases hdisjoint with hbefore | hafter
        · right; omega
        · left; omega

theorem represents_selectProgress_disjoint_region (memory : ByteArray)
    (activeWords mask : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count) (hdstFit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ ptr ∨
      ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (selectProgress memory activeWords (UInt256.ofNat dst) mask iter).memory
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  unfold Limbs.memoryLimbs
  rw [← hrep.2]
  apply List.map_congr_left
  intro j hj
  rw [readWord_selectProgress_disjoint_region memory activeWords mask dst ptr
    count iter j hiter (by simpa using hj) hdstFit hdisjoint]

theorem selectProgress_memoryLimbs (memory : ByteArray)
    (activeWords : UInt256) (dst count iter : Nat) (useSub : UInt256)
    (hiter : iter ≤ count) (huseSub : useSub.toNat ≤ 1)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst) :
    Limbs.memoryLimbs
        (selectProgress memory activeWords (UInt256.ofNat dst)
          (0 - useSub) iter).memory dst iter =
      if useSub.toNat = 1 then Limbs.memoryLimbs memory 5120 iter
      else Limbs.memoryLimbs memory dst iter := by
  induction iter with
  | zero => simp [selectProgress, Limbs.memoryLimbs]
  | succ iter ih =>
      have hi : iter < count := by omega
      let before := selectProgress memory activeWords (UInt256.ofNat dst)
        (0 - useSub) iter
      let sum := MachineState.readWord before.memory (dst + 32 * iter)
      let reduced := MachineState.readWord before.memory (5120 + 32 * iter)
      have hsum : sum = MachineState.readWord memory (dst + 32 * iter) := by
        exact readWord_selectProgress_future_dst memory activeWords
          (0 - useSub) dst iter iter (by omega) (by omega)
      have hreduced : reduced =
          MachineState.readWord memory (5120 + 32 * iter) := by
        exact readWord_selectProgress_candidate memory activeWords
          (0 - useSub) dst count iter iter (by omega) hi hdstFit hdisjoint
      have hselected := selectWord_toNat sum reduced useSub huseSub
      have hoffDst :
          (UInt256.ofNat dst + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = dst + 32 * iter :=
        addOffset_toNat dst iter (by omega)
      have hoffCandidate :
          (UInt256.ofNat 5120 + UInt256.shiftLeft (UInt256.ofNat iter)
            (UInt256.ofNat 5)).toNat = 5120 + 32 * iter :=
        addOffset_toNat 5120 iter (by omega)
      dsimp only [selectProgress]
      rw [hoffDst, hoffCandidate, memoryLimbs_write_next,
        memoryLimbs_succ, memoryLimbs_succ, ih (by omega)]
      split <;> simp_all [sum, reduced, before]

theorem selectProgress_represents (memory : ByteArray)
    (activeWords : UInt256) (dst count sum reduced chosen : Nat)
    (useSub : UInt256) (huseSub : useSub.toNat ≤ 1)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hdisjoint : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hsum : Limbs.Represents memory dst count sum)
    (hreduced : Limbs.Represents memory 5120 count reduced)
    (hchosen : chosen = if useSub.toNat = 1 then reduced else sum)
    (hchosenFit : chosen < Limbs.radix ^ count) :
    Limbs.Represents
      (selectProgress memory activeWords (UInt256.ofNat dst)
        (0 - useSub) count).memory dst count chosen := by
  rw [Limbs.represents_iff_value hchosenFit,
    selectProgress_memoryLimbs memory activeWords dst count count useSub
      (by omega) huseSub hdstFit hdisjoint, hchosen]
  by_cases hselect : useSub.toNat = 1
  · simpa [hselect] using Limbs.value_of_represents hreduced
  · simpa [hselect] using Limbs.value_of_represents hsum

def selectLoop (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let added := addProgress s.memory s.activeWords dst src mask count
  let subtracted := subtractProgress added.memory added.activeWords dst modulus count
  let useSub := UInt256.lor added.carry (UInt256.isZero subtracted.borrow)
  let selectMask := 0 - useSub
  let progress := selectProgress subtracted.memory subtracted.activeWords dst
    selectMask i
  { s with pc := UInt256.ofNat 244
           stack := [UInt256.ofNat i, selectMask, subtracted.borrow,
             added.carry, mask, dst, src, take, modulus, UInt256.ofNat count,
             returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def selectBodyEntry (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { selectLoop s dst src take modulus count i returnDest rest with
      pc := UInt256.ofNat 253 }

def selectExit (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { selectLoop s dst src take modulus count count returnDest rest with
      pc := UInt256.ofNat 292 }

def addReturned (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask := 0 - take
  let added := addProgress s.memory s.activeWords dst src mask count
  let subtracted := subtractProgress added.memory added.activeWords dst modulus count
  let useSub := UInt256.lor added.carry (UInt256.isZero subtracted.borrow)
  let progress := selectProgress subtracted.memory subtracted.activeWords dst
    (0 - useSub) count
  { s with pc := returnDest
           stack := rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-! ### Functional contract for `addMaskedMod` -/

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
  let total := x + take * y
  let bound := Limbs.radix ^ count
  let added := addProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat src) (0 - UInt256.ofNat take) count
  let wrapped := total % bound
  have htotalLt : total < 2 * modulusValue := by
    exact Limbs.masked_sum_lt_twice_of_le hx hy htake
  have hwrappedLt : wrapped < bound := by
    exact Nat.mod_lt _ (pow_pos Limbs.radix_pos _)
  have hadded : Limbs.Represents added.memory dst count wrapped := by
    exact addProgress_represents_wrapped s.memory s.activeWords dst src count
      take x y htake hdstFit hsrcFit halias hdst hsrc
  have haddValue :
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs added.memory dst count) +
          bound * added.carry.toNat = total ∧ added.carry.toNat ≤ 1 := by
    simpa [added, wrapped, total, bound] using
      addProgress_value_carry s.memory s.activeWords dst src count take x y
        htake hdstFit hsrcFit halias hdst hsrc
  have haddedModulus :
      Limbs.Represents added.memory modulus count modulusValue := by
    exact represents_addProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat src) (0 - UInt256.ofNat take) dst modulus count count
      modulusValue
      (by omega) hdstFit hdstModulus hmodulus
  let subtracted := subtractProgress added.memory added.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  let candidate := Nat.ofDigits Limbs.radix
    (Limbs.memoryLimbs subtracted.memory 5120 count)
  have hsubValue : candidate + modulusValue =
        wrapped + bound * subtracted.borrow.toNat ∧
      subtracted.borrow.toNat ≤ 1 := by
    simpa [subtracted, candidate, wrapped, bound] using
      subtractProgress_value_borrow added.memory added.activeWords dst modulus
        count wrapped modulusValue hdstFit hmodulusFit hcandidateFit
        hdstCandidate hmodulusCandidate hadded haddedModulus
  have hcandidateLt : candidate < bound := by
    exact memoryLimbs_value_lt subtracted.memory 5120 count
  have hsubtractedDst :
      Limbs.Represents subtracted.memory dst count wrapped := by
    exact represents_subtractProgress_input added.memory added.activeWords
      (UInt256.ofNat dst) (UInt256.ofNat modulus) dst count count wrapped
      (by omega) hcandidateFit hdstCandidate hadded
  have hsubtractedCandidate :
      Limbs.Represents subtracted.memory 5120 count candidate := by
    exact represents_memoryLimbs_value subtracted.memory 5120 count
  have hcarryIff : added.carry.toNat = 1 ↔ bound ≤ total := by
    apply carry_eq_one_iff hwrappedLt haddValue.2
    simpa [Limbs.value_of_represents hadded] using haddValue.1
  have hborrowIff : subtracted.borrow.toNat = 0 ↔
      modulusValue ≤ wrapped :=
    borrow_eq_zero_iff hcandidateLt hmodulusBound hsubValue.2 hsubValue.1
  let useSub := UInt256.lor added.carry
    (UInt256.isZero subtracted.borrow)
  have huseSubLe : useSub.toNat ≤ 1 := by
    exact useSub_toNat_le_one added.carry subtracted.borrow haddValue.2
      hsubValue.2
  have huseSubIff : useSub.toNat = 1 ↔ modulusValue ≤ total := by
    exact useSub_eq_one_iff added.carry subtracted.borrow hmodulusBound rfl
      haddValue.2 hsubValue.2 hcarryIff hborrowIff
  have hchosen :
      (if useSub.toNat = 1 then candidate else wrapped) =
        total % modulusValue := by
    rw [Limbs.mod_eq_cond_sub htotalLt]
    by_cases hlt : total < modulusValue
    · rw [if_pos hlt,
        if_neg (fun h => (Nat.not_le_of_lt hlt) (huseSubIff.mp h))]
      exact Nat.mod_eq_of_lt (by simpa [wrapped, bound, total] using
        (show total < bound from hlt.trans hmodulusBound))
    · have hge : modulusValue ≤ total := Nat.le_of_not_gt hlt
      rw [if_neg hlt, if_pos (huseSubIff.mpr hge)]
      let carryNat := added.carry.toNat
      let borrowNat := subtracted.borrow.toNat
      have hcarryNat : carryNat ≤ 1 := haddValue.2
      have hborrowNat : borrowNat ≤ 1 := hsubValue.2
      have haddEq : wrapped + bound * carryNat = total := by
        simpa [carryNat, Limbs.value_of_represents hadded] using haddValue.1
      have hsubEq : candidate + modulusValue =
          wrapped + bound * borrowNat := by
        simpa [borrowNat] using hsubValue.1
      have hcarryIff' : carryNat = 1 ↔ bound ≤ total := by
        simpa [carryNat] using hcarryIff
      have hborrowIff' : borrowNat = 0 ↔ modulusValue ≤ wrapped := by
        simpa [borrowNat] using hborrowIff
      interval_cases carryNat <;> interval_cases borrowNat <;>
        omega
  have hresultFit : total % modulusValue < bound :=
    (Nat.mod_lt total (by omega)).trans hmodulusBound
  have hselected := selectProgress_represents subtracted.memory
    subtracted.activeWords dst count wrapped candidate (total % modulusValue)
    useSub huseSubLe hdstFit hdstCandidate hsubtractedDst
    hsubtractedCandidate hchosen.symm hresultFit
  simpa [addReturned, added, subtracted, useSub] using hselected

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
  let added := addProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat src) (0 - UInt256.ofNat take) count
  have hadded : Limbs.Represents added.memory ptr count value := by
    exact represents_addProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat src) (0 - UInt256.ofNat take) dst ptr count count value
      (by omega) hdstFit hptrDst hrep
  let subtracted := subtractProgress added.memory added.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  have hsubtracted : Limbs.Represents subtracted.memory ptr count value := by
    exact represents_subtractProgress_input added.memory added.activeWords
      (UInt256.ofNat dst) (UInt256.ofNat modulus) ptr count count value
      (by omega) hcandidateFit hptrCandidate hadded
  let useSub := UInt256.lor added.carry (UInt256.isZero subtracted.borrow)
  exact represents_selectProgress_disjoint_region subtracted.memory
    subtracted.activeWords (0 - useSub) dst ptr count count value (by omega)
    hdstFit hptrDst hsubtracted

@[simp] private theorem selectPCs (i : Nat)
    (hi : 209 ≤ i) (hii : i ≤ 260) :
    Artifact.submissionArtifact.instructionPC i =
      ([244,245,246,247,248,249,252,253,254,256,257,258,259,260,261,262,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,284,285,286,287,288,291,292,293,294,295,296,297,298,299,300,301,302,303] : List Nat)[i - 209]! := by
  interval_cases i <;> decide

@[simp] private theorem jump245 :
    Decode.isValidJumpDest submissionBytecode 244 = true :=
  Artifact.isValidJumpDest_index 209 (by rfl)

@[simp] private theorem jump293 :
    Decode.isValidJumpDest submissionBytecode 292 = true :=
  Artifact.isValidJumpDest_index 249 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_selectGuard (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (selectLoop s dst src take modulus count i returnDest rest) =
        some (selectBodyEntry s dst src take modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 249 + UInt256.ofNat 3 = UInt256.ofNat 252 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [selectGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    selectLoop, selectBodyEntry, selectPCs, hc11, hc12, hc13, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

set_option linter.unusedSimpArgs false in
theorem run_selectBody (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBodyPath
      (selectBodyEntry s dst src take modulus count i returnDest rest) =
        some (selectLoop s dst src take modulus count (i + 1)
          returnDest rest) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hloop : (244 : UInt256) = UInt256.ofNat 244 := by decide
  have hloopNat : (244 : UInt256).toNat = 244 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (244 : UInt256).toNat = true := by
    rw [hloopNat]
    exact jump245
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  simp (config := { maxSteps := 800000 })
    [selectBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      selectBodyEntry, selectLoop, selectProgress,
      selectPCs, hc11, hc12, hc13, hc14, hc15, hc16, hc17,
      hcode, hrun, hone, hfive, hfiveK, hinc, hloop, hloopNat,
      hjump, jump245, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_selectFinishGuard (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (selectLoop s dst src take modulus count count returnDest rest) =
        some (selectExit s dst src take modulus count returnDest rest) := by
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (292 : UInt256) = UInt256.ofNat 292 := by decide
  have hdestNat : (292 : UInt256).toNat = 292 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (292 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump293
  have hpc : UInt256.ofNat 249 + UInt256.ofNat 3 = UInt256.ofNat 252 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [selectGuardPath, opAt, pushAt, wfOp, selectLoop, selectExit, selectPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc11, hc12, hc13, hcode, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hdest, hdestNat, hjump, jump293, hpc]

set_option linter.unusedSimpArgs false in
theorem run_selectExit (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectExitPath
      (selectExit s dst src take modulus count returnDest rest) =
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
  simp [selectExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    selectExit, selectLoop, addReturned, selectPCs, hc1, hc2, hc3, hc4,
    hc5, hc6, hc7, hc8, hc9, hc10, hc11, hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ### Whole-helper execution certificate -/

def gasSteps_addSetup (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (addLoop s dst src take modulus count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addSetupPath hcode hfork
      (run_addSetup s dst src take modulus count returnDest rest (by omega) hrun)
      hrun hnp

def gasSteps_addIteration (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addLoop s dst src take modulus count i returnDest rest)
      (addLoop s dst src take modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addGuardPath
        (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addLoop, State.fork] using hfork)
        (run_addGuard s dst src take modulus count i returnDest rest (by omega)
          hcount hi hrun)
        (by simpa [addLoop] using hrun)
        (by simpa [addLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addBodyPath
        (by simpa [addBodyEntry, addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addBodyEntry, addLoop, State.fork] using hfork)
        (run_addBody s dst src take modulus count i returnDest rest (by omega)
          (by omega) hcode hrun)
        (by simpa [addBodyEntry, addLoop] using hrun)
        (by simpa [addBodyEntry, addLoop, State.fork] using hnp))

def gasSteps_addLoop (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addLoop s dst src take modulus count 0 returnDest rest)
      (addLoop s dst src take modulus count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_addIteration s dst src take modulus count i returnDest rest hcap
      hcount hi hcode hfork hrun hnp

def gasSteps_addToSubtract (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addLoop s dst src take modulus count count returnDest rest)
      (subtractLoop s dst src take modulus count 0 returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addGuardPath
      (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [addLoop, State.fork] using hfork)
      (run_addFinishGuard s dst src take modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [addLoop] using hrun)
      (by simpa [addLoop, State.fork] using hnp)
  have htransition := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addToSubtractPath
      (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [addLoop, State.fork] using hfork)
      (run_addToSubtract s dst src take modulus count returnDest rest (by omega)
        hrun)
      (by simpa [addLoop] using hrun)
      (by simpa [addLoop, State.fork] using hnp)
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [subtractLoop, subtractLoopEntry, subtractProgress, hzero] using
    hguard.trans htransition

def gasSteps_subtractIteration (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (subtractLoop s dst src take modulus count i returnDest rest)
      (subtractLoop s dst src take modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractGuardPath
        (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [subtractLoop, State.fork] using hfork)
        (run_subtractGuard s dst src take modulus count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [subtractLoop] using hrun)
        (by simpa [subtractLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractBodyPath
        (by simpa [subtractBodyEntry, subtractLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [subtractBodyEntry, subtractLoop, State.fork] using hfork)
        (run_subtractBody s dst src take modulus count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [subtractBodyEntry, subtractLoop] using hrun)
        (by simpa [subtractBodyEntry, subtractLoop, State.fork] using hnp))

def gasSteps_subtractLoop (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (subtractLoop s dst src take modulus count 0 returnDest rest)
      (subtractLoop s dst src take modulus count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_subtractIteration s dst src take modulus count i returnDest rest
      hcap hcount hi hcode hfork hrun hnp

def gasSteps_subtractToSelect (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (subtractLoop s dst src take modulus count count returnDest rest)
      (selectLoop s dst src take modulus count 0 returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka subtractGuardPath
      (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [subtractLoop, State.fork] using hfork)
      (run_subtractFinishGuard s dst src take modulus count returnDest rest hcap
        hcode hrun)
      (by simpa [subtractLoop] using hrun)
      (by simpa [subtractLoop, State.fork] using hnp)
  have htransition := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka subtractToSelectPath
      (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [subtractLoop, State.fork] using hfork)
      (run_subtractToSelect s dst src take modulus count returnDest rest hcap hrun)
      (by simpa [subtractLoop] using hrun)
      (by simpa [subtractLoop, State.fork] using hnp)
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [selectLoop, selectLoopEntry, selectProgress, hzero] using
    hguard.trans htransition

def gasSteps_selectIteration (s : State) (dst src take modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s dst src take modulus count i returnDest rest)
      (selectLoop s dst src take modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectLoop, State.fork] using hfork)
        (run_selectGuard s dst src take modulus count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [selectLoop] using hrun)
        (by simpa [selectLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectBodyPath
        (by simpa [selectBodyEntry, selectLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [selectBodyEntry, selectLoop, State.fork] using hfork)
        (run_selectBody s dst src take modulus count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [selectBodyEntry, selectLoop] using hrun)
        (by simpa [selectBodyEntry, selectLoop, State.fork] using hnp))

def gasSteps_selectLoop (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s dst src take modulus count 0 returnDest rest)
      (selectLoop s dst src take modulus count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_selectIteration s dst src take modulus count i returnDest rest
      hcap hcount hi hcode hfork hrun hnp

def gasSteps_selectFinish (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (selectLoop s dst src take modulus count count returnDest rest)
      (addReturned s dst src take modulus count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectLoop, State.fork] using hfork)
        (run_selectFinishGuard s dst src take modulus count returnDest rest hcap
          hcode hrun)
        (by simpa [selectLoop] using hrun)
        (by simpa [selectLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectExitPath
        (by simpa [selectExit, selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectExit, selectLoop, State.fork] using hfork)
        (run_selectExit s dst src take modulus count returnDest rest hcap hcode
          hvalid hrun)
        (by simpa [selectExit, selectLoop] using hrun)
        (by simpa [selectExit, selectLoop, State.fork] using hnp))

def gasSteps_addMaskedMod (s : State) (dst src take modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst src take modulus count returnDest rest)
      (addReturned s dst src take modulus count returnDest rest) :=
  (gasSteps_addSetup s dst src take modulus count returnDest rest hcap hcode
    hfork hrun hnp).trans <|
  (gasSteps_addLoop s dst src take modulus count returnDest rest hcap hcount
    hcode hfork hrun hnp).trans <|
  (gasSteps_addToSubtract s dst src take modulus count returnDest rest hcap hcode
    hfork hrun hnp).trans <|
  (gasSteps_subtractLoop s dst src take modulus count returnDest rest hcap hcount
    hcode hfork hrun hnp).trans <|
  (gasSteps_subtractToSelect s dst src take modulus count returnDest rest hcap
    hcode hfork hrun hnp).trans <|
  (gasSteps_selectLoop s dst src take modulus count returnDest rest hcap hcount
    hcode hfork hrun hnp).trans <|
  gasSteps_selectFinish s dst src take modulus count returnDest rest hcap hcode
    hfork hrun hnp hvalid

/-! ### Exact gas potential

As elsewhere in `EvmProof`, the potential is `gas + memCost(activeWords)`.
This makes memory expansion telescope across loads and stores while retaining
an exact, compositional statement for callers.
-/

theorem gasSteps_addSetup_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_addSetup s dst src take modulus count returnDest rest hcap hcode
        hfork hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
      13 + MachineState.memCost
        (addLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    addSetupPath 13
      (run_addSetup s dst src take modulus count returnDest rest (by omega) hrun)
      (by simpa [addEntry, State.fork] using hfork)
      (by decide) (by rfl)
  unfold gasSteps_addSetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [addEntry] using hmeter

theorem gasSteps_addIteration_cost_potential (s : State)
    (dst src take modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_addIteration s dst src take modulus count i returnDest rest hcap
        hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
          (addLoop s dst src take modulus count i returnDest rest).activeWords.toNat =
      164 + MachineState.memCost
        (addLoop s dst src take modulus count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    addGuardPath 26
      (run_addGuard s dst src take modulus count i returnDest rest (by omega)
        hcount hi hrun)
      (by simpa [addLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    addBodyPath 138
      (run_addBody s dst src take modulus count i returnDest rest (by omega)
        (by omega) hcode hrun)
      (by simpa [addBodyEntry, addLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addGuardPath
        (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addLoop, State.fork] using hfork)
        (run_addGuard s dst src take modulus count i returnDest rest (by omega)
          hcount hi hrun)
        (by simpa [addLoop] using hrun)
        (by simpa [addLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addBodyPath
        (by simpa [addBodyEntry, addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addBodyEntry, addLoop, State.fork] using hfork)
        (run_addBody s dst src take modulus count i returnDest rest (by omega)
          (by omega) hcode hrun)
        (by simpa [addBodyEntry, addLoop] using hrun)
        (by simpa [addBodyEntry, addLoop, State.fork] using hnp)))
    26 138 hguard hbody
  simpa [gasSteps_addIteration] using htrans

theorem gasSteps_addLoop_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_addLoop s dst src take modulus count returnDest rest hcap hcount
        hcode hfork hrun hnp).cost + MachineState.memCost
          (addLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat =
      count * 164 + MachineState.memCost
        (addLoop s dst src take modulus count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_addLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_addIteration_cost_potential s dst src take modulus count i
    returnDest rest hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_addToSubtract_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_addToSubtract s dst src take modulus count returnDest rest hcap
        hcode hfork hrun hnp).cost + MachineState.memCost
          (addLoop s dst src take modulus count count returnDest rest).activeWords.toNat =
      33 + MachineState.memCost
        (subtractLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    addGuardPath 26
      (run_addFinishGuard s dst src take modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [addLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    addToSubtractPath 7
      (run_addToSubtract s dst src take modulus count returnDest rest (by omega)
        hrun)
      (by simpa [addLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addGuardPath
        (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addLoop, State.fork] using hfork)
        (run_addFinishGuard s dst src take modulus count returnDest rest (by omega)
          hcode hrun)
        (by simpa [addLoop] using hrun)
        (by simpa [addLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addToSubtractPath
        (by simpa [addLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [addLoop, State.fork] using hfork)
        (run_addToSubtract s dst src take modulus count returnDest rest (by omega)
          hrun)
        (by simpa [addLoop] using hrun)
        (by simpa [addLoop, State.fork] using hnp)))
    26 7 hguard hnext
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [gasSteps_addToSubtract, subtractLoop, subtractLoopEntry,
    subtractProgress, hzero] using htrans

theorem gasSteps_subtractIteration_cost_potential (s : State)
    (dst src take modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_subtractIteration s dst src take modulus count i returnDest rest
        hcap hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
          (subtractLoop s dst src take modulus count i returnDest rest).activeWords.toNat =
      163 + MachineState.memCost
        (subtractLoop s dst src take modulus count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    subtractGuardPath 26
      (run_subtractGuard s dst src take modulus count i returnDest rest hcap
        hcount hi hrun)
      (by simpa [subtractLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    subtractBodyPath 137
      (run_subtractBody s dst src take modulus count i returnDest rest hcap
        (by omega) hcode hrun)
      (by simpa [subtractBodyEntry, subtractLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractGuardPath
        (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [subtractLoop, State.fork] using hfork)
        (run_subtractGuard s dst src take modulus count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [subtractLoop] using hrun)
        (by simpa [subtractLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractBodyPath
        (by simpa [subtractBodyEntry, subtractLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [subtractBodyEntry, subtractLoop, State.fork] using hfork)
        (run_subtractBody s dst src take modulus count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [subtractBodyEntry, subtractLoop] using hrun)
        (by simpa [subtractBodyEntry, subtractLoop, State.fork] using hnp)))
    26 137 hguard hbody
  simpa [gasSteps_subtractIteration] using htrans

theorem gasSteps_subtractLoop_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_subtractLoop s dst src take modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp).cost + MachineState.memCost
          (subtractLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat =
      count * 163 + MachineState.memCost
        (subtractLoop s dst src take modulus count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_subtractLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_subtractIteration_cost_potential s dst src take modulus count i
    returnDest rest hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_subtractToSelect_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_subtractToSelect s dst src take modulus count returnDest rest hcap
        hcode hfork hrun hnp).cost + MachineState.memCost
          (subtractLoop s dst src take modulus count count returnDest rest).activeWords.toNat =
      48 + MachineState.memCost
        (selectLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    subtractGuardPath 26
      (run_subtractFinishGuard s dst src take modulus count returnDest rest hcap
        hcode hrun)
      (by simpa [subtractLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    subtractToSelectPath 22
      (run_subtractToSelect s dst src take modulus count returnDest rest hcap hrun)
      (by simpa [subtractLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractGuardPath
        (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [subtractLoop, State.fork] using hfork)
        (run_subtractFinishGuard s dst src take modulus count returnDest rest hcap
          hcode hrun)
        (by simpa [subtractLoop] using hrun)
        (by simpa [subtractLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractToSelectPath
        (by simpa [subtractLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [subtractLoop, State.fork] using hfork)
        (run_subtractToSelect s dst src take modulus count returnDest rest hcap hrun)
        (by simpa [subtractLoop] using hrun)
        (by simpa [subtractLoop, State.fork] using hnp)))
    26 22 hguard hnext
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [gasSteps_subtractToSelect, selectLoop, selectLoopEntry,
    selectProgress, hzero] using htrans

theorem gasSteps_selectIteration_cost_potential (s : State)
    (dst src take modulus : UInt256) (count i : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selectIteration s dst src take modulus count i returnDest rest
        hcap hcount hi hcode hfork hrun hnp).cost + MachineState.memCost
          (selectLoop s dst src take modulus count i returnDest rest).activeWords.toNat =
      126 + MachineState.memCost
        (selectLoop s dst src take modulus count (i + 1) returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    selectGuardPath 26
      (run_selectGuard s dst src take modulus count i returnDest rest hcap
        hcount hi hrun)
      (by simpa [selectLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    selectBodyPath 100
      (run_selectBody s dst src take modulus count i returnDest rest hcap
        (by omega) hcode hrun)
      (by simpa [selectBodyEntry, selectLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectLoop, State.fork] using hfork)
        (run_selectGuard s dst src take modulus count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [selectLoop] using hrun)
        (by simpa [selectLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectBodyPath
        (by simpa [selectBodyEntry, selectLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [selectBodyEntry, selectLoop, State.fork] using hfork)
        (run_selectBody s dst src take modulus count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [selectBodyEntry, selectLoop] using hrun)
        (by simpa [selectBodyEntry, selectLoop, State.fork] using hnp)))
    26 100 hguard hbody
  simpa [gasSteps_selectIteration] using htrans

theorem gasSteps_selectLoop_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selectLoop s dst src take modulus count returnDest rest hcap hcount
        hcode hfork hrun hnp).cost + MachineState.memCost
          (selectLoop s dst src take modulus count 0 returnDest rest).activeWords.toNat =
      count * 126 + MachineState.memCost
        (selectLoop s dst src take modulus count count returnDest rest).activeWords.toNat := by
  unfold gasSteps_selectLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  exact gasSteps_selectIteration_cost_potential s dst src take modulus count i
    returnDest rest hcap hcount hi hcode hfork hrun hnp

theorem gasSteps_selectFinish_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_selectFinish s dst src take modulus count returnDest rest hcap hcode
        hfork hrun hnp hvalid).cost + MachineState.memCost
          (selectLoop s dst src take modulus count count returnDest rest).activeWords.toNat =
      55 + MachineState.memCost
        (addReturned s dst src take modulus count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    selectGuardPath 26
      (run_selectFinishGuard s dst src take modulus count returnDest rest hcap
        hcode hrun)
      (by simpa [selectLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    selectExitPath 29
      (run_selectExit s dst src take modulus count returnDest rest hcap hcode
        hvalid hrun)
      (by simpa [selectExit, selectLoop, State.fork] using hfork)
      (by decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectLoop, State.fork] using hfork)
        (run_selectFinishGuard s dst src take modulus count returnDest rest hcap
          hcode hrun)
        (by simpa [selectLoop] using hrun)
        (by simpa [selectLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectExitPath
        (by simpa [selectExit, selectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [selectExit, selectLoop, State.fork] using hfork)
        (run_selectExit s dst src take modulus count returnDest rest hcap hcode
          hvalid hrun)
        (by simpa [selectExit, selectLoop] using hrun)
        (by simpa [selectExit, selectLoop, State.fork] using hnp)))
    26 29 hguard hexit
  simpa [gasSteps_selectFinish] using htrans

theorem gasSteps_addMaskedMod_cost_potential (s : State)
    (dst src take modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (gasSteps_addMaskedMod s dst src take modulus count returnDest rest hcap
        hcount hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      (149 + count * 453) + MachineState.memCost
        (addReturned s dst src take modulus count returnDest rest).activeWords.toNat := by
  have hsetup := gasSteps_addSetup_cost_potential s dst src take modulus count
    returnDest rest hcap hcode hfork hrun hnp
  have hadd := gasSteps_addLoop_cost_potential s dst src take modulus count
    returnDest rest hcap hcount hcode hfork hrun hnp
  have haddFinish := gasSteps_addToSubtract_cost_potential s dst src take modulus
    count returnDest rest hcap hcode hfork hrun hnp
  have hsub := gasSteps_subtractLoop_cost_potential s dst src take modulus count
    returnDest rest hcap hcount hcode hfork hrun hnp
  have hsubFinish := gasSteps_subtractToSelect_cost_potential s dst src take
    modulus count returnDest rest hcap hcode hfork hrun hnp
  have hselect := gasSteps_selectLoop_cost_potential s dst src take modulus count
    returnDest rest hcap hcount hcode hfork hrun hnp
  have hfinish := gasSteps_selectFinish_cost_potential s dst src take modulus
    count returnDest rest hcap hcode hfork hrun hnp hvalid
  unfold gasSteps_addMaskedMod
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
