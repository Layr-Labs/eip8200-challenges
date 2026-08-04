import Challenge.Modexp.Reference.Proofs.Bytecode.Artifact
import Challenge.Modexp.Reference.Proofs.Limbs
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

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigHelpers

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
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def clearSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 15 .JUMPDEST, pushAt 16 0 0]

def clearGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 17 .JUMPDEST, opAt 18 (.Dup ⟨2, by decide⟩),
   opAt 19 (.Dup ⟨1, by decide⟩), opAt 20 .LT, opAt 21 .ISZERO,
   pushAt 22 2 48, opAt 23 .JUMPI]

def clearBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 24 0 0, opAt 25 (.Dup ⟨1, by decide⟩), pushAt 26 1 5,
   opAt 27 .SHL, opAt 28 (.Dup ⟨3, by decide⟩), opAt 29 .ADD,
   opAt 30 .MSTORE, pushAt 31 1 1, opAt 32 (.Dup ⟨1, by decide⟩),
   opAt 33 .ADD, opAt 34 (.Swap ⟨0, by decide⟩), opAt 35 .POP,
   pushAt 36 2 21, opAt 37 .JUMP]

def clearExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
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
    Artifact.referenceArtifact.instructionPC i =
      [19,20,21,22,23,24,25,26,29,30,31,32,34,35,36,37,38,40,
       41,42,43,44,47,48,49,50,51,52][i - 15]! := by
  interval_cases i <;> decide

@[simp] private theorem jump21 :
    Decode.isValidJumpDest referenceBytecode 21 = true :=
  Artifact.isValidJumpDest_index 17 (by rfl)

@[simp] private theorem jump48 :
    Decode.isValidJumpDest referenceBytecode 48 = true :=
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
    (hcode : s.executionEnv.code = referenceBytecode)
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
  have hjump : Decode.isValidJumpDest referenceBytecode
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock clearGuardPath
      (clearLoop s ptr count count returnDest rest) =
        some (clearExit s ptr count returnDest rest) := by
  have hnmod : count % 2 ^ 256 = count := Nat.mod_eq_of_lt hcount
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hfortyEight : (48 : UInt256) = UInt256.ofNat 48 := by decide
  have hfortyEightNat : (48 : UInt256).toNat = 48 := by decide
  have hjump : Decode.isValidJumpDest referenceBytecode
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
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = referenceBytecode)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true)
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
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearEntry s ptr count returnDest rest)
      (clearLoop s ptr count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka clearSetupPath hcode hfork
      (run_clearSetup s ptr count returnDest rest hcap hrun) hrun hnp

def gasSteps_clearIteration (s : State) (ptr : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hi : i < count) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count i returnDest rest)
      (clearLoop s ptr count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearGuard s ptr count i returnDest rest hcap hcount hi hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearBodyPath
        (by simpa [clearBodyEntry, clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
        (run_clearBody s ptr count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [clearBodyEntry, clearLoop] using hrun)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hnp))

def gasSteps_clearLoop (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count 0 returnDest rest)
      (clearLoop s ptr count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_clearIteration s ptr count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_clearFinish (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (clearLoop s ptr count count returnDest rest)
      (clearReturned s ptr count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearFinishGuard s ptr count returnDest rest hcap hcount hcode hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearExitPath
        (by simpa [clearExit, clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearExit, clearLoop, State.fork] using hfork)
        (run_clearExit s ptr count returnDest rest hcap hcode hvalid hrun)
        (by simpa [clearExit, clearLoop] using hrun)
        (by simpa [clearExit, clearLoop, State.fork] using hnp))

def gasSteps_clear (s : State) (ptr : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
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

theorem gasSteps_clearSetup_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_clearSetup s ptr count returnDest rest hcap hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      3 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearSetupPath 3 (run_clearSetup s ptr count returnDest rest hcap hrun)
    (by simpa [clearEntry, State.fork] using hfork)
    (by native_decide) (by rfl)
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
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
    (by native_decide) (by rfl)
  have hbody := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearBodyPath 45 (run_clearBody s ptr count i returnDest rest hcap
      (by omega) hcode hrun)
    (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
    (by native_decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearGuard s ptr count i returnDest rest hcap hcount hi hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearBodyPath
        (by simpa [clearBodyEntry, clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hfork)
        (run_clearBody s ptr count i returnDest rest hcap (by omega) hcode hrun)
        (by simpa [clearBodyEntry, clearLoop] using hrun)
        (by simpa [clearBodyEntry, clearLoop, State.fork] using hnp)))
    26 45 hguard hbody
  simpa [gasSteps_clearIteration] using htrans

theorem gasSteps_clearLoop_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (gasSteps_clearFinish s ptr count returnDest rest hcap hcount hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost
        (clearLoop s ptr count count returnDest rest).activeWords.toNat =
      41 + MachineState.memCost
        (clearReturned s ptr count returnDest rest).activeWords.toNat := by
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearGuardPath 26 (run_clearFinishGuard s ptr count returnDest rest
      hcap hcount hcode hrun)
    (by simpa [clearLoop, State.fork] using hfork)
    (by native_decide) (by rfl)
  have hexit := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    clearExitPath 15 (run_clearExit s ptr count returnDest rest hcap hcode
      hvalid hrun)
    (by simpa [clearExit, clearLoop, State.fork] using hfork)
    (by native_decide) (by rfl)
  have htrans := Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearGuardPath
        (by simpa [clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearLoop, State.fork] using hfork)
        (run_clearFinishGuard s ptr count returnDest rest hcap hcount hcode hrun)
        (by simpa [clearLoop] using hrun)
        (by simpa [clearLoop, State.fork] using hnp)))
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka clearExitPath
        (by simpa [clearExit, clearLoop, Artifact.referenceArtifact] using hcode)
        (by simpa [clearExit, clearLoop, State.fork] using hfork)
        (run_clearExit s ptr count returnDest rest hcap hcode hvalid hrun)
        (by simpa [clearExit, clearLoop] using hrun)
        (by simpa [clearExit, clearLoop, State.fork] using hnp)))
    26 15 hguard hexit
  simpa [gasSteps_clearFinish] using htrans

theorem gasSteps_clear_cost_potential (s : State) (ptr : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
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
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 46 .JUMPDEST, pushAt 47 0 0]

def copyGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 48 .JUMPDEST, opAt 49 (.Dup ⟨3, by decide⟩),
   opAt 50 (.Dup ⟨1, by decide⟩), opAt 51 .LT, opAt 52 .ISZERO,
   pushAt 53 2 93, opAt 54 .JUMPI]

def copyBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 55 (.Dup ⟨0, by decide⟩), pushAt 56 1 5, opAt 57 .SHL,
   opAt 58 (.Dup ⟨3, by decide⟩), opAt 59 .ADD, opAt 60 .MLOAD,
   opAt 61 (.Dup ⟨1, by decide⟩), pushAt 62 1 5, opAt 63 .SHL,
   opAt 64 (.Dup ⟨3, by decide⟩), opAt 65 .ADD, opAt 66 .MSTORE,
   pushAt 67 1 1, opAt 68 (.Dup ⟨1, by decide⟩), opAt 69 .ADD,
   opAt 70 (.Swap ⟨0, by decide⟩), opAt 71 .POP,
   pushAt 72 2 60, opAt 73 .JUMP]

def copyExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
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
    Artifact.referenceArtifact.instructionPC i =
      [58,59,60,61,62,63,64,65,68,69,70,72,73,74,75,76,77,
       79,80,81,82,83,85,86,87,88,89,92,93,94,95,96,97,98][i - 46]! := by
  interval_cases i <;> decide

@[simp] private theorem jump60 :
    Decode.isValidJumpDest referenceBytecode 60 = true :=
  Artifact.isValidJumpDest_index 48 (by rfl)

@[simp] private theorem jump93 :
    Decode.isValidJumpDest referenceBytecode 93 = true :=
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
    (hcode : s.executionEnv.code = referenceBytecode)
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
  have hjump : Decode.isValidJumpDest referenceBytecode
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyGuardPath
      (copyLoop s dst src count count returnDest rest) =
        some (copyExit s dst src count returnDest rest) := by
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hninetyThree : (93 : UInt256) = UInt256.ofNat 93 := by decide
  have hninetyThreeNat : (93 : UInt256).toNat = 93 := by decide
  have hjump : Decode.isValidJumpDest referenceBytecode
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
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = referenceBytecode)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true)
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

end Challenge.Modexp.Reference.Proofs.Bytecode.BigHelpers
