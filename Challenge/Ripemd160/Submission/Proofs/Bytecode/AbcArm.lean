import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

/-!
# The fused empty/`abc` arm: instructions 4082-4107, pc 5167-5241

Appended past the digest table.  Reached from the byte-0 `JUMPI` (instruction
4035), whose pushed destination (instruction 4034) is 5167.  Misses re-enter
the generic compressor at pc 268 (instruction 173).

One fused test covers both tiny inputs: `size ≫ 2` gates out everything of
four bytes or more, and `leadWord ⊻ size · 0x207621` vanishes exactly on the
empty input (`0 ⊻ 0`) and on `"abc"` (`0x616263 ⊻ 3 · 0x207621`).  The stored
word is `emptyDigest - size · K`, which is the empty digest at size 0 and the
`abc` digest at size 3.

```
 idx    pc    instruction
  4082   5167  JUMPDEST
  4083   5168  CALLDATASIZE
  4084   5169  PUSH1 2
  4085   5171  SHR            ; sizeWord = size >> 2
  4086   5172  PUSH2 268
  4087   5175  JUMPI          ; size >= 4 -> generic
  4088   5176  PUSH3 0x207621
  4089   5180  CALLDATASIZE
  4090   5181  MUL            ; size * 0x207621
  4091   5182  PUSH0
  4092   5183  CALLDATALOAD
  4093   5184  PUSH1 232
  4094   5186  SHR            ; leadWord
  4095   5187  XOR            ; mixWord
  4096   5188  PUSH2 268
  4097   5191  JUMPI          ; mix != 0 -> generic
  4098   5192  CALLDATASIZE
  4099   5193  PUSH20 K
  4100   5214  MUL            ; K * size
  4101   5215  PUSH20 C       ; emptyDigest
  4102   5236  SUB            ; C - K*size
  4103   5237  PUSH0
  4104   5238  MSTORE
  4105   5239  MSIZE          ; = 32 (memory was empty)
  4106   5240  PUSH0
  4107   5241  RETURN
```

Guard soundness is `AbcRecognition.zero_cases`; digest correctness is
`AbcDigest.spec_abc` and `EmptySpec.spec_empty`.  This module does NOT import
`DirectGuardBase` (whose closure pulls in the whole compression proof); its
helpers are copied.

Provenance: the arm's shape and its run lemmas are ported from
`TinyGuard.lean` at commit `7c9d3ca2` (submission `819379e5`, co-authored by
terrapinelf), retargeted to pc 5167 with generic entry 268.
-/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open AbcInputData AbcRecognition

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-- The generic compressor entry. Definitionally `DirectGuard.fallbackState`. -/
def fallbackState (input : ByteArray) : State := atPC input 268

def storeWord (memory : ByteArray) (offset : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

/-! ## Jump destinations (the `rw` idiom — cheap at high indices) -/

theorem pcArm : Artifact.submissionArtifact.instructionPC 4082 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5167 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4082 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 173 = 268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 268 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 173 (by rfl)
  rw [pcGeneric] at h
  exact h

/-! ## The size gate -/

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5167 []

def sizePath : List Located :=
  [opAt 4082 .JUMPDEST, opAt 4083 .CALLDATASIZE, pushAt 4084 1 2, opAt 4085 .SHR,
   pushAt 4086 2 268]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5175 [268, sizeWord input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4082 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4082 5167 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5167 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4083 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4083 5168 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5168 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4084 1 2
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4084 5169 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5169 1 2 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4085 .SHR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4085 5171 [2, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5171 2 sz [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4086 2 268
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4086 5172 [sizeWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5172 2 268 [sizeWord input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeWord input)) :
    run [opAt 4087 .JUMPI] (PatternedScan.stS input 5175 [268, sizeWord input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4087 .JUMPI)
    (PatternedScan.pcFactS input 4087 5175 [268, sizeWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5175 268 268 (sizeWord input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 268) hc generic_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeWord input)) :
    run [opAt 4087 .JUMPI] (PatternedScan.stS input 5175 [268, sizeWord input]) =
      some (PatternedScan.stS input 5176 []) :=
  PatternedScan.blockOfS (opAt 4087 .JUMPI)
    (PatternedScan.pcFactS input 4087 5175 [268, sizeWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5175 268 (sizeWord input) []
      (by simp) (by norm_num) hc)

/-! ## The content mix -/

def mixPath : List Located :=
  [pushAt 4088 3 2127393, opAt 4089 .CALLDATASIZE, opAt 4090 .MUL,
   pushAt 4091 0 0, opAt 4092 .CALLDATALOAD, pushAt 4093 1 232, opAt 4094 .SHR,
   opAt 4095 .XOR, pushAt 4096 2 268]

theorem run_mix (input : ByteArray) :
    run mixPath (PatternedScan.stS input 5176 []) =
      some (PatternedScan.stS input 5191 [268, mixWord input]) := by
  let sz := UInt256.ofNat input.size
  let w := MachineState.readWord input 0
  let l0 : Located := pushAt 4088 3 2127393
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4088 5176 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5176 3 2127393 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := opAt 4089 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4089 5180 [2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5180 [2127393] (by simp) (by norm_num))
  let l2 : Located := opAt 4090 .MUL
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4090 5181 [sz, 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_mul input 5181 sz 2127393 [] (by simp) (by norm_num))
  let l3 : Located := pushAt 4091 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4091 5182 [sz * 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5182 [sz * 2127393] (by simp) (by norm_num))
  let l4 : Located := opAt 4092 .CALLDATALOAD
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4092 5183 [0, sz * 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5183 0 [sz * 2127393] (by simp) (by norm_num))
  let l5 : Located := pushAt 4093 1 232
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4093 5184 [w, sz * 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5184 1 232 [w, sz * 2127393] (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := opAt 4094 .SHR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4094 5186 [232, w, sz * 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5186 232 w [sz * 2127393] (by simp) (by norm_num))
  let l7 : Located := opAt 4095 .XOR
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4095 5187
        [UInt256.shiftRight w 232, sz * 2127393] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5187 (UInt256.shiftRight w 232) (sz * 2127393) []
      (by simp) (by norm_num))
  let l8 : Located := pushAt 4096 2 268
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4096 5188 [mixWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5188 2 268 [mixWord input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  have s7 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ s6 rfl h7
  have s8 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7] [l8] _ _ _ s7 rfl h8
  exact s8

theorem run_mix_miss (input : ByteArray) (hc : UInt256.isTrue (mixWord input)) :
    run [opAt 4097 .JUMPI] (PatternedScan.stS input 5191 [268, mixWord input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4097 .JUMPI)
    (PatternedScan.pcFactS input 4097 5191 [268, mixWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5191 268 268 (mixWord input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 268) hc generic_dest)

theorem run_mix_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (mixWord input)) :
    run [opAt 4097 .JUMPI] (PatternedScan.stS input 5191 [268, mixWord input]) =
      some (PatternedScan.stS input 5192 []) :=
  PatternedScan.blockOfS (opAt 4097 .JUMPI)
    (PatternedScan.pcFactS input 4097 5191 [268, mixWord input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5191 268 (mixWord input) []
      (by simp) (by norm_num) hc)

/-! ## The stored return: `CALLDATASIZE PUSH20 K MUL PUSH20 C SUB`,
`PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

/-- The stored word: `emptyDigest - size · K`, which is the empty digest at
size 0 and the `abc` digest at size 3. -/
def answerWord (input : ByteArray) : UInt256 :=
  UInt256.sub (UInt256.ofNat EmptySpec.digestNat)
    (UInt256.mul (UInt256.ofNat 25448770637332498804579667936807160623886401639)
      (UInt256.ofNat input.size))

def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32

def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0

private theorem mul_op (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem sub_op (a b : UInt256) : a - b = UInt256.sub a b := rfl

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5239
    memory := answerMemory input
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5240, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5241
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory input) 0 32 }

def storePath : List Located :=
  [opAt 4098 .CALLDATASIZE,
   pushAt 4099 20 25448770637332498804579667936807160623886401639,
   opAt 4100 .MUL,
   pushAt 4101 20 890993315260586290631548281360202943075753233713,
   opAt 4102 .SUB, pushAt 4103 0 0, opAt 4104 .MSTORE]

def finishPath : List Located :=
  [pushAt 4106 0 0, opAt 4107 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4098 = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4099 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4100 = 5214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4101 = 5215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4102 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4103 = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet6 : Artifact.submissionArtifact.instructionPC 4104 = 5238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet7 : Artifact.submissionArtifact.instructionPC 4105 = 5239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet8 : Artifact.submissionArtifact.instructionPC 4106 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet9 : Artifact.submissionArtifact.instructionPC 4107 = 5241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5192 []) = some (storedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [storePath, opAt, pushAt, wfOp, PatternedScan.stS, storedState,
    answerMemory, answerBytes, answerWord, EmptySpec.digestNat, initialState,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, mul_op, sub_op,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_finish (input : ByteArray) :
    run finishPath (sizedState input) = some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [finishPath, opAt, pushAt, wfOp, sizedState, storedState, returnedState, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_msize (input : ByteArray) : GasSteps (storedState input) (sizedState input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4105 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4105 := by
    rw [pcRet7]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4105
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## Guard semantics -/

private theorem isTrue_of_ne (c : UInt256) (h : c ≠ 0) : UInt256.isTrue c := by
  intro hz
  exact h (Word.word_ext hz)

private theorem not_isTrue_of_eq (c : UInt256) (h : c = 0) : ¬ UInt256.isTrue c := by
  rw [h]; decide

/-! ## The two exported certificates -/

/-- **Miss.** Any input other than empty or `"abc"` leaves the arm at the
generic entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hnempty : input ≠ ByteArray.empty) (hne : input ≠ abcInput) :
    GasSteps (armEntry input) (fallbackState input) :=
  have hcond : condition input ≠ 0 := fun hz =>
    (zero_cases input hfit hz).elim hnempty hne
  if hs : sizeWord input = 0 then
    have hx : mixWord input ≠ 0 := fun hx =>
      hcond ((KnownInputLogic.wordOr_eq_zero_iff (mixWord input) (sizeWord input)).mpr
        ⟨hx, hs⟩)
    (sound sizePath (run_size input)).trans
      ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
        ((sound mixPath (run_mix input)).trans
          (sound _ (run_mix_miss input (isTrue_of_ne _ hx)))))
  else
    (sound sizePath (run_size input)).trans
      (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

/-- **Hit.** A zero condition stores `emptyDigest - size · K` and returns. -/
def gasSteps_hit (input : ByteArray) (hm : condition input = 0) :
    GasSteps (armEntry input) (returnedState input) := by
  have hz := (KnownInputLogic.wordOr_eq_zero_iff (mixWord input) (sizeWord input)).mp
    (condition_split input ▸ hm)
  exact (sound sizePath (run_size input)).trans
    ((sound _ (run_size_pass input (not_isTrue_of_eq _ hz.2))).trans
      ((sound mixPath (run_mix input)).trans
        ((sound _ (run_mix_hit input (not_isTrue_of_eq _ hz.1))).trans
          ((sound storePath (run_store input)).trans
            ((gasSteps_msize input).trans (sound finishPath (run_finish input)))))))

/-- The stored 32-byte answer for the empty input is `emptyOutput`. -/
theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

/-- The stored 32-byte answer for `"abc"` is `abcPaddedDigest`. -/
theorem answer_abc : answerBytes abcInput = abcPaddedDigest := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

/-- **The arm's contribution to `Correct`.** -/
theorem correct_hit (input : ByteArray) (hfit : CalldataFits input)
    (hm : condition input = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hm)
  have hspec : spec input = answerBytes input := by
    rcases zero_cases input hfit hm with h | h
    · subst input; rw [EmptySpec.spec_empty, answer_empty]
    · subst input; rw [AbcDigest.spec_abc, answer_abc]
  have hsize : (answerBytes input).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hread : MachineState.readPadded (answerMemory input) 0 32 = answerBytes input := by
    rw [← hsize]
    exact Memory.readPadded_writeBytes_same ByteArray.empty (answerBytes input) 0
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, returnedState, storedState, initialState,
      State.isDone, State.isHalted, State.isRunning]
    rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded (answerMemory input) 0 32)) at heval
  rw [hread, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas
      = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval

/-- `"abc"` hits the arm: `condition abcInput = 0`. -/
theorem correct_abc (input : ByteArray) (hfit : CalldataFits input) (heq : input = abcInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  correct_hit input hfit (heq ▸ condition_abc) entryPrefix

/-- The empty input hits the arm: `condition ByteArray.empty = 0`. -/
theorem correct_empty (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = ByteArray.empty)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  correct_hit input hfit (heq ▸ condition_empty) entryPrefix

#print axioms correct_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
