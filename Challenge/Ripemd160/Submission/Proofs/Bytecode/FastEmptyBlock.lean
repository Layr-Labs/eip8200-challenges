import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Empty-input block shortcut

The appended dispatcher preserves the legacy compressor entry stack. A
nonempty calldata buffer therefore jumps to the existing compressor. For the
unique padded block of empty calldata, it installs the five known chaining
words and returns directly to the driver.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def h0 : UInt256 := UInt256.ofNat 0xa585119c
def h1 : UInt256 := UInt256.ofNat 0x54fce9c5
def h2 : UInt256 := UInt256.ofNat 0x97082861
def h3 : UInt256 := UInt256.ofNat 0x48f5e87e
def h4 : UInt256 := UInt256.ofNat 0x318d25b2

def emptyHash : Compression.EvmHashState :=
  { h0 := h0, h1 := h1, h2 := h2, h3 := h3, h4 := h4 }

/-- Kernel-checked evaluation of the unique padded block for empty calldata. -/
theorem compress_empty :
    Crypto.Ripemd160.compressBlock Crypto.Ripemd160.H0
        (Padding.paddedMessage ByteArray.empty) 0 =
      #[0xa585119c, 0x54fce9c5, 0x97082861, 0x48f5e87e, 0x318d25b2] := by
  let initial : Compression.HashState :=
    { h0 := 0x67452301, h1 := 0xefcdab89, h2 := 0x98badcfe
      h3 := 0x10325476, h4 := 0xc3d2e1f0 }
  have hspec := CompressionCorrect.compressModel_eq_compressBlock
    (Padding.paddedMessage ByteArray.empty) 0 initial
  have hinitial : CompressionCorrect.hashArray initial =
      Crypto.Ripemd160.H0 := by rfl
  rw [hinitial] at hspec
  rw [← hspec]
  have hschedule :
      CompressionCorrect.schedule (Padding.paddedMessage ByteArray.empty) 0 =
        #[0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    apply Array.ext
    · norm_num (config := { maxSteps := 1000000 })
        [CompressionCorrect.schedule, Padding.paddedMessage, Padding.zeroBytes,
          Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
          Crypto.Ripemd160.readLE32, List.range', List.foldl,
          Array.setIfInBounds]
    · intro i hi
      have hi16 : i < 16 := by
        simpa [CompressionCorrect.schedule, List.range', List.foldl] using hi
      interval_cases i <;>
        norm_num (config := { maxSteps := 1000000 })
          [CompressionCorrect.schedule, Padding.paddedMessage, Padding.zeroBytes,
            Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
            Crypto.Ripemd160.readLE32, List.range', List.foldl,
            Array.setIfInBounds] <;>
        simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  rw [hschedule]
  norm_num (config := { maxSteps := 1000000 })
    [initial, CompressionCorrect.hashArray, CompressionCorrect.compressModel,
      Compression.combine, CompressionCorrect.workingOfHash,
      CompressionCorrect.leftRounds, CompressionCorrect.rightRounds,
      CompressionCorrect.leftStep, CompressionCorrect.rightStep,
      Compression.round, Crypto.Ripemd160.f, Crypto.Ripemd160.bnot32,
      Crypto.Ripemd160.rotl32, Crypto.Ripemd160.r, Crypto.Ripemd160.rP,
      Crypto.Ripemd160.s, Crypto.Ripemd160.sP, Crypto.Ripemd160.K,
      Crypto.Ripemd160.KP]
  decide

def decisionPath : List Located :=
  [⟨77, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨78, .push ⟨2, by decide⟩ (UInt256.ofNat 5035), by rfl, by decide⟩,
   ⟨79, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def bodyPrefixPath : List Located :=
  [⟨80, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨81, .push ⟨2, by decide⟩ (UInt256.ofNat 5270), by rfl, by decide⟩,
   ⟨82, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩]

def bodySuffixPath : List Located :=
  [⟨84, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bodyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x7e
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x66,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

/-- Entry state for the original empty-input dispatcher.  The outer exact-input
dispatcher falls back to this address without changing the compressor stack. -/
def legacyDispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x79
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x66,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

/-- Nonempty dispatcher target: checked first-block helper. -/
def nonemptyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 5035
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

private def writeWord (memory : ByteArray) (offset : Nat)
    (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def emptyMemory (memory : ByteArray) : ByteArray :=
  let m0 := writeWord memory 0x20 h0
  let m1 := writeWord m0 0x40 h1
  let m2 := writeWord m1 0x60 h2
  let m3 := writeWord m2 0x80 h3
  writeWord m3 0xa0 h4

def emptyCodeTable : ByteArray :=
  (((Data.Bytes.natToBytesPadded h0.toNat 32 ++
      Data.Bytes.natToBytesPadded h1.toNat 32) ++
      Data.Bytes.natToBytesPadded h2.toNat 32) ++
      Data.Bytes.natToBytesPadded h3.toNat 32) ++
      Data.Bytes.natToBytesPadded h4.toNat 32

private theorem emptyMemory_codeTable (memory : ByteArray) :
    emptyMemory memory = MachineState.writeBytes memory emptyCodeTable 0x20 := by
  unfold emptyMemory emptyCodeTable writeWord
  rw [Challenge.EvmProof.Memory.writeBytes_append_adjacent,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]


def emptyActiveWords (s : State) : UInt256 :=
  let a0 := s.activeWordsAfterUInt256 0x20 32
  let a1 := UInt256.ofNat (MachineState.activeWordsAfter a0.toNat 0x40 32)
  let a2 := UInt256.ofNat (MachineState.activeWordsAfter a1.toNat 0x60 32)
  let a3 := UInt256.ofNat (MachineState.activeWordsAfter a2.toNat 0x80 32)
  UInt256.ofNat (MachineState.activeWordsAfter a3.toNat 0xa0 32)

def bodyCopyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { bodyEntry s input i with
    pc := UInt256.ofNat 0x85
    stack := [UInt256.ofNat 32, UInt256.ofNat 5270, UInt256.ofNat 160,
      DriverTrace.messageOffsetWord i, UInt256.ofNat 0x66,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

def bodyCopiedState (s : State) (input : ByteArray) (i : Nat) : State :=
  { bodyEntry s input i with
    pc := UInt256.ofNat 0x86
    memory := emptyMemory s.memory
    activeWords := emptyActiveWords s }

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x66
    stack := [DriverTrace.blockOffsetWord i, Padding.paddedWord input]
    memory := emptyMemory s.memory
    activeWords := emptyActiveWords s }

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by
  rfl

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by
  rfl

private theorem readWord_writeWord_same (memory : ByteArray)
    (offset : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory offset value) offset = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

private theorem readWord_writeWord_disjoint (memory : ByteArray)
    (readStart writeStart : Nat) (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readWord (writeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

@[simp] private theorem emptyMemory_h0 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x20 = h0 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h1 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x40 = h1 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h2 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x60 = h2 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h3 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x80 = h3 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h4 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0xa0 = h4 := by
  unfold emptyMemory
  exact readWord_writeWord_same _ _ _

@[simp] theorem resultState_hashAt (s : State) (input : ByteArray) (i : Nat) :
    StackMemory.hashAt (resultState s input i).memory = emptyHash := by
  unfold StackMemory.hashAt resultState emptyHash
  rw [emptyMemory_h0, emptyMemory_h1, emptyMemory_h2, emptyMemory_h3,
    emptyMemory_h4]

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x120 ≤ address) :
    MachineState.readWord (resultState s input i).memory address =
      MachineState.readWord s.memory address := by
  unfold resultState emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega))]

theorem run_decision_nonempty (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock decisionPath
      (legacyDispatchEntry s input i) =
        some (nonemptyEntry s input i) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hmod : input.size % 2 ^ 256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hsize]
    omega
  norm_num at hmod
  have htrue : UInt256.isTrue (UInt256.ofNat input.size) := by
    exact hmod
  have hdest : Decode.isValidJumpDest submissionBytecode 5035 = true := by
    have hpc : Artifact.submissionArtifact.instructionPC 4090 = 5035 := by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]
      decide
    have h := Artifact.submissionArtifact.isValidJumpDest_index 4090 (by rfl)
    rw [hpc] at h
    exact h
  have hpc2792 : Artifact.submissionArtifact.instructionPC 77 = 0x79 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2793 : Artifact.submissionArtifact.instructionPC 77 = 0x79 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2794 : Artifact.submissionArtifact.instructionPC 78 = 0x7a := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2795 : Artifact.submissionArtifact.instructionPC 79 = 0x7d := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [decisionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    legacyDispatchEntry, nonemptyEntry, hcalldata, hcode,
    hrun, hmod, htrue, hdest, hpc2792, hpc2793, hpc2794, hpc2795, UInt256.isTrue,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_decision_empty (s : State) (input : ByteArray) (i : Nat)
    (hempty : input.size = 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock decisionPath
      (legacyDispatchEntry s input i) = some (bodyEntry s input i) := by
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat input.size) := by
    simp [hempty, UInt256.isTrue]
  have hpc2792 : Artifact.submissionArtifact.instructionPC 77 = 0x79 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2793 : Artifact.submissionArtifact.instructionPC 77 = 0x79 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2794 : Artifact.submissionArtifact.instructionPC 78 = 0x7a := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc2795 : Artifact.submissionArtifact.instructionPC 79 = 0x7d := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [decisionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    legacyDispatchEntry, bodyEntry, hcalldata, hrun, hempty, hfalse,
    hpc2792, hpc2793, hpc2794, hpc2795,
    UInt256.isTrue, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

set_option maxHeartbeats 5000000 in
private theorem bodyCodeTable :
    MachineState.readPadded submissionBytecode 5270 160 = emptyCodeTable := by
  decide

private theorem run_bodyPrefix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodyPrefixPath
      (bodyEntry s input i) = some (bodyCopyEntry s input i) := by
  have hpc80 : Artifact.submissionArtifact.instructionPC 80 = 0x7e := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc81 : Artifact.submissionArtifact.instructionPC 81 = 0x80 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc82 : Artifact.submissionArtifact.instructionPC 82 = 0x83 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc83 : Artifact.submissionArtifact.instructionPC 83 = 0x85 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [bodyPrefixPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bodyEntry, bodyCopyEntry, hcode, hrun, hpc80, hpc81, hpc82, hpc83,
    Challenge.EvmProof.Word.succ_ofNat_mod]

private theorem run_bodySuffix (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodySuffixPath
      (bodyCopiedState s input i) = some (resultState s input i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x66 = true := by
    have hpc : Artifact.submissionArtifact.instructionPC 64 = 0x66 := by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]
      decide
    have h := Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
    rw [hpc] at h
    exact h
  have hpc84 : Artifact.submissionArtifact.instructionPC 84 = 0x86 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc85 : Artifact.submissionArtifact.instructionPC 85 = 0x87 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [bodySuffixPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bodyCopiedState, resultState, bodyEntry, hcode, hrun, hdest,
    hpc84, hpc85, Challenge.EvmProof.Word.succ_ofNat_mod]

def gasSteps_codecopy (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (bodyCopyEntry s input i) (bodyCopiedState s input i) := by
  let pre := bodyCopyEntry s input i
  let cost := Gas.codecopyTotal pre (UInt256.ofNat 5270) (UInt256.ofNat 160)
  refine GasSteps.one cost ?_
  intro gas hgas
  have hcode' : (withGas pre gas).executionEnv.code =
      Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hpc : (withGas pre gas).pc.toNat =
      Artifact.submissionArtifact.instructionPC 83 := by
    change (UInt256.ofNat 0x85).toNat = _
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hdec := Stepper.decodes_of_artifact
    Artifact.submissionArtifact (withGas pre gas) 83 (.op .CODECOPY)
    hcode' hpc (by rfl) (by exact ⟨by decide, trivial, rfl⟩)
  change (withGas pre gas).decodedOp = some .CODECOPY at hdec
  apply EVM.Step.running
  · simpa [pre, bodyCopyEntry, withGas] using hrun
  · simpa [pre, bodyCopyEntry, withGas] using hnp
  · have hstack :
        (withGas pre gas).stack =
          UInt256.ofNat 32 :: UInt256.ofNat 5270 :: UInt256.ofNat 160 ::
            [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x66,
              DriverTrace.blockOffsetWord i, Padding.paddedWord input] := by
      rfl
    have hcap : (withGas pre gas).stack.length +
        Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY := by
      norm_num [pre, bodyCopyEntry, bodyEntry, withGas,
        Operation.pushArity, Operation.popArity]
    have hstep := StepRunning.codecopy (withGas pre gas)
      (UInt256.ofNat 32) (UInt256.ofNat 5270) (UInt256.ofNat 160)
      [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x66,
        DriverTrace.blockOffsetWord i, Padding.paddedWord input]
      hdec hstack hgas hcap
    have h32 : (32 : Nat) % 2 ^ 256 = 32 := Nat.mod_eq_of_lt (by norm_num)
    have h5270 : (5270 : Nat) % 2 ^ 256 = 5270 :=
      Nat.mod_eq_of_lt (by norm_num)
    have h160 : (160 : Nat) % 2 ^ 256 = 160 := Nat.mod_eq_of_lt (by norm_num)
    simpa [pre, cost, bodyCopyEntry, bodyCopiedState, bodyEntry,
      emptyMemory_codeTable, emptyActiveWords, withGas, Gas.codecopyTotal,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
      h32, h5270, h160, bodyCodeTable, hcode,
      Challenge.EvmProof.Word.succ_ofNat (n := 0x85) (by norm_num)] using hstep

private def gasStepsBlock (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

def gasSteps_nonempty (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (legacyDispatchEntry s input i)
      (nonemptyEntry s input i) :=
  gasStepsBlock decisionPath _ _ hcode hfork
    (run_decision_nonempty s input i hfit hpositive hcalldata hcode hrun)
    hrun hnp

def gasSteps_empty (s : State) (input : ByteArray) (i : Nat)
    (hempty : input.size = 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (legacyDispatchEntry s input i) (resultState s input i) := by
  have gdecision := gasStepsBlock decisionPath
    (legacyDispatchEntry s input i) (bodyEntry s input i)
    hcode hfork (run_decision_empty s input i hempty hcalldata hrun) hrun hnp
  have gprefix := gasStepsBlock bodyPrefixPath
    (bodyEntry s input i) (bodyCopyEntry s input i)
    hcode hfork (run_bodyPrefix s input i hcode hrun) hrun hnp
  have gcopy := gasSteps_codecopy s input i hcode hrun hnp
  have gsuffix := gasStepsBlock bodySuffixPath
    (bodyCopiedState s input i) (resultState s input i)
    (by simpa [bodyCopiedState, bodyEntry] using hcode)
    (by simpa [bodyCopiedState, bodyEntry, State.fork] using hfork)
    (run_bodySuffix s input i hcode hrun)
    (by simpa [bodyCopiedState, bodyEntry] using hrun)
    (by simpa [bodyCopiedState, bodyEntry] using hnp)
  exact gdecision.trans (gprefix.trans (gcopy.trans gsuffix))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
