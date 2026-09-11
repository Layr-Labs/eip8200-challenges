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

/-- The empty-input test is `DriverTrace.enterPath` at the driver entry. -/
def decisionPath : List Located := DriverTrace.enterPath

/-- Empty calldata falls through the entry test into the direct return. -/
def bodyEntry (s : State) (input : ByteArray) (_i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 369
    stack := [UInt256.ofNat 0, Padding.paddedWord input] }

/-- Compression entry after the per-block setup.  The empty-input test runs
once at the driver entry, so this is already the compressor entry. -/
def legacyDispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 423
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 402,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

/-- Nonempty dispatcher target: checked first-block helper. -/
def nonemptyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 423
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 402,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

private def writeWord (memory : ByteArray) (offset : Nat)
    (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def emptyMemory (memory : ByteArray) : ByteArray :=
  let m0 := writeWord memory 0x220 h0
  let m1 := writeWord m0 0x240 h1
  let m2 := writeWord m1 0x260 h2
  let m3 := writeWord m2 0x280 h3
  writeWord m3 0x2a0 h4

def emptyActiveWords (s : State) : UInt256 :=
  let a0 := s.activeWordsAfterUInt256 0x220 32
  let a1 := UInt256.ofNat (MachineState.activeWordsAfter a0.toNat 0x240 32)
  let a2 := UInt256.ofNat (MachineState.activeWordsAfter a1.toNat 0x260 32)
  let a3 := UInt256.ofNat (MachineState.activeWordsAfter a2.toNat 0x280 32)
  UInt256.ofNat (MachineState.activeWordsAfter a3.toNat 0x2a0 32)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 402
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
    MachineState.readWord (emptyMemory memory) 0x220 = h0 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h1 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x240 = h1 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h2 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x260 = h2 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h3 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x280 = h3 := by
  unfold emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inl (by omega))]
  exact readWord_writeWord_same _ _ _

@[simp] private theorem emptyMemory_h4 (memory : ByteArray) :
    MachineState.readWord (emptyMemory memory) 0x2a0 = h4 := by
  unfold emptyMemory
  exact readWord_writeWord_same _ _ _

@[simp] theorem resultState_hashAt (s : State) (input : ByteArray) (i : Nat) :
    StackMemory.hashAt (resultState s input i).memory = emptyHash := by
  unfold StackMemory.hashAt resultState emptyHash
  rw [emptyMemory_h0, emptyMemory_h1, emptyMemory_h2, emptyMemory_h3,
    emptyMemory_h4]

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x2c0 ≤ address) :
    MachineState.readWord (resultState s input i).memory address =
      MachineState.readWord s.memory address := by
  unfold resultState emptyMemory
  rw [readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    readWord_writeWord_disjoint _ _ _ _ (Or.inr (by omega))]

theorem run_decision_empty (s : State) (input : ByteArray) (i : Nat)
    (hempty : input.size = 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock decisionPath
      (DriverTrace.setupEntry s input) = some (bodyEntry s input i) := by
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat input.size) := by
    simp [hempty, UInt256.isTrue]
  have hpc231 : Artifact.submissionArtifact.instructionPC 231 = 364 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc232 : Artifact.submissionArtifact.instructionPC 232 = 365 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc233 : Artifact.submissionArtifact.instructionPC 233 = 368 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [decisionPath, DriverTrace.enterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.setupEntry, bodyEntry, hcalldata, hrun, hempty, hfalse,
    hpc231, hpc232, hpc233,
    UInt256.isTrue, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

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

/-- Later blocks no longer re-test for empty calldata: the dispatcher state is
already the compressor entry. -/
def gasSteps_nonempty (s : State) (input : ByteArray) (i : Nat)
    (_hfit : CalldataFits input) (_hpositive : 0 < input.size)
    (_hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (_hfork : s.fork = .Osaka) (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (legacyDispatchEntry s input i)
      (nonemptyEntry s input i) :=
  GasSteps.refl _

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
