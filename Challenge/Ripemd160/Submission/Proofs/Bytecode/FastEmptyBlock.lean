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
  [⟨2779, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2780, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2781, .push ⟨2, by decide⟩ (UInt256.ofNat 0x519), by rfl, by decide⟩,
   ⟨2782, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def bodyPath : List Located :=
  [⟨2783, .push ⟨4, by decide⟩ h0, by rfl, by decide⟩,
   ⟨2784, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨2785, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2786, .push ⟨4, by decide⟩ h1, by rfl, by decide⟩,
   ⟨2787, .push ⟨1, by decide⟩ (UInt256.ofNat 0x40), by rfl, by decide⟩,
   ⟨2788, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2789, .push ⟨4, by decide⟩ h2, by rfl, by decide⟩,
   ⟨2790, .push ⟨1, by decide⟩ (UInt256.ofNat 0x60), by rfl, by decide⟩,
   ⟨2791, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2792, .push ⟨4, by decide⟩ h3, by rfl, by decide⟩,
   ⟨2793, .push ⟨1, by decide⟩ (UInt256.ofNat 0x80), by rfl, by decide⟩,
   ⟨2794, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2795, .push ⟨4, by decide⟩ h4, by rfl, by decide⟩,
   ⟨2796, .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0), by rfl, by decide⟩,
   ⟨2797, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2798, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2799, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bodyEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x12e7
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
      DriverTrace.blockOffsetWord i, Padding.paddedWord input] }

/-- Entry state for the original empty-input dispatcher.  The outer exact-input
dispatcher falls back to this address without changing the compressor stack. -/
def legacyDispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x12e1
    stack := [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
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

def emptyActiveWords (s : State) : UInt256 :=
  let a0 := s.activeWordsAfterUInt256 0x20 32
  let a1 := UInt256.ofNat (MachineState.activeWordsAfter a0.toNat 0x40 32)
  let a2 := UInt256.ofNat (MachineState.activeWordsAfter a1.toNat 0x60 32)
  let a3 := UInt256.ofNat (MachineState.activeWordsAfter a2.toNat 0x80 32)
  UInt256.ofNat (MachineState.activeWordsAfter a3.toNat 0xa0 32)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x436
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
    (haddress : 0x4a0 ≤ address) :
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
        some (DriverTrace.compressEntry s input i) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hmod : input.size % 2 ^ 256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hsize]
    omega
  norm_num at hmod
  have htrue : UInt256.isTrue (UInt256.ofNat input.size) := by
    exact hmod
  have hdest : Decode.isValidJumpDest submissionBytecode 0x519 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 913 (by rfl)
  have hpc2779 : Artifact.submissionArtifact.instructionPC 2779 = 0x12e1 := by rfl
  have hpc2780 : Artifact.submissionArtifact.instructionPC 2780 = 0x12e2 := by rfl
  have hpc2781 : Artifact.submissionArtifact.instructionPC 2781 = 0x12e3 := by rfl
  have hpc2782 : Artifact.submissionArtifact.instructionPC 2782 = 0x12e6 := by rfl
  simp [decisionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    legacyDispatchEntry, DriverTrace.compressEntry, hcalldata, hcode,
    hrun, hmod, htrue, hdest, hpc2779, hpc2780, hpc2781, hpc2782, UInt256.isTrue,
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
  have hpc2779 : Artifact.submissionArtifact.instructionPC 2779 = 0x12e1 := by rfl
  have hpc2780 : Artifact.submissionArtifact.instructionPC 2780 = 0x12e2 := by rfl
  have hpc2781 : Artifact.submissionArtifact.instructionPC 2781 = 0x12e3 := by rfl
  have hpc2782 : Artifact.submissionArtifact.instructionPC 2782 = 0x12e6 := by rfl
  simp [decisionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    legacyDispatchEntry, bodyEntry, hcalldata, hrun, hempty, hfalse,
    hpc2779, hpc2780, hpc2781, hpc2782,
    UInt256.isTrue, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_body (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodyPath (bodyEntry s input i) =
      some (resultState s input i) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x436 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 717 (by rfl)
  have hpc2783 : Artifact.submissionArtifact.instructionPC 2783 = 0x12e7 := by rfl
  have hpc2784 : Artifact.submissionArtifact.instructionPC 2784 = 0x12ec := by rfl
  have hpc2785 : Artifact.submissionArtifact.instructionPC 2785 = 0x12ee := by rfl
  have hpc2786 : Artifact.submissionArtifact.instructionPC 2786 = 0x12ef := by rfl
  have hpc2787 : Artifact.submissionArtifact.instructionPC 2787 = 0x12f4 := by rfl
  have hpc2788 : Artifact.submissionArtifact.instructionPC 2788 = 0x12f6 := by rfl
  have hpc2789 : Artifact.submissionArtifact.instructionPC 2789 = 0x12f7 := by rfl
  have hpc2790 : Artifact.submissionArtifact.instructionPC 2790 = 0x12fc := by rfl
  have hpc2791 : Artifact.submissionArtifact.instructionPC 2791 = 0x12fe := by rfl
  have hpc2792 : Artifact.submissionArtifact.instructionPC 2792 = 0x12ff := by rfl
  have hpc2793 : Artifact.submissionArtifact.instructionPC 2793 = 0x1304 := by rfl
  have hpc2794 : Artifact.submissionArtifact.instructionPC 2794 = 0x1306 := by rfl
  have hpc2795 : Artifact.submissionArtifact.instructionPC 2795 = 0x1307 := by rfl
  have hpc2796 : Artifact.submissionArtifact.instructionPC 2796 = 0x130c := by rfl
  have hpc2797 : Artifact.submissionArtifact.instructionPC 2797 = 0x130e := by rfl
  have hpc2798 : Artifact.submissionArtifact.instructionPC 2798 = 0x130f := by rfl
  have hpc2799 : Artifact.submissionArtifact.instructionPC 2799 = 0x1310 := by rfl
  simp (config := { maxSteps := 300000 })
    [bodyPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, emptyMemory, emptyActiveWords, writeWord,
      h0, h1, h2, h3, h4, hcode, hrun, hdest,
      hpc2783, hpc2784, hpc2785, hpc2786, hpc2787, hpc2788, hpc2789,
      hpc2790, hpc2791, hpc2792, hpc2793, hpc2794, hpc2795, hpc2796,
      hpc2797, hpc2798, hpc2799,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

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
      (DriverTrace.compressEntry s input i) :=
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
  have gbody := gasStepsBlock bodyPath (bodyEntry s input i)
    (resultState s input i) (by simpa [bodyEntry] using hcode)
    (by simpa [bodyEntry, State.fork] using hfork)
    (run_body s input i hcode hrun) (by simpa [bodyEntry] using hrun)
    (by simpa [bodyEntry] using hnp)
  exact gdecision.trans gbody

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
