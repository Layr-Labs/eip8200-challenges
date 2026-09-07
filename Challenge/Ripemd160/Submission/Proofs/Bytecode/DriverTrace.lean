import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Certified post-padding block driver

The reference bytecode at instruction indices 719--733 walks the padded
message in 64-byte blocks.  This file certifies the loop mechanics while
leaving the compression call as an explicit `GasSteps` seam.  Consequently
the driver can be composed with a compression proof without depending on its
internal state representation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace

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

def callPath : List Located :=
  [⟨882, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨883, .push ⟨2, by decide⟩ (UInt256.ofNat 1060), by rfl, by decide⟩,
   ⟨884, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨885, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨886, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨887, .push ⟨2, by decide⟩ (UInt256.ofNat 4915), by rfl, by decide⟩,
   ⟨888, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def postCheckPath : List Located :=
  [⟨874, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨875, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨876, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨877, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨878, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨879, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨880, .push ⟨2, by decide⟩ (UInt256.ofNat 4729), by rfl, by decide⟩,
   ⟨881, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pc785 : Artifact.submissionArtifact.instructionPC 874 = 0x424 := by decide
@[simp] private theorem pc786 : Artifact.submissionArtifact.instructionPC 875 = 0x425 := by decide
@[simp] private theorem pc787 : Artifact.submissionArtifact.instructionPC 876 = 0x427 := by decide
@[simp] private theorem pc788 : Artifact.submissionArtifact.instructionPC 877 = 0x428 := by decide
@[simp] private theorem pc789 : Artifact.submissionArtifact.instructionPC 878 = 0x429 := by decide
@[simp] private theorem pc790 : Artifact.submissionArtifact.instructionPC 879 = 0x42a := by decide
@[simp] private theorem pc791 : Artifact.submissionArtifact.instructionPC 880 = 0x42b := by decide
@[simp] private theorem pc792 : Artifact.submissionArtifact.instructionPC 881 = 0x42e := by decide
@[simp] private theorem pc793 : Artifact.submissionArtifact.instructionPC 882 = 0x42f := by decide
@[simp] private theorem pc794 : Artifact.submissionArtifact.instructionPC 883 = 0x430 := by decide
@[simp] private theorem pc795 : Artifact.submissionArtifact.instructionPC 884 = 0x433 := by decide
@[simp] private theorem pc796 : Artifact.submissionArtifact.instructionPC 885 = 0x434 := by decide
@[simp] private theorem pc797 : Artifact.submissionArtifact.instructionPC 886 = 0x437 := by decide
@[simp] private theorem pc798 : Artifact.submissionArtifact.instructionPC 887 = 0x438 := by decide
@[simp] private theorem pc799 : Artifact.submissionArtifact.instructionPC 888 = 0x43b := by decide

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

def setupEntry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x42f
    stack := [UInt256.ofNat 0, Padding.paddedWord input] }

def loopAt (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x42f
    stack := [blockOffsetWord i, Padding.paddedWord input] }

/-- State at the appended empty-input dispatcher. Its stack matches the
ordinary compression entry stack. -/
def dispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x1333
    stack := [messageOffsetWord i, UInt256.ofNat 0x424,
      blockOffsetWord i, Padding.paddedWord input] }

/-- State at the compression entry point. The helper receives the concrete
padded-message pointer, its return destination, and the driver invariant
stack underneath. -/
def compressEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x43c
    stack := [messageOffsetWord i, UInt256.ofNat 0x424,
      blockOffsetWord i, Padding.paddedWord input] }

/-- Normalize an arbitrary post-compression state to the driver's return seam. -/
def compressReturned (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 0x424
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterIteration (s : State) (input : ByteArray) (i : Nat) : State :=
  loopAt s input (i + 1)

def afterExit (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 0x1279
    stack := [blockOffsetWord (blockCount input), Padding.paddedWord input] }

def iterationEnd (s : State) (input : ByteArray) (i : Nat) : State :=
  if i + 1 = blockCount input then afterExit s input else loopAt s input (i + 1)

theorem paddedLength_eq_blockCount (input : ByteArray) :
    Padding.paddedLength input.size = blockCount input * 64 := by
  exact Padding.paddedLength_eq_blocks input.size

/-- RIPEMD padding always contributes at least one block.  The driver may
therefore enter the compression call before performing its first completion
test. -/
theorem blockCount_pos (input : ByteArray) : 0 < blockCount input := by
  have hpad := Padding.paddedLength_pos input.size
  have heq := paddedLength_eq_blockCount input
  unfold blockCount at *
  omega

private theorem paddedLength_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    Padding.paddedLength input.size < 2 ^ 256 := by
  have hlt := Padding.paddedLength_lt input.size
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num at hfit ⊢
  omega

private theorem blockOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i ≤ blockCount input) : blockOffset i < 2 ^ 256 := by
  have hpadded := paddedLength_lt_uint256 input hfit
  have heq := paddedLength_eq_blockCount input
  unfold blockOffset
  omega

private theorem messageOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    Padding.messageOffset + blockOffset i < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hoff : blockOffset i < Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num [Padding.messageOffset] at hfit ⊢
  omega

private theorem offset_ne_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    UInt256.eq (blockOffsetWord i) (Padding.paddedWord input) = 0 := by
  have hoff := blockOffset_lt_uint256 input hfit i (Nat.le_of_lt hi)
  have hpad := paddedLength_lt_uint256 input hfit
  have hnat : blockOffset i ≠ Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    unfold blockOffset
    omega
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.eq blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad]
  simp only [if_neg hnat]
  rfl

private theorem offset_eq_total (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) :
    UInt256.eq (blockOffsetWord (blockCount input))
      (Padding.paddedWord input) = UInt256.ofNat 1 := by
  have hoff := blockOffset_lt_uint256 input hfit (blockCount input) (by omega)
  have hpad := paddedLength_lt_uint256 input hfit
  have heq : blockOffset (blockCount input) =
      Padding.paddedLength input.size := by
    rw [paddedLength_eq_blockCount input]
    rfl
  rw [Padding.paddedWord_eq input hfit]
  unfold UInt256.eq blockOffsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hpad, heq]
  simp only [if_pos rfl]
  rfl

/-- The driver's concrete pointer selects block `i` of the padded message. -/
theorem padReturned_messageBlockAt (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ScheduleCorrect.MessageBlockAt (PaddingTrace.padReturned input).memory
      (messageOffsetWord i) (Padding.paddedMessage input) (blockOffset i) := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexAt input hfit i hi

/-- The same block pointer is separated from the dense schedule scratch. -/
theorem padReturned_blockSeparated (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input) :
    ∀ k, k < 16 →
      0x2e0 ≤ (Schedule.loadOffsetWord (messageOffsetWord i) k).toNat := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi

theorem run_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath
      (loopAt s input i) = some (dispatchEntry s input i) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (messageOffset_lt_uint256 input hfit i hi)
  have hdest : Decode.isValidJumpDest submissionBytecode 0x1333 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3201 (by rfl)
  simp [callPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, dispatchEntry, messageOffsetWord, blockOffsetWord,
    hcode, hrun, hadd, hdest]

private theorem incrementedOffset (_input : ByteArray) (i : Nat)
    (hoff : blockOffset (i + 1) < 2 ^ 256)
    : UInt256.ofNat 64 + blockOffsetWord i = blockOffsetWord (i + 1) := by
  have haddBound : i * 64 + 64 < 2 ^ 256 := by
    simpa [blockOffset, Nat.add_mul] using hoff
  have hadd : blockOffsetWord i + UInt256.ofNat 64 =
      blockOffsetWord (i + 1) := by
    simpa [blockOffsetWord, blockOffset, Nat.add_mul] using
      Challenge.EvmProof.Word.ofNat_add_ofNat
        (a := i * 64) (b := 64) haddBound
  rw [show UInt256.ofNat 64 + blockOffsetWord i =
    blockOffsetWord i + UInt256.ofNat 64 from
      Challenge.EvmProof.Word.word_add_comm _ _]
  exact hadd

theorem run_postCheck_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i + 1 < blockCount input)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock postCheckPath
      (compressReturned s input i) = some (loopAt s input (i + 1)) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  have hadd := incrementedOffset input i hoff
  have heq := offset_ne_total input hfit (i + 1) hi
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [postCheckPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, loopAt, hrun, hadd, heq, hfalse]

theorem run_postCheck_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hlast : i + 1 = blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock postCheckPath
      (compressReturned s input i) = some (afterExit s input) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  have hadd := incrementedOffset input i hoff
  have heq := offset_eq_total input hfit
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (1 : UInt256) = 1 := by decide
  have hdest : Decode.isValidJumpDest submissionBytecode 0x1279 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3151 (by rfl)
  simp [postCheckPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, afterExit, hrun, hcode, hadd, hlast, heq,
    htrue, honeNat, UInt256.isTrue, hdest]

private def gasStepsBlock (path : List Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

def gasSteps_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopAt s input i) (dispatchEntry s input i) :=
  gasStepsBlock callPath _ _ hcode hfork
    (run_call s input hfit i hi hcode hrun) hrun hnp

def gasSteps_postCheck_continue (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i + 1 < blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressReturned s input i)
      (loopAt s input (i + 1)) :=
  gasStepsBlock postCheckPath _ _ hcode hfork
    (run_postCheck_continue s input hfit i hi hrun) hrun hnp

def gasSteps_postCheck_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hlast : i + 1 = blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (compressReturned s input i)
      (afterExit s input) :=
  gasStepsBlock postCheckPath _ _ hcode hfork
    (run_postCheck_exit s input hfit i hlast hcode hrun) hrun hnp

/-- One complete driver iteration, parameterized by the compression proof. -/
def gasSteps_iteration_of_compress (s next : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (hcodeS : s.executionEnv.code = submissionBytecode)
    (hforkS : s.fork = .Osaka) (hrunS : s.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcodeNext : next.executionEnv.code = submissionBytecode)
    (hforkNext : next.fork = .Osaka) (hrunNext : next.halt = .Running)
    (hnpNext : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig next.executionEnv.fork
      next.executionEnv.codeAddr = false)
    (hcompress : Challenge.EvmProof.GasSteps (dispatchEntry s input i)
      (compressReturned next input i)) :
    Challenge.EvmProof.GasSteps (loopAt s input i)
      (iterationEnd next input i) := by
  have gcall := gasSteps_call s input hfit i hi hcodeS hforkS hrunS hnpS
  by_cases hlast : i + 1 = blockCount input
  · have gexit := gasSteps_postCheck_exit next input hfit i hlast hcodeNext
      hforkNext hrunNext hnpNext
    exact Challenge.EvmProof.GasSteps.cast
      (gcall.trans (hcompress.trans gexit)) rfl (by simp [iterationEnd, hlast])
  · have hnext : i + 1 < blockCount input := by omega
    have gcheck := gasSteps_postCheck_continue next input hfit i hnext hcodeNext
      hforkNext hrunNext hnpNext
    exact Challenge.EvmProof.GasSteps.cast
      (gcall.trans (hcompress.trans gcheck)) rfl
      (by simp [iterationEnd, hlast])

/-- Iterate the driver over all padded blocks, given a state invariant family
and one compression certificate at each block. -/
def gasSteps_loop_of_compress (states : Nat → State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : ∀ i, i ≤ blockCount input →
      (states i).executionEnv.code = submissionBytecode)
    (hfork : ∀ i, i ≤ blockCount input → (states i).fork = .Osaka)
    (hrun : ∀ i, i ≤ blockCount input → (states i).halt = .Running)
    (hnp : ∀ i, i ≤ blockCount input →
      Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
        (states i).executionEnv.codeAddr = false)
    (hcompress : ∀ i, i < blockCount input →
      Challenge.EvmProof.GasSteps (dispatchEntry (states i) input i)
        (compressReturned (states (i + 1)) input i)) :
    Challenge.EvmProof.GasSteps (loopAt (states 0) input 0)
      (afterExit (states (blockCount input)) input) := by
  let I := fun i =>
    if i = blockCount input then afterExit (states i) input
    else loopAt (states i) input i
  have hall : Challenge.EvmProof.GasSteps (I 0) (I (blockCount input)) := by
    apply Challenge.EvmProof.GasSteps.iterateBounded
      (I := I) (count := blockCount input)
    intro i hi
    have gi := gasSteps_iteration_of_compress (states i) (states (i + 1))
      input hfit i hi (hcode i (by omega)) (hfork i (by omega))
      (hrun i (by omega)) (hnp i (by omega)) (hcode (i + 1) (by omega))
      (hfork (i + 1) (by omega)) (hrun (i + 1) (by omega))
      (hnp (i + 1) (by omega)) (hcompress i hi)
    exact Challenge.EvmProof.GasSteps.cast gi
      (by simp [I, Nat.ne_of_lt hi])
      (by simp [I, iterationEnd])
  have hpositive := blockCount_pos input
  exact Challenge.EvmProof.GasSteps.cast hall
    (by simp [I, Nat.ne_of_lt hpositive]) (by simp [I])

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
