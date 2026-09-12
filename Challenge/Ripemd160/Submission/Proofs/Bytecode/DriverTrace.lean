import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Certified post-padding block driver

The driver walks the padded message in 64-byte blocks: the entry at pc 364
tests for empty calldata once, the block setup at pc 413 calls the compressor,
and the post-check at pc 402 advances the block pointer.  This file certifies the loop mechanics while
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
  [⟨309, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨310, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨311, .push ⟨6, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨312, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The block post-check.  The compressor's stack cleanup falls straight into
it (no return address, no `JUMP`); unfinished blocks jump back to the block
setup at pc 506 and the last block falls through into the finaliser. -/
def postCheckPath : List Located :=
  [⟨3973, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨3974, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3975, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3976, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3977, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3978, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3979, .push ⟨2, by decide⟩ (UInt256.ofNat 506), by rfl, by decide⟩,
   ⟨3980, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- The one-time unconditional jump to the first block setup. -/
def enterPath : List Located :=
  [⟨234, .push ⟨2, by decide⟩ (UInt256.ofNat 506), by rfl, by decide⟩,
   ⟨235, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pcD236 : Artifact.submissionArtifact.instructionPC 234 = 368 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD237 : Artifact.submissionArtifact.instructionPC 235 = 371 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD238 : Artifact.submissionArtifact.instructionPC 236 = 372 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD239 : Artifact.submissionArtifact.instructionPC 237 = 373 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD312 : Artifact.submissionArtifact.instructionPC 309 = 506 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD313 : Artifact.submissionArtifact.instructionPC 310 = 507 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD314 : Artifact.submissionArtifact.instructionPC 311 = 508 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD315 : Artifact.submissionArtifact.instructionPC 312 = 515 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD316 : Artifact.submissionArtifact.instructionPC 313 = 516 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3981 : Artifact.submissionArtifact.instructionPC 3973 = 4707 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3982 : Artifact.submissionArtifact.instructionPC 3974 = 4709 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3983 : Artifact.submissionArtifact.instructionPC 3975 = 4710 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3984 : Artifact.submissionArtifact.instructionPC 3976 = 4711 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3985 : Artifact.submissionArtifact.instructionPC 3977 = 4712 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3986 : Artifact.submissionArtifact.instructionPC 3978 = 4713 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3987 : Artifact.submissionArtifact.instructionPC 3979 = 4714 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3988 : Artifact.submissionArtifact.instructionPC 3980 = 4717 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem pcD3989 : Artifact.submissionArtifact.instructionPC 3981 = 4718 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

def setupEntry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 368
    stack := [UInt256.ofNat 0, Padding.paddedWord input] }

def loopAt (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 506
    stack := [blockOffsetWord i, Padding.paddedWord input] }

/-- State after the block setup.  The empty-input test now runs once at the
driver entry, so this coincides with the compression entry. -/
def dispatchEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 516
    stack := [messageOffsetWord i,
      blockOffsetWord i, Padding.paddedWord input] }

/-- State at the compression entry point. The helper receives the concrete
padded-message pointer and the driver invariant stack underneath; its stack
cleanup falls through into the post-check. -/
def compressEntry (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 516
    stack := [messageOffsetWord i,
      blockOffsetWord i, Padding.paddedWord input] }

/-- Normalize an arbitrary post-compression state to the driver's return seam. -/
def compressReturned (s : State) (input : ByteArray) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 4707
    stack := [blockOffsetWord i, Padding.paddedWord input] }

def afterIteration (s : State) (input : ByteArray) (i : Nat) : State :=
  loopAt s input (i + 1)

def afterExit (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 4718
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
      0x400 ≤ (Schedule.loadOffsetWord (messageOffsetWord i) k).toNat := by
  simpa [messageOffsetWord, blockOffset, blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi

theorem run_call (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i < blockCount input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock callPath
      (loopAt s input i) = some (dispatchEntry s input i) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (messageOffset_lt_uint256 input hfit i hi)
  simp [callPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, dispatchEntry, messageOffsetWord, blockOffsetWord,
    hrun, hadd]

theorem run_enter (s : State) (input : ByteArray)
    (_hfit : Challenge.Ripemd160.CalldataFits input) (_hpositive : 0 < input.size)
    (_hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock enterPath
      (setupEntry s input) = some (loopAt s input 0) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 506 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 309 (by rfl)
    rw [pcD312] at h
    exact h
  simp [enterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    setupEntry, loopAt, blockOffsetWord, blockOffset, hcode,
    hrun, hdest, UInt256.isTrue,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

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
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock postCheckPath
      (compressReturned s input i) = some (loopAt s input (i + 1)) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  have hadd := incrementedOffset input i hoff
  have heq := offset_ne_total input hfit (i + 1) hi
  have hz : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (UInt256.ofNat 506) = 506 := by decide
  have hdest : Decode.isValidJumpDest submissionBytecode 506 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 309 (by rfl)
    rw [pcD312] at h
    exact h
  simp [postCheckPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, loopAt, hrun, hcode, hadd, heq, hz, htrue, honeNat,
    UInt256.isTrue, hdest]

theorem run_postCheck_exit (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hlast : i + 1 = blockCount input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock postCheckPath
      (compressReturned s input i) = some (afterExit s input) := by
  have hoff := blockOffset_lt_uint256 input hfit (i + 1) (by omega)
  have hadd := incrementedOffset input i hoff
  have heq := offset_eq_total input hfit
  have hz : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [postCheckPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressReturned, afterExit, hrun, hadd, hlast, heq, hz, hfalse]

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

/-- The one-time empty-input test at the driver entry, for nonempty calldata. -/
def gasSteps_enter (s : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (hpositive : 0 < input.size)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (setupEntry s input) (loopAt s input 0) :=
  gasStepsBlock enterPath _ _ hcode hfork
    (run_enter s input hfit hpositive hcalldata hcode hrun) hrun hnp

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
    (run_postCheck_continue s input hfit i hi hcode hrun) hrun hnp

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


/-- One dispatcher execution that consumes two blocks (the depth-2 prefix
ladder): the call, the two-block certificate, then the post-check for
block 1. -/
def gasSteps_iteration2_of_compress (s next : State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (h1 : 1 < blockCount input)
    (hcodeS : s.executionEnv.code = submissionBytecode)
    (hforkS : s.fork = .Osaka) (hrunS : s.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcodeNext : next.executionEnv.code = submissionBytecode)
    (hforkNext : next.fork = .Osaka) (hrunNext : next.halt = .Running)
    (hnpNext : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig next.executionEnv.fork
      next.executionEnv.codeAddr = false)
    (hcompress : Challenge.EvmProof.GasSteps (dispatchEntry s input 0)
      (compressReturned next input 1)) :
    Challenge.EvmProof.GasSteps (loopAt s input 0)
      (iterationEnd next input 1) := by
  have gcall := gasSteps_call s input hfit 0 (by omega) hcodeS hforkS hrunS hnpS
  by_cases hlast : 1 + 1 = blockCount input
  · have gexit := gasSteps_postCheck_exit next input hfit 1 hlast hcodeNext
      hforkNext hrunNext hnpNext
    exact Challenge.EvmProof.GasSteps.cast
      (gcall.trans (hcompress.trans gexit)) rfl (by simp [iterationEnd, hlast])
  · have hnext : 1 + 1 < blockCount input := by omega
    have gcheck := gasSteps_postCheck_continue next input hfit 1 hnext hcodeNext
      hforkNext hrunNext hnpNext
    exact Challenge.EvmProof.GasSteps.cast
      (gcall.trans (hcompress.trans gcheck)) rfl
      (by simp [iterationEnd, hlast])

/-- Iterate the driver from block `start` to the exit, one block per
dispatcher execution. -/
def gasSteps_loop_from (states : Nat → State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hcode : ∀ i, i ≤ blockCount input →
      (states i).executionEnv.code = submissionBytecode)
    (hfork : ∀ i, i ≤ blockCount input → (states i).fork = .Osaka)
    (hrun : ∀ i, i ≤ blockCount input → (states i).halt = .Running)
    (hnp : ∀ i, i ≤ blockCount input →
      Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
        (states i).executionEnv.codeAddr = false)
    (start : Nat) (hstart : start ≤ blockCount input)
    (hcompress : ∀ i, start ≤ i → i < blockCount input →
      Challenge.EvmProof.GasSteps (dispatchEntry (states i) input i)
        (compressReturned (states (i + 1)) input i)) :
    Challenge.EvmProof.GasSteps
      (if start = blockCount input then afterExit (states start) input
        else loopAt (states start) input start)
      (afterExit (states (blockCount input)) input) := by
  let I := fun i =>
    if i = blockCount input then afterExit (states i) input
    else loopAt (states i) input i
  let J := fun j => I (start + j)
  have hall : Challenge.EvmProof.GasSteps (J 0) (J (blockCount input - start)) := by
    apply Challenge.EvmProof.GasSteps.iterateBounded
      (I := J) (count := blockCount input - start)
    intro j hj
    have hi : start + j < blockCount input := by omega
    have gi := gasSteps_iteration_of_compress (states (start + j)) (states (start + j + 1))
      input hfit (start + j) hi (hcode _ (by omega)) (hfork _ (by omega))
      (hrun _ (by omega)) (hnp _ (by omega)) (hcode _ (by omega))
      (hfork _ (by omega)) (hrun _ (by omega))
      (hnp _ (by omega)) (hcompress (start + j) (by omega) hi)
    exact Challenge.EvmProof.GasSteps.cast gi
      (by simp [J, I, Nat.ne_of_lt hi])
      (by simp [J, I, iterationEnd, Nat.add_assoc])
  have hend : start + (blockCount input - start) = blockCount input := by omega
  exact Challenge.EvmProof.GasSteps.cast hall (by simp [J, I]) (by simp [J, I, hend])

/-- Iterate the driver over all padded blocks.  When `double` is set, the
first dispatcher execution consumes blocks 0 and 1 together. -/
def gasSteps_loop_of_compress_double (states : Nat → State) (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (double : Bool)
    (hcode : ∀ i, i ≤ blockCount input →
      (states i).executionEnv.code = submissionBytecode)
    (hfork : ∀ i, i ≤ blockCount input → (states i).fork = .Osaka)
    (hrun : ∀ i, i ≤ blockCount input → (states i).halt = .Running)
    (hnp : ∀ i, i ≤ blockCount input →
      Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig (states i).executionEnv.fork
        (states i).executionEnv.codeAddr = false)
    (hcompress : ∀ i, i < blockCount input → (double = true → 2 ≤ i) →
      Challenge.EvmProof.GasSteps (dispatchEntry (states i) input i)
        (compressReturned (states (i + 1)) input i))
    (hdoubleBlocks : double = true → 2 ≤ blockCount input)
    (hdoubleTrace : double = true →
      Challenge.EvmProof.GasSteps (dispatchEntry (states 0) input 0)
        (compressReturned (states 2) input 1)) :
    Challenge.EvmProof.GasSteps (loopAt (states 0) input 0)
      (afterExit (states (blockCount input)) input) := by
  have hpositive := blockCount_pos input
  cases double with
  | false =>
    have h := gasSteps_loop_from states input hfit hcode hfork hrun hnp 0 (Nat.zero_le _)
      (fun i _ hi => hcompress i hi (fun h => absurd h (by decide)))
    exact Challenge.EvmProof.GasSteps.cast h (by simp [Nat.ne_of_lt hpositive]) rfl
  | true =>
    have h2 := hdoubleBlocks rfl
    have g2 := hdoubleTrace rfl
    have gfirst := gasSteps_iteration2_of_compress (states 0) (states 2) input hfit (by omega)
      (hcode 0 (by omega)) (hfork 0 (by omega)) (hrun 0 (by omega)) (hnp 0 (by omega))
      (hcode 2 h2) (hfork 2 h2) (hrun 2 h2) (hnp 2 h2) g2
    have hrest := gasSteps_loop_from states input hfit hcode hfork hrun hnp 2 h2
      (fun i hi2 hi => hcompress i hi (fun _ => hi2))
    exact gfirst.trans (Challenge.EvmProof.GasSteps.cast hrest (by simp [iterationEnd]) rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
