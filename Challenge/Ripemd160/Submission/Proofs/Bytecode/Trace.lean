import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Ops
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Reference-artifact trace helpers

These lemmas install structural decoder certificates in arbitrary symbolic
states and normalize program-counter movement by instruction index.  They are
the small reference-specific adapter over the submission-generic direct-bytecode
artifact and opcode libraries.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace

open EvmSemantics
open EvmSemantics.EVM

theorem pcBound (index : Nat) : Artifact.instructionPC index < 2 ^ 256 := by
  have hle := Challenge.EvmProof.ProgramArtifact.instructionPC_le_code_size
    Artifact.submissionArtifact index
  change Artifact.instructionPC index ≤ submissionBytecode.size at hle
  rw [referenceBytecode_size] at hle
  omega

theorem pcToNat {s : State} {index : Nat}
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index)) :
    s.pc.toNat = Artifact.instructionPC index := by
  rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (pcBound index)]

theorem decodedOpAt (s : State) (index : Nat) (op : Operation)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.submissionInstructions[index]? = some (.op op))
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork s.fork = true) :
    s.decodedOp = some op := by
  apply Challenge.EvmProof.ProgramArtifact.state_decodedOp_of
    Artifact.submissionArtifact s index
    (by simpa [Artifact.submissionArtifact] using hcode) (pcToNat hpc) op none
  · exact Artifact.submissionArtifact.decodeAt_op_index index op hget hopcode hplain
  · exact havailable

theorem decodedPushAt (s : State) (index : Nat) (width : Fin 33)
    (value : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.submissionInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val)
    (havailable : (Operation.Push ⟨width⟩).availableInFork s.fork = true) :
    s.decoded = some (.Push ⟨width⟩, some (value, width.val)) := by
  apply Challenge.EvmProof.ProgramArtifact.state_decoded_of
    Artifact.submissionArtifact s index
    (by simpa [Artifact.submissionArtifact] using hcode) (pcToNat hpc)
    (.Push ⟨width⟩) (some (value, width.val))
  · exact Artifact.submissionArtifact.decodeAt_push_index index width value hget hfit
  · exact havailable

theorem decodedPushOpAt (s : State) (index : Nat) (width : Fin 33)
    (value : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.submissionInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val)
    (havailable : (Operation.Push ⟨width⟩).availableInFork s.fork = true) :
    s.decodedOp = some (.Push ⟨width⟩) := by
  unfold State.decodedOp
  rw [decodedPushAt s index width value hcode hpc hget hfit havailable]
  rfl


theorem validJumpDestAt (index : Nat)
    (hget : Artifact.submissionInstructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest submissionBytecode
      (UInt256.ofNat (Artifact.instructionPC index)).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (pcBound index)]
  exact Artifact.submissionArtifact.isValidJumpDest_index index hget

theorem succPC {index : Nat}
    (hnext : Artifact.instructionPC (index + 1) =
      Artifact.instructionPC index + 1) :
    (UInt256.ofNat (Artifact.instructionPC index)).succ =
      UInt256.ofNat (Artifact.instructionPC (index + 1)) := by
  rw [Challenge.EvmProof.Word.succ_ofNat (by
    have := pcBound (index + 1)
    omega), hnext]

theorem pushPC {index width : Nat}
    (hnext : Artifact.instructionPC (index + 1) =
      Artifact.instructionPC index + (width + 1)) :
    UInt256.ofNat (Artifact.instructionPC index) + UInt256.ofNat (width + 1) =
      UInt256.ofNat (Artifact.instructionPC (index + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by
    have := pcBound (index + 1)
    omega), hnext]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
