import Challenge.Sha256.RouteB.Artifact
import Challenge.RouteB.Ops
import Challenge.RouteB.Word
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Reference-artifact trace helpers

These lemmas install structural decoder certificates in arbitrary symbolic
states and normalize program-counter movement by instruction index.  They are
the small reference-specific adapter over the submission-generic Route B
artifact and opcode libraries.
-/

namespace Challenge.Sha256.RouteB.Trace

open EvmSemantics
open EvmSemantics.EVM

theorem pcBound (index : Nat) : Artifact.instructionPC index < 2 ^ 256 := by
  have hle := Challenge.RouteB.ProgramArtifact.instructionPC_le_code_size
    Artifact.referenceArtifact index
  change Artifact.instructionPC index ≤ referenceBytecode.size at hle
  rw [referenceBytecode_size] at hle
  omega

theorem pcToNat {s : State} {index : Nat}
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index)) :
    s.pc.toNat = Artifact.instructionPC index := by
  rw [hpc, Challenge.RouteB.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (pcBound index)]

theorem decodedOpAt (s : State) (index : Nat) (op : Operation)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.referenceInstructions[index]? = some (.op op))
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork s.fork = true) :
    s.decodedOp = some op := by
  apply Challenge.RouteB.ProgramArtifact.state_decodedOp_of
    Artifact.referenceArtifact s index
    (by simpa [Artifact.referenceArtifact] using hcode) (pcToNat hpc) op none
  · exact Artifact.decodeAt_op_index index op hget hopcode hplain
  · exact havailable

theorem decodedPushAt (s : State) (index : Nat) (width : Fin 33)
    (value : UInt256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.referenceInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val)
    (havailable : (Operation.Push ⟨width⟩).availableInFork s.fork = true) :
    s.decoded = some (.Push ⟨width⟩, some (value, width.val)) := by
  apply Challenge.RouteB.ProgramArtifact.state_decoded_of
    Artifact.referenceArtifact s index
    (by simpa [Artifact.referenceArtifact] using hcode) (pcToNat hpc)
    (.Push ⟨width⟩) (some (value, width.val))
  · exact Artifact.decodeAt_push_index index width value hget hfit
  · exact havailable

theorem decodedPushOpAt (s : State) (index : Nat) (width : Fin 33)
    (value : UInt256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC index))
    (hget : Artifact.referenceInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val)
    (havailable : (Operation.Push ⟨width⟩).availableInFork s.fork = true) :
    s.decodedOp = some (.Push ⟨width⟩) := by
  unfold State.decodedOp
  rw [decodedPushAt s index width value hcode hpc hget hfit havailable]
  rfl


theorem validJumpDestAt (index : Nat)
    (hget : Artifact.referenceInstructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest referenceBytecode
      (UInt256.ofNat (Artifact.instructionPC index)).toNat = true := by
  rw [Challenge.RouteB.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (pcBound index)]
  exact Artifact.isValidJumpDest_index index hget

theorem succPC {index : Nat}
    (hnext : Artifact.instructionPC (index + 1) =
      Artifact.instructionPC index + 1) :
    (UInt256.ofNat (Artifact.instructionPC index)).succ =
      UInt256.ofNat (Artifact.instructionPC (index + 1)) := by
  rw [Challenge.RouteB.Word.succ_ofNat (by
    have := pcBound (index + 1)
    omega), hnext]

theorem pushPC {index width : Nat}
    (hnext : Artifact.instructionPC (index + 1) =
      Artifact.instructionPC index + (width + 1)) :
    UInt256.ofNat (Artifact.instructionPC index) + UInt256.ofNat (width + 1) =
      UInt256.ofNat (Artifact.instructionPC (index + 1)) := by
  rw [Challenge.RouteB.Word.ofNat_add_ofNat (by
    have := pcBound (index + 1)
    omega), hnext]

end Challenge.Sha256.RouteB.Trace
