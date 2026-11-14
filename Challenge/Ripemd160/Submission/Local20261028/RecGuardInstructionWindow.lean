import Challenge.Ripemd160.Submission.Local20261028.ColdArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InstructionWindow
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.GuardInstructionWindow
open EvmSemantics YulEvmCompiler Challenge.EvmProof ArtifactByteLength
open Control.Artifact (op)
def tail : List Instr := [
  .push ⟨3, by decide⟩ (UInt256.ofNat 6382179),
  .push ⟨1, by decide⟩ (UInt256.ofNat 229),
  .op .SHL,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .CALLDATALOAD,
  .op .CALLDATASIZE,
  .op .SAR,
  .op .XOR,
  .push ⟨2, by decide⟩ (UInt256.ofNat 4658),
  .op .JUMPI,
  .push ⟨20, by decide⟩ (UInt256.ofNat 814647003348588794217809277549781461204094028796),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .MSTORE,
  .op .MSIZE,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .RETURN]

theorem tail_eq : (Control.Artifact.submissionArtifact.instructions.drop 3430).take tail.length = tail := by rfl

theorem pc_base : Control.Artifact.submissionArtifact.instructionPC 3430 = 4840 := by
  rw [instructionPC_eq_byteLength]
  rfl

theorem get (index : Nat) (h : index < tail.length := by decide) :
    Control.Artifact.submissionArtifact.instructions[3430 + index]? = tail[index]? := by
  have ht := congrArg (fun l : List Instr => l[index]?) tail_eq
  simp only [List.getElem?_take_of_lt h] at ht
  rw [← InstructionWindow.get_drop]
  exact ht

theorem pc (index : Nat) (h : index ≤ tail.length := by decide) :
    Control.Artifact.submissionArtifact.instructionPC (3430 + index) =
      4840 + byteLength (tail.take index) := by
  have ht : (Control.Artifact.submissionArtifact.instructions.drop 3430).take index = tail.take index := by
    have ht0 := congrArg (List.take index) tail_eq
    rw [List.take_take, Nat.min_eq_left h] at ht0
    exact ht0
  rw [InstructionWindow.pc_drop, pc_base, ht]

#print axioms get
#print axioms pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.GuardInstructionWindow
