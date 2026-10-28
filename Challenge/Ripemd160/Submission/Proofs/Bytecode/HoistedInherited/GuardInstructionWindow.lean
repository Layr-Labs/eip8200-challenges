import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InstructionWindow
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GuardInstructionWindow
open EvmSemantics YulEvmCompiler Challenge.EvmProof ArtifactByteLength
open HoistedInherited.Artifact (op)
def tail : List Instr :=
[
  .push 32 5506022574726681700290820341793915503137370776112178186780075461015395893248,
  .push 0 0,
  op 0x35,
  op 0x36,
  op 0x1d,
  op 0x18,
  .push 2 8085,
  op 0x57,
  .push 20 814647003348588794217809277549781461204094028796,
  .push 0 0,
  op 0x52,
  op 0x59,
  .push 0 0,
  op 0xf3
]
theorem tail_eq : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 6199).take tail.length = tail := by rfl

theorem pc_base : HoistedInherited.Artifact.submissionArtifact.instructionPC 6199 = 8329 := by
  rw [instructionPC_eq_byteLength]
  rfl

theorem get (index : Nat) (h : index < tail.length := by decide) :
    HoistedInherited.Artifact.submissionArtifact.instructions[6199 + index]? = tail[index]? := by
  have ht := congrArg (fun l : List Instr => l[index]?) tail_eq
  simp only [List.getElem?_take_of_lt h] at ht
  rw [← InstructionWindow.get_drop]
  exact ht

theorem pc (index : Nat) (h : index ≤ tail.length := by decide) :
    HoistedInherited.Artifact.submissionArtifact.instructionPC (6199 + index) =
      8329 + byteLength (tail.take index) := by
  have ht : (HoistedInherited.Artifact.submissionArtifact.instructions.drop 6199).take index = tail.take index := by
    have ht0 := congrArg (List.take index) tail_eq
    rw [List.take_take, Nat.min_eq_left h] at ht0
    exact ht0
  rw [InstructionWindow.pc_drop, pc_base, ht]

#print axioms get
#print axioms pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GuardInstructionWindow
