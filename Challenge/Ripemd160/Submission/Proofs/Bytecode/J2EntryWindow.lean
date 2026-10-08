import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InstructionWindow
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2EntryWindow
open EvmSemantics YulEvmCompiler Challenge.EvmProof ArtifactByteLength
open Artifact (op)
def tail : List Instr := [
  op 0x5b,
  op 0x36,
  .push 1 1,
  .push 17 342276208914615837337402008677671501826,
  op 0x36,
  op 0x1c,
  op 0x16,
  .push 2 4813,
  op 0x57,
  .push 2 376,
  .push 5 24641792,
  op 0x36,
  .push 1 16,
  op 0x16,
  op 0x1c,
  op 0x16,
  op 0x14,
  .push 2 4810,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 232,
  op 0x1d,
  op 0x36,
  .push 3 2127393,
  op 0x02,
  op 0x18,
  .push 1 246,
  op 0x57,
  .push 20 95383801997447390147238369573240532004699299169,
  op 0x36,
  op 0x1c,
  .push 20 802931186561056611446976448233794645126013734992,
  op 0x18,
  .push 1 98,
  op 0x56,
  .push 1 3,
  op 0x03,
  op 0x03,
  op 0x03,
  op 0x03,
  op 0x03,
  op 0x5b,
  .push 1 251,
  op 0x5b
]
private theorem tail_eq : (Artifact.submissionArtifact.instructions.drop 3510).take tail.length = tail := by rfl
private theorem pc_base : Artifact.submissionArtifact.instructionPC 3510 = 4691 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
theorem get (index : Nat) (h : index < tail.length := by decide) :
    Artifact.submissionArtifact.instructions[3510 + index]? = tail[index]? := by
  have ht := congrArg (fun l : List Instr => l[index]?) tail_eq
  simp only [List.getElem?_take_of_lt h] at ht
  rw [← InstructionWindow.get_drop]
  exact ht
theorem pc (index : Nat) (h : index ≤ tail.length := by decide) :
    Artifact.submissionArtifact.instructionPC (3510 + index) =
      4691 + byteLength (tail.take index) := by
  have ht : (Artifact.submissionArtifact.instructions.drop 3510).take index = tail.take index := by
    have ht0 := congrArg (List.take index) tail_eq
    rw [List.take_take, Nat.min_eq_left h] at ht0
    exact ht0
  rw [InstructionWindow.pc_drop, pc_base, ht]
#print axioms get
#print axioms pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2EntryWindow
