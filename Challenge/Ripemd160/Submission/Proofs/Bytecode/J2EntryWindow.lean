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
  .push 2 4796,
  op 0x57,
  .push 2 256,
  op 0x14,
  .push 2 376,
  op 0x36,
  op 0x14,
  op 0x01,
  .push 2 4793,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 232,
  op 0x1d,
  op 0x36,
  .push 3 2127393,
  op 0x02,
  op 0x18,
  .push 1 247,
  op 0x57,
  .push 20 95383801997447390147238369573240532004699299169,
  op 0x36,
  op 0x1c,
  .push 20 802931186561056611446976448233794645126013734992,
  op 0x18,
  .push 0 0,
  op 0x52,
  op 0x59,
  .push 0 0,
  op 0xf3
]
def tailB : List Instr := [
  op 0x5b,
  .push 1 251,
  op 0x5b
]
private theorem tail_eq : (Artifact.submissionArtifact.instructions.drop 3440).take tail.length = tail := by rfl
private theorem pc_base : Artifact.submissionArtifact.instructionPC 3440 = 4601 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
theorem get (index : Nat) (h : index < tail.length := by decide) :
    Artifact.submissionArtifact.instructions[3440 + index]? = tail[index]? := by
  have ht := congrArg (fun l : List Instr => l[index]?) tail_eq
  simp only [List.getElem?_take_of_lt h] at ht
  rw [← InstructionWindow.get_drop]
  exact ht
theorem pc (index : Nat) (h : index ≤ tail.length := by decide) :
    Artifact.submissionArtifact.instructionPC (3440 + index) =
      4601 + byteLength (tail.take index) := by
  have ht : (Artifact.submissionArtifact.instructions.drop 3440).take index = tail.take index := by
    have ht0 := congrArg (List.take index) tail_eq
    rw [List.take_take, Nat.min_eq_left h] at ht0
    exact ht0
  rw [InstructionWindow.pc_drop, pc_base, ht]
private theorem tailB_eq : (Artifact.submissionArtifact.instructions.drop 3528).take tailB.length = tailB := by rfl
private theorem pc_baseB : Artifact.submissionArtifact.instructionPC 3528 = 4793 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
theorem getB (index : Nat) (h : index < tailB.length := by decide) :
    Artifact.submissionArtifact.instructions[3528 + index]? = tailB[index]? := by
  have ht := congrArg (fun l : List Instr => l[index]?) tailB_eq
  simp only [List.getElem?_take_of_lt h] at ht
  rw [← InstructionWindow.get_drop]
  exact ht
theorem pcB (index : Nat) (h : index ≤ tailB.length := by decide) :
    Artifact.submissionArtifact.instructionPC (3528 + index) =
      4793 + byteLength (tailB.take index) := by
  have ht : (Artifact.submissionArtifact.instructions.drop 3528).take index = tailB.take index := by
    have ht0 := congrArg (List.take index) tailB_eq
    rw [List.take_take, Nat.min_eq_left h] at ht0
    exact ht0
  rw [InstructionWindow.pc_drop, pc_baseB, ht]
#print axioms get
#print axioms pc
#print axioms getB
#print axioms pcB
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2EntryWindow
