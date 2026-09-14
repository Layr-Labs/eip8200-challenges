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
  .push 1 1,
  .push 17 342276208914615837337402008677671501826,
  op 0x36,
  op 0x1c,
  op 0x16,
  .push 1 112,
  op 0x57,
  op 0x36,
  .push 2 376,
  op 0x14,
  .push 2 256,
  op 0x36,
  op 0x14,
  op 0x36,
  .push 2 1000,
  op 0x14,
  op 0x17,
  op 0x17,
  .push 1 112,
  op 0x57,
  .push 0 0,
  op 0x35,
  .push 1 232,
  op 0x1c,
  op 0x36,
  .push 3 2127393,
  op 0x02,
  op 0x18,
  .push 2 352,
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
  op 0xf3]
private theorem tail_eq : Artifact.submissionArtifact.instructions.drop 3725 = tail := by rfl
private theorem pc_base : Artifact.submissionArtifact.instructionPC 3725 = 4840 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
theorem get (index : Nat) :
    Artifact.submissionArtifact.instructions[3725+index]? = tail[index]? := by
  rw [← InstructionWindow.get_drop, tail_eq]
theorem pc (index : Nat) :
    Artifact.submissionArtifact.instructionPC (3725+index) = 4840+byteLength (tail.take index) := by
  rw [InstructionWindow.pc_drop, pc_base, tail_eq]
#print axioms get
#print axioms pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2EntryWindow
