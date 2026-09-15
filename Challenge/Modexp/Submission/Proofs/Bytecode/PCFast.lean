import Challenge.EvmProof.Program
set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
open YulEvmCompiler Challenge.EvmProof
def byteLength : List Instr → Nat
  | [] => 0
  | .op _ :: rest => 1 + byteLength rest
  | .push width _ :: rest => (1 + width.val) + byteLength rest
theorem byteLength_eq_assemble (instructions : List Instr) :
    byteLength instructions = (assembleBytes instructions).length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [byteLength, assembleBytes_cons, ih, Nat.add_comm]
theorem instructionPC_eq_byteLength (artifact : ProgramArtifact) (index : Nat) :
    artifact.instructionPC index = byteLength (artifact.instructions.take index) :=
  (byteLength_eq_assemble _).symm
end Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
