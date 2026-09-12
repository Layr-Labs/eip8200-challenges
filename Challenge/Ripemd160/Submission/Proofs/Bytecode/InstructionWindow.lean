import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.InstructionWindow
open YulEvmCompiler Challenge.EvmProof ArtifactByteLength

theorem get_drop {α : Type} (xs : List α) (base index : Nat) :
    (xs.drop base)[index]? = xs[base + index]? := by
  induction base generalizing xs with
  | zero => simp
  | succ base ih =>
    cases xs with
    | nil => simp
    | cons x xs => simp [Nat.succ_add, ih]

theorem take_add {α : Type} (xs : List α) (base count : Nat) :
    xs.take (base + count) = xs.take base ++ (xs.drop base).take count := by
  induction base generalizing xs with
  | zero => simp
  | succ base ih =>
    cases xs with
    | nil => simp
    | cons x xs => simpa [Nat.succ_add] using congrArg (List.cons x) (ih xs)

theorem byteLength_append (xs ys : List Instr) :
    byteLength (xs ++ ys) = byteLength xs + byteLength ys := by
  induction xs with
  | nil => simp [byteLength]
  | cons x xs ih => cases x <;> simp [byteLength, ih, Nat.add_assoc]

theorem pc_drop (artifact : ProgramArtifact) (base index : Nat) :
    artifact.instructionPC (base + index) = artifact.instructionPC base +
      byteLength ((artifact.instructions.drop base).take index) := by
  rw [instructionPC_eq_byteLength, instructionPC_eq_byteLength,
    take_add, byteLength_append]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.InstructionWindow
