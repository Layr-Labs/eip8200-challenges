import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true

/-!
# Local instruction segments

These lemmas split a concrete artifact once, then compute instruction positions
inside the small certified segment.  Downstream PC proofs no longer normalize the
entire submission prefix independently.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactSegment

open Challenge.EvmProof
open YulEvmCompiler
open WindowTwentyOneBinding

theorem getElem?_segment (p : ProgramArtifact) (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i < segment.length) :
    p.instructions[before.length + i]? = segment[i]? := by
  rw [hsplit, List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hi

theorem instructionPC_succ (p : ProgramArtifact) (index : Nat) (instruction : Instr)
    (hget : p.instructions[index]? = some instruction) :
    p.instructionPC (index + 1) = p.instructionPC index + instruction.bytes.length := by
  simp only [ProgramArtifact.instructionPC, List.take_add_one, hget,
    Option.toList_some, assembleBytes_append, assembleBytes_cons, assembleBytes_nil,
    List.append_nil, List.length_append]

theorem instructionPC_segment (p : ProgramArtifact)
    (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (before.length + i) =
      (assembleBytes before).length + (assembleBytes (segment.take i)).length := by
  unfold ProgramArtifact.instructionPC
  rw [hsplit, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega : before.length ≤ before.length + i)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length hi, assembleBytes_append, List.length_append]

theorem instructionPC_segment_of_bounds (p : ProgramArtifact)
    (before segment after : List Instr) (startIndex startPC : Nat)
    (hsplit : p.instructions = before ++ segment ++ after)
    (hindex : before.length = startIndex)
    (hpc : (assembleBytes before).length = startPC)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (startIndex + i) =
      startPC + (assembleBytes (segment.take i)).length := by
  simpa only [hindex, hpc] using
    instructionPC_segment p before segment after hsplit i hi

theorem locations_segment {fork : EvmSemantics.Fork}
    (p : ProgramArtifact) (cert : Stepper.AllWellFormed p fork)
    (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (off count : Nat) (hrange : off + count ≤ segment.length)
    (hbound : before.length + off + count ≤ p.instructions.length) :
    (WindowTwentyOneSlice.locations cert (before.length + off) count hbound).map
      Stepper.Located.instruction = (segment.drop off).take count := by
  induction count generalizing off with
  | zero => rfl
  | succ count ih =>
      have hi : off < segment.length := by omega
      have hp : before.length + off < p.instructions.length := by omega
      have hget := getElem?_segment p before segment after hsplit off hi
      have hhead : p.instructions[before.length + off] = segment[off] := by
        simpa only [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hi,
          Option.some.injEq] using hget
      rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
      simp only [WindowTwentyOneSlice.locations, List.map_cons, Stepper.Located.ofIndex]
      rw [hhead]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (off + 1) (by omega) (by omega)

def block {fork : EvmSemantics.Fork}
    (p : ProgramArtifact) (cert : Stepper.AllWellFormed p fork)
    (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (off count pc : Nat) (instructions : List Instr)
    (hrange : off + count ≤ segment.length)
    (hpc : (assembleBytes before).length +
      (assembleBytes (segment.take off)).length = pc)
    (hinstructions : (segment.drop off).take count = instructions)
    (hlinear : WindowTwentyOneSlice.linearProgram instructions = true) :
    Block p fork pc instructions :=
  WindowTwentyOneSlice.block cert (before.length + off) count pc instructions
    (by rw [hsplit]; simp only [List.length_append]; omega)
    (by simpa only [instructionPC_segment p before segment after hsplit off (by omega)]
      using hpc)
    (by
      rw [locations_segment p cert before segment after hsplit off count hrange]
      exact hinstructions)
    hlinear

end Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactSegment
