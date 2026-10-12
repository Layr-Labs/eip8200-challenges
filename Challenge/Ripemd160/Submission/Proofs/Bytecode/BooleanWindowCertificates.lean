import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired16Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
import Challenge.EvmProof.Meter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired16

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanWindowCertificates
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

/-- Freeze the mixed f2/f4 circuit, rather than treating it as a single-lane
choice kernel. Both lanes share this selector-dependent computation. -/
def mixedChoiceWindow : List Instr := StaggerRawPaired16.template.drop 4 |>.take 13

theorem mixedChoiceWindow_opcodes : mixedChoiceWindow =
    [.op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨11, by decide⟩),
     .op (.Dup ⟨1, by decide⟩), .op .OR,
     .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨8, by decide⟩),
     .op .XOR, .op .AND, .op .XOR,
     .op (.Dup ⟨11, by decide⟩), .op (.Dup ⟨9, by decide⟩),
     .op .AND, .op .OR] := by rfl

theorem mixedChoiceWindow_cost :
    (mixedChoiceWindow.map (Meter.instrStaticCost .Osaka)).sum = 39 := by decide

theorem mixedChoiceWindow_size : (mixedChoiceWindow.map Instr.size).sum = 13 := by decide

/-- Bind the frozen thirteen-opcode circuit to the installed artifact, not just
to a separate symbolic Boolean template. Round 16 starts at instruction 1088. -/
theorem mixedChoiceWindow_actual :
    ((((Artifact.submissionArtifact.instructions.drop 1088).take
      StaggerRawPaired16.template.length).drop 4).take 13) = mixedChoiceWindow := by
  rw [StaggerRawPaired16.actual_slice]
  rfl

/-- At selector zero the installed mixed circuit is f2; at selector all-ones
it is f4. A single seven-operation f2 kernel cannot replace this block. -/
theorem selector_zero (b c d : BitVec w) :
    StaggerBoolean.raw 1 (BitVec.allOnes w) 0#w b c d =
      d ^^^ (b &&& (c ^^^ d)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [StaggerBoolean.raw, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

theorem selector_ones (b c d : BitVec w) :
    StaggerBoolean.raw 1 (BitVec.allOnes w) (BitVec.allOnes w) b c d =
      c ^^^ (d &&& (b ^^^ c)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [StaggerBoolean.raw, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, hi, decide_true]
  cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

/-- The scalar f2 replacement is false even on one supported bit. This is a
generic circuit witness, not a claim that the specific words are reachable
after sixteen RIPEMD rounds. -/
theorem scalarChoice_not_mixed :
    StaggerBoolean.raw 1 1#1 1#1 1#1 0#1 1#1 ≠
      (1#1 ^^^ (1#1 &&& (0#1 ^^^ 1#1))) := by decide

#print axioms mixedChoiceWindow_cost
#print axioms mixedChoiceWindow_actual
#print axioms scalarChoice_not_mixed
#print axioms selector_zero
#print axioms selector_ones
end Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanWindowCertificates
