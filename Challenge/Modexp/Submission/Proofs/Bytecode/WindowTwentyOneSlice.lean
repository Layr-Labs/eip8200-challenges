import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper WindowTwentyOneLocated WindowTwentyOneBinding

/-- Consecutive, individually certified instruction locations. The count bound
rules out truncated slices rather than silently dropping missing instructions. -/
def locations {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start : Nat) :
    (count : Nat) → start + count ≤ artifact.instructions.length → List (Located artifact fork)
  | 0, _ => []
  | count + 1, h =>
      Located.ofIndex cert ⟨start, by omega⟩ ::
        locations cert (start + 1) count (by omega)

/-- Exactly the opcode restriction needed by the checked linear-PC bridge. -/
def linearProgram : List Instr → Bool
  | [] | [_] => true
  | instruction :: next :: rest => Linear instruction && linearProgram (next :: rest)

private theorem instructionPC_succ (artifact : ProgramArtifact) (index : Nat)
    (instruction : Instr) (hget : artifact.instructions[index]? = some instruction) :
    artifact.instructionPC (index + 1) = artifact.instructionPC index + instruction.size := by
  simp only [ProgramArtifact.instructionPC, List.take_add_one, hget,
    Option.toList_some, assembleBytes_append, assembleBytes_cons, assembleBytes_nil,
    List.append_nil, List.length_append, Instr.size]

theorem locations_layout {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start count : Nat)
    (hbound : start + count ≤ artifact.instructions.length)
    (hlinear : linearProgram ((locations cert start count hbound).map Located.instruction) = true) :
    LinearPath (UInt256.ofNat (artifact.instructionPC start)) (locations cert start count hbound) := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          let first := Located.ofIndex cert ⟨start, by omega⟩
          have htailBound : start + 1 + (count + 1) ≤ artifact.instructions.length := by omega
          change (Linear first.instruction &&
            linearProgram ((locations cert (start + 1) (count + 1) htailBound).map Located.instruction)) = true at hlinear
          have parts := Bool.and_eq_true_iff.mp hlinear
          refine ⟨rfl, parts.1, ?_⟩
          have hpc : UInt256.ofNat (artifact.instructionPC (start + 1)) =
              UInt256.ofNat (artifact.instructionPC start) + UInt256.ofNat first.instruction.size := by
            rw [instructionPC_succ artifact start first.instruction first.atIndex]
            exact (Challenge.EvmProof.Word.ofNat_add_mod _ _).symm
          rw [← hpc]
          exact ih (start + 1) htailBound parts.2

/-- A start-PC equality and an exact opcode slice determine every interior PC.
No unchecked instruction-index or code-target assumptions enter the result. -/
def block {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start count pc : Nat)
    (instructions : List Instr) (hbound : start + count ≤ artifact.instructions.length)
    (hpc : artifact.instructionPC start = pc)
    (hopcodes : (locations cert start count hbound).map Located.instruction = instructions)
    (hlinear : linearProgram instructions = true) : Block artifact fork pc instructions where
  path := locations cert start count hbound
  instructions_eq := hopcodes
  layout := by
    rw [← hpc]
    apply locations_layout
    rw [hopcodes]
    exact hlinear

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
