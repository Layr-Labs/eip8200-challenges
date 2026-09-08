import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program : List Instr :=
  WindowNineGroup.program ⟨247, by decide⟩ ⟨243, by decide⟩ ⟨239, by decide⟩ ++
    WindowNineGroup.program ⟨235, by decide⟩ ⟨231, by decide⟩ ⟨227, by decide⟩ ++
    WindowNineGroup.program ⟨223, by decide⟩ ⟨219, by decide⟩ ⟨215, by decide⟩

theorem program_length : program.length = 183 := by
  have group_length (s0 s1 s2 : Fin 256) :
      (WindowNineGroup.program s0 s1 s2).length = 61 := by
    simp [WindowNineGroup.program, WindowNineGroup.nibbleProgram,
      WindowNineStage.stageProgram, WindowNineStage.fourSquaresProgram,
      WindowNineStage.pairProgram, WindowNineLookup.program]
  simp only [program, List.length_append, group_length]

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

private theorem address_at (exponent : UInt256) (processed index : Nat)
    (hindex : index < 9) (hinside : processed + index < 64) :
    WindowNineGroup.address
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))
      ⟨247 - 4 * index, by omega⟩ =
    32 * WindowNineMath.nibble exponent.toNat (processed + index) := by
  unfold WindowNineGroup.address
  rw [land_comm]
  exact WindowNineBits.shifted_lookupAddress exponent processed index hindex hinside

/-- Exact 192-byte straight-line body for every eligible exponent position.
The shifted exponent and counter are preserved for the separate loop tail. -/
theorem run_nine (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (processed : Nat) (hprocessed : processed + 9 ≤ 64)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowNineGroup.state template pc base modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter 0 rest) =
    some (WindowNineGroup.state template (advancePC 192 pc) base modulus
      (WindowNineMath.advance base modulus exponent.toNat processed 9 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))
  let digit := fun index => WindowNineMath.nibble exponent.toNat (processed + index)
  let a1 := WindowNineGroup.accumulatorAfter base modulus accumulator (digit 0) (digit 1) (digit 2)
  let a2 := WindowNineGroup.accumulatorAfter base modulus a1 (digit 3) (digit 4) (digit 5)
  have hi (index : Nat) : digit index < 16 := WindowNineMath.nibble_lt _ _
  have ha (index : Nat) (hindex : index < 9) :
      WindowNineGroup.address shifted ⟨247 - 4 * index, by omega⟩ = 32 * digit index :=
    address_at exponent processed index hindex (by omega)
  have h0 := WindowNineGroup.run_group template pc base modulus accumulator shifted counter
    ⟨247, by decide⟩ ⟨243, by decide⟩ ⟨239, by decide⟩
    (digit 0) (digit 1) (digit 2) (hi 0) (hi 1) (hi 2)
    (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) rest hrest
  have h1 := WindowNineGroup.run_group template (advancePC 64 pc) base modulus a1 shifted counter
    ⟨235, by decide⟩ ⟨231, by decide⟩ ⟨227, by decide⟩
    (digit 3) (digit 4) (digit 5) (hi 3) (hi 4) (hi 5)
    (ha 3 (by decide)) (ha 4 (by decide)) (ha 5 (by decide)) rest hrest
  have h2 := WindowNineGroup.run_group template (advancePC 64 (advancePC 64 pc))
    base modulus a2 shifted counter
    ⟨223, by decide⟩ ⟨219, by decide⟩ ⟨215, by decide⟩
    (digit 6) (digit 7) (digit 8) (hi 6) (hi 7) (hi 8)
    (ha 6 (by decide)) (ha 7 (by decide)) (ha 8 (by decide)) rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  simpa only [program, shifted, a1, a2, digit, WindowNineGroup.accumulatorAfter,
    WindowNineMath.advance, Nat.add_zero, ← advancePC_add,
    show 64 + 64 + 64 = 192 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBody
