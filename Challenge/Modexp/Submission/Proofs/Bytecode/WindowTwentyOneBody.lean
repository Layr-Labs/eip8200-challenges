import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program : List Instr :=
  WindowTwentyOneGroup.program ⟨247, by decide⟩ ⟨243, by decide⟩ ⟨239, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨235, by decide⟩ ⟨231, by decide⟩ ⟨227, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨223, by decide⟩ ⟨219, by decide⟩ ⟨215, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨211, by decide⟩ ⟨207, by decide⟩ ⟨203, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨199, by decide⟩ ⟨195, by decide⟩ ⟨191, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨187, by decide⟩ ⟨183, by decide⟩ ⟨179, by decide⟩ ++
    WindowTwentyOneGroup.program ⟨175, by decide⟩ ⟨171, by decide⟩ ⟨167, by decide⟩

theorem program_length : program.length = 427 := by
  have group_length (s0 s1 s2 : Fin 256) :
      (WindowTwentyOneGroup.program s0 s1 s2).length = 61 := by
    simp [WindowTwentyOneGroup.program, WindowTwentyOneGroup.nibbleProgram,
      WindowTwentyOneStage.stageProgram, WindowTwentyOneStage.fourSquaresProgram,
      WindowTwentyOneStage.pairProgram, WindowTwentyOneLookup.program]
  simp only [program, List.length_append, group_length]

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

private theorem address_at (exponent : UInt256) (processed index : Nat)
    (hindex : index < 21) (hinside : processed + index < 64) :
    WindowTwentyOneGroup.address
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed)))
      ⟨247 - 4 * index, by omega⟩ =
    32 * WindowTwentyOneMath.nibble exponent.toNat (processed + index) := by
  unfold WindowTwentyOneGroup.address
  rw [land_comm]
  exact WindowTwentyOneBits.shifted_lookupAddress exponent processed index hindex hinside

/-- Exact 448-byte straight-line body for every eligible exponent position.
The shifted exponent and counter are preserved for the separate loop tail. -/
theorem run_twentyOne (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (processed : Nat) (hprocessed : processed + 21 ≤ 64)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowTwentyOneGroup.state template pc base modulus accumulator
        (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 448 pc) base modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat processed 21 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat (4 * processed))
  let digit := fun index => WindowTwentyOneMath.nibble exponent.toNat (processed + index)
  let a1 := WindowTwentyOneGroup.accumulatorAfter base modulus accumulator (digit 0) (digit 1) (digit 2)
  let a2 := WindowTwentyOneGroup.accumulatorAfter base modulus a1 (digit 3) (digit 4) (digit 5)
  let a3 := WindowTwentyOneGroup.accumulatorAfter base modulus a2 (digit 6) (digit 7) (digit 8)
  let a4 := WindowTwentyOneGroup.accumulatorAfter base modulus a3 (digit 9) (digit 10) (digit 11)
  let a5 := WindowTwentyOneGroup.accumulatorAfter base modulus a4 (digit 12) (digit 13) (digit 14)
  let a6 := WindowTwentyOneGroup.accumulatorAfter base modulus a5 (digit 15) (digit 16) (digit 17)
  have hi (index : Nat) : digit index < 16 := WindowTwentyOneMath.nibble_lt _ _
  have ha (index : Nat) (hindex : index < 21) :
      WindowTwentyOneGroup.address shifted ⟨247 - 4 * index, by omega⟩ = 32 * digit index :=
    address_at exponent processed index hindex (by omega)
  have h0 := WindowTwentyOneGroup.run_group template pc
    base modulus accumulator shifted counter
    ⟨247, by decide⟩ ⟨243, by decide⟩ ⟨239, by decide⟩
    (digit 0) (digit 1) (digit 2) (hi 0) (hi 1) (hi 2)
    (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) rest hrest
  have h1 := WindowTwentyOneGroup.run_group template (advancePC 64 pc)
    base modulus a1 shifted counter
    ⟨235, by decide⟩ ⟨231, by decide⟩ ⟨227, by decide⟩
    (digit 3) (digit 4) (digit 5) (hi 3) (hi 4) (hi 5)
    (ha 3 (by decide)) (ha 4 (by decide)) (ha 5 (by decide)) rest hrest
  have h2 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 pc))
    base modulus a2 shifted counter
    ⟨223, by decide⟩ ⟨219, by decide⟩ ⟨215, by decide⟩
    (digit 6) (digit 7) (digit 8) (hi 6) (hi 7) (hi 8)
    (ha 6 (by decide)) (ha 7 (by decide)) (ha 8 (by decide)) rest hrest
  have h3 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 pc)))
    base modulus a3 shifted counter
    ⟨211, by decide⟩ ⟨207, by decide⟩ ⟨203, by decide⟩
    (digit 9) (digit 10) (digit 11) (hi 9) (hi 10) (hi 11)
    (ha 9 (by decide)) (ha 10 (by decide)) (ha 11 (by decide)) rest hrest
  have h4 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 pc))))
    base modulus a4 shifted counter
    ⟨199, by decide⟩ ⟨195, by decide⟩ ⟨191, by decide⟩
    (digit 12) (digit 13) (digit 14) (hi 12) (hi 13) (hi 14)
    (ha 12 (by decide)) (ha 13 (by decide)) (ha 14 (by decide)) rest hrest
  have h5 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 pc)))))
    base modulus a5 shifted counter
    ⟨187, by decide⟩ ⟨183, by decide⟩ ⟨179, by decide⟩
    (digit 15) (digit 16) (digit 17) (hi 15) (hi 16) (hi 17)
    (ha 15 (by decide)) (ha 16 (by decide)) (ha 17 (by decide)) rest hrest
  have h6 := WindowTwentyOneGroup.run_group template (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 (advancePC 64 pc))))))
    base modulus a6 shifted counter
    ⟨175, by decide⟩ ⟨171, by decide⟩ ⟨167, by decide⟩
    (digit 18) (digit 19) (digit 20) (hi 18) (hi 19) (hi 20)
    (ha 18 (by decide)) (ha 19 (by decide)) (ha 20 (by decide)) rest hrest
  have hall1 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall2 := runInstructions_append_some _ _ _ _ _ hall1 h2
  have hall3 := runInstructions_append_some _ _ _ _ _ hall2 h3
  have hall4 := runInstructions_append_some _ _ _ _ _ hall3 h4
  have hall5 := runInstructions_append_some _ _ _ _ _ hall4 h5
  have hall6 := runInstructions_append_some _ _ _ _ _ hall5 h6
  simpa only [program, shifted, a1, a2, a3, a4, a5, a6, digit, WindowTwentyOneGroup.accumulatorAfter,
    WindowTwentyOneMath.advance, Nat.add_zero, ← advancePC_add,
    show 64 + 64 + 64 + 64 + 64 + 64 + 64 = 448 by decide] using hall6

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
