import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate
def coreAdvancesCheck : Instr → Bool
  | .push _ _ => true
  | .op .ADD | .op .MUL | .op .AND | .op .OR | .op .XOR | .op .NOT |
    .op .SHL | .op .SHR | .op .POP | .op .MLOAD | .op .MSTORE | .op .JUMPDEST => true
  | .op (.Dup _) | .op (.Swap _) => true
  | _ => false

theorem coreAdvancesCheck_sound (instruction : Instr)
    (h : coreAdvancesCheck instruction = true) : DenseScheduleLift.Advances instruction := by
  cases instruction with
  | push width value => exact Or.inl (Or.inl (StraightLine.push width value))
  | op operation =>
    cases operation <;> first
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl (StraightLine.swap _))
      | (rename_i inner; cases inner <;> first
          | exact Or.inl (Or.inl StraightLine.add)
          | exact Or.inl (Or.inl StraightLine.and)
          | exact Or.inl (Or.inl StraightLine.or)
          | exact Or.inl (Or.inl StraightLine.xor)
          | exact Or.inl (Or.inl StraightLine.not)
          | exact Or.inl (Or.inl StraightLine.shl)
          | exact Or.inl (Or.inl StraightLine.shr)
          | exact Or.inl (Or.inl StraightLine.pop)
          | exact Or.inl (Or.inl StraightLine.mload)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
          | exact Or.inl (Or.inr (Or.inr rfl))
          | simp only [coreAdvancesCheck, Bool.false_eq_true] at h)


theorem coreAdvancesAll_sound (code : List Instr)
    (h : code.all coreAdvancesCheck = true) :
    ∀ instruction ∈ code, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  exact coreAdvancesCheck_sound instruction ((List.all_eq_true.mp h) instruction hmem)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
