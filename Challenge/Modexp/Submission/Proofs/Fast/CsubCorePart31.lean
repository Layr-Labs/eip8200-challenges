import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart30

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem lowValue_lt (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n j < Limbs.radix ^ j := by
  have hdigits : ∀ d ∈ (List.range j).map (fun k =>
      (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat),
      d < Limbs.radix := by
    intro d hd
    simp only [List.mem_map] at hd
    rcases hd with ⟨k, _, rfl⟩
    exact (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).val.isLt
  have h := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one hdigits
  simpa [lowValue] using h

end Challenge.Modexp.Submission.Proofs.Fast.Csub
