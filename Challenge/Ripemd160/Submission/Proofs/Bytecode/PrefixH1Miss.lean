import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranchSite

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Miss

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- A rejected prefix preserves the logical normal-driver seed exactly.
The additional branch gas is carried by the actual GasSteps certificate. -/
def gasSteps_miss_to_driver (input : ByteArray)
    (hfit : CalldataFits input)
    (hmiss : ¬ PrefixBranch.Recognised input) :
    GasSteps (PaddingTrace.padBranchReturned input)
      (PaddingTrace.padReturned input) := by
  have branch := PrefixBranchSite.gasSteps_miss
    (hfit := hfit)
    (PaddingTrace.padBranchReturned input) input
    [UInt256.ofNat 0, Padding.paddedWord input]
    rfl rfl deployAddress_not_precompile rfl rfl rfl rfl (by decide) hmiss
  exact branch.cast rfl (by
    unfold PaddingTrace.padBranchReturned PrefixBranch.originalBodyPC
    have hpc := PaddingTrace.padReturned_pc input
    rw [← hpc])

/-- Full initial-state-to-normal-driver trace for the miss case only. -/
noncomputable def gasSteps_padding_miss (input : ByteArray)
    (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x16c))
    (hmiss : ¬ PrefixBranch.Recognised input) :
    GasSteps (initialState submissionBytecode input 0)
      (PaddingTrace.padReturned input) :=
  (PaddingTrace.gasSteps_padToBranch input hfit entryPrefix).trans
    (gasSteps_miss_to_driver input hfit hmiss)

#print axioms gasSteps_miss_to_driver
#print axioms gasSteps_padding_miss

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Miss
