import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1753). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 745 .JUMPDEST,
   pushAt 746 2 2688,
   opAt 747 .MLOAD,
   pushAt 748 2 32,
   opAt 749 (.Dup ⟨1, by decide⟩),
   opAt 750 (.Dup ⟨3, by decide⟩),
   opAt 751 .ADD,
   opAt 752 .SUB,
   opAt 753 (.Dup ⟨1, by decide⟩),
   opAt 754 (.Dup ⟨4, by decide⟩),
   opAt 755 .ADD,
   pushAt 756 1 32,
   opAt 757 (.Swap ⟨0, by decide⟩),
   opAt 758 .SUB,
   opAt 759 (.Swap ⟨2, by decide⟩),
   opAt 760 .POP,
   opAt 761 (.Swap ⟨2, by decide⟩),
   opAt 762 .POP,
   opAt 763 .POP,
   pushAt 764 2 2784,
   opAt 765 .MLOAD,
   pushAt 766 0 0,
   opAt 767 (.Swap ⟨2, by decide⟩),
   opAt 768 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
