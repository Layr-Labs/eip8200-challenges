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
  [opAt 749 .JUMPDEST,
   pushAt 750 2 2688,
   opAt 751 .MLOAD,
   pushAt 752 2 32,
   opAt 753 (.Dup ⟨1, by decide⟩),
   opAt 754 (.Dup ⟨3, by decide⟩),
   opAt 755 .ADD,
   opAt 756 .SUB,
   opAt 757 (.Dup ⟨1, by decide⟩),
   opAt 758 (.Dup ⟨4, by decide⟩),
   opAt 759 .ADD,
   pushAt 760 1 32,
   opAt 761 (.Swap ⟨0, by decide⟩),
   opAt 762 .SUB,
   opAt 763 (.Swap ⟨2, by decide⟩),
   opAt 764 .POP,
   opAt 765 (.Swap ⟨2, by decide⟩),
   opAt 766 .POP,
   opAt 767 .POP,
   pushAt 768 2 2784,
   opAt 769 .MLOAD,
   pushAt 770 0 0,
   opAt 771 (.Swap ⟨2, by decide⟩),
   opAt 772 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
