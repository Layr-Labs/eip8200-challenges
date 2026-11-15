import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/
namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   opAt 2669 (.Dup ⟨0,by decide⟩),
   opAt 2670 .MLOAD,
   pushAt 2671 2 2112,
   opAt 2672 (.Dup ⟨2,by decide⟩),
   opAt 2673 .SUB,
   opAt 2674 .MLOAD,
   opAt 2675 (.Dup ⟨1,by decide⟩),
   opAt 2676 .ADD,
   opAt 2677 (.Swap ⟨0,by decide⟩),
   opAt 2678 (.Dup ⟨1,by decide⟩),
   opAt 2679 .LT,
   opAt 2680 (.Swap ⟨0,by decide⟩),
   opAt 2681 (.Dup ⟨3,by decide⟩),
   opAt 2682 .ADD,
   opAt 2683 (.Swap ⟨2,by decide⟩),
   opAt 2684 (.Dup ⟨3,by decide⟩),
   opAt 2685 .LT,
   opAt 2686 .OR,
   opAt 2687 (.Swap ⟨1,by decide⟩),
   opAt 2688 (.Dup ⟨1,by decide⟩),
   opAt 2689 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2690 1 31,
   opAt 2691 .NOT,
   opAt 2692 .ADD,
   pushAt 2693 2 2111,
   opAt 2694 (.Dup ⟨1,by decide⟩),
   opAt 2695 .GT,
   pushAt 2696 2 3480,
   opAt 2697 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2399 to 2403). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
