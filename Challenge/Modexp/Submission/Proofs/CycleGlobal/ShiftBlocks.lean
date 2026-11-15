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
  [opAt 870 .JUMPDEST,
   opAt 871 (.Dup ⟨0,by decide⟩),
   opAt 872 .MLOAD,
   pushAt 873 2 2112,
   opAt 874 (.Dup ⟨2,by decide⟩),
   opAt 875 .SUB,
   opAt 876 .MLOAD,
   opAt 877 (.Dup ⟨1,by decide⟩),
   opAt 878 .ADD,
   opAt 879 (.Swap ⟨0,by decide⟩),
   opAt 880 (.Dup ⟨1,by decide⟩),
   opAt 881 .LT,
   opAt 882 (.Swap ⟨0,by decide⟩),
   opAt 883 (.Dup ⟨3,by decide⟩),
   opAt 884 .ADD,
   opAt 885 (.Swap ⟨2,by decide⟩),
   opAt 886 (.Dup ⟨3,by decide⟩),
   opAt 887 .LT,
   opAt 888 .OR,
   opAt 889 (.Swap ⟨1,by decide⟩),
   opAt 890 (.Dup ⟨1,by decide⟩),
   opAt 891 .MSTORE]
/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 892 1 31,
   opAt 893 .NOT,
   opAt 894 .ADD,
   pushAt 895 2 2111,
   opAt 896 (.Dup ⟨1,by decide⟩),
   opAt 897 .GT,
   pushAt 898 2 1234,
   opAt 899 .JUMPI]
/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 8166 to 8170). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []
end CycleSubmission.Global.Fast
