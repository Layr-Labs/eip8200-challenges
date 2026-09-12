import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3813 .JUMPDEST,
   pushAt 3814 1 64,
   opAt 3815 .CALLDATALOAD,
   opAt 3816 (.Dup ⟨0, by decide⟩),
   pushAt 3817 1 33,
   opAt 3818 .GT,
   pushAt 3819 2 1448,
   opAt 3820 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3821 1 32,
   opAt 3822 .CALLDATALOAD,
   pushAt 3823 0 0,
   opAt 3824 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3825 (.Dup ⟨2, by decide⟩),
   pushAt 3826 1 31,
   opAt 3827 .ADD,
   pushAt 3828 1 5,
   opAt 3829 .SHR,
   opAt 3830 (.Dup ⟨0, by decide⟩),
   pushAt 3831 1 5,
   opAt 3832 .SHL,
   opAt 3833 (.Dup ⟨3, by decide⟩),
   opAt 3834 (.Dup ⟨3, by decide⟩),
   opAt 3835 .ADD,
   pushAt 3836 1 96,
   opAt 3837 .ADD,
   opAt 3838 (.Dup ⟨5, by decide⟩),
   opAt 3839 (.Dup ⟨2, by decide⟩),
   opAt 3840 .SUB,
   pushAt 3841 1 3,
   opAt 3842 .SHL,
   opAt 3843 (.Dup ⟨1, by decide⟩),
   opAt 3844 .CALLDATALOAD,
   opAt 3845 (.Swap ⟨0, by decide⟩),
   opAt 3846 .SHR,
   opAt 3847 .ISZERO,
   pushAt 3848 2 1454,
   opAt 3849 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
