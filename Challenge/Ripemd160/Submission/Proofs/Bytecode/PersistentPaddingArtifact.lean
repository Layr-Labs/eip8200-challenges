import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPaddingArtifact
open EvmSemantics EvmSemantics.EVM Artifact
private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The padding code is entered by fall-through; no return address is pushed. -/
def padEnterPath : List
    (Challenge.EvmProof.Stepper.Located submissionArtifact .Osaka) :=
  []

/-- Cached located path for RIPEMD padded-length arithmetic. -/
def padLengthPath : List
    (Challenge.EvmProof.Stepper.Located submissionArtifact .Osaka) :=
  [⟨179, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by rfl, by decide⟩,
   ⟨181, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨182, .push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨183, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨184, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨185, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for copying calldata and setting up the footer loop. -/
def padSetupPath : List
    (Challenge.EvmProof.Stepper.Located submissionArtifact .Osaka) :=
  [⟨186, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨187, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨188, .push ⟨2, by decide⟩ (UInt256.ofNat 1632), by rfl, by decide⟩,
   ⟨189, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨190, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨191, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨192, .push ⟨2, by decide⟩ (UInt256.ofNat 1632), by rfl, by decide⟩,
   ⟨193, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨194, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨195, .push ⟨1, by decide⟩ (UInt256.ofNat 195), by rfl, by decide⟩,
   ⟨196, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨197, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨198, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨199, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨200, .push ⟨2, by decide⟩ (UInt256.ofNat 1624), by rfl, by decide⟩,
   ⟨201, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨202, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨203, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨204, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨205, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨207, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨208, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩]





end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPaddingArtifact
