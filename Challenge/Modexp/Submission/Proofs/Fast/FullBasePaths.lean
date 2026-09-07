import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1668.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

namespace FullBaseLocated

def startIndex : Nat := 2361

/-- The complete, contiguous full-base helper as a bounded local slice.  Keeping
the default `getElem?` proofs on this small template avoids unfolding the whole
submission artifact for every located instruction. -/
private def template : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .EQ,
   .push 0 0,
   .op .MLOAD,
   .push 1 255,
   .op .SHR,
   .op .AND,
   .op .ISZERO,
   .push 2 3661,
   .op .JUMPI,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .push 2 1024,
   .op .CALLDATACOPY,
   .push 2 1755,
   .push 2 2048,
   .push 2 1024,
   .push 2 6144,
   .push 2 4057,
   .op .JUMP,
   .op .JUMPDEST,
   .push 2 1755,
   .push 2 2048,
   .push 2 6144,
   .push 2 1024,
   .push 2 4057,
   .op .JUMP,
   .op .JUMPDEST,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 31,
   .op .ADD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push 1 5,
   .op .SHL,
   .op .SUB,
   .push 1 3,
   .op .SHL,
   .push 1 96,
   .op .CALLDATALOAD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 992,
   .op .ADD,
   .op .MSTORE,
   .push 1 1,
   .push 2 1668,
   .op .JUMP]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop startIndex).take template.length = template := by
  rfl

private theorem getElem_slice (offset : Nat) (hoffset : offset < template.length) :
    Artifact.submissionInstructions[startIndex + offset]? = template[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) slice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

def opAt (offset : Nat) (op : Operation)
    (hget : template[offset]? = some (.op op) := by rfl)
    (hoffset : offset < template.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨startIndex + offset, .op op, (getElem_slice offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def pushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : template[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < template.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨startIndex + offset, .push width value, (getElem_slice offset hoffset).trans hget, hwf⟩

end FullBaseLocated

/-- pc 3606..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [FullBaseLocated.opAt 0 .JUMPDEST,
   FullBaseLocated.opAt 1 (.Dup ⟨0, by decide⟩),
   FullBaseLocated.opAt 2 (.Dup ⟨3, by decide⟩),
   FullBaseLocated.opAt 3 .EQ,
   FullBaseLocated.pushAt 4 0 0,
   FullBaseLocated.opAt 5 .MLOAD,
   FullBaseLocated.pushAt 6 1 255,
   FullBaseLocated.opAt 7 .SHR,
   FullBaseLocated.opAt 8 .AND,
   FullBaseLocated.opAt 9 .ISZERO,
   FullBaseLocated.pushAt 10 2 3661,
   FullBaseLocated.opAt 11 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [FullBaseLocated.opAt 12 (.Dup ⟨0, by decide⟩),
   FullBaseLocated.pushAt 13 1 96,
   FullBaseLocated.pushAt 14 2 1024,
   FullBaseLocated.opAt 15 .CALLDATACOPY,
   FullBaseLocated.pushAt 16 2 1755,
   FullBaseLocated.pushAt 17 2 2048,
   FullBaseLocated.pushAt 18 2 1024,
   FullBaseLocated.pushAt 19 2 6144,
   FullBaseLocated.pushAt 20 2 4057,
   FullBaseLocated.opAt 21 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [FullBaseLocated.opAt 22 .JUMPDEST,
   FullBaseLocated.pushAt 23 2 1755,
   FullBaseLocated.pushAt 24 2 2048,
   FullBaseLocated.pushAt 25 2 6144,
   FullBaseLocated.pushAt 26 2 1024,
   FullBaseLocated.pushAt 27 2 4057,
   FullBaseLocated.opAt 28 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [FullBaseLocated.opAt 29 .JUMPDEST,
   FullBaseLocated.opAt 30 (.Dup ⟨2, by decide⟩),
   FullBaseLocated.pushAt 31 1 31,
   FullBaseLocated.opAt 32 .ADD,
   FullBaseLocated.pushAt 33 1 5,
   FullBaseLocated.opAt 34 .SHR,
   FullBaseLocated.opAt 35 (.Dup ⟨3, by decide⟩),
   FullBaseLocated.opAt 36 (.Dup ⟨1, by decide⟩),
   FullBaseLocated.pushAt 37 1 5,
   FullBaseLocated.opAt 38 .SHL,
   FullBaseLocated.opAt 39 .SUB,
   FullBaseLocated.pushAt 40 1 3,
   FullBaseLocated.opAt 41 .SHL,
   FullBaseLocated.pushAt 42 1 96,
   FullBaseLocated.opAt 43 .CALLDATALOAD,
   FullBaseLocated.opAt 44 (.Swap ⟨0, by decide⟩),
   FullBaseLocated.opAt 45 .SHR,
   FullBaseLocated.opAt 46 (.Dup ⟨2, by decide⟩),
   FullBaseLocated.pushAt 47 2 992,
   FullBaseLocated.opAt 48 .ADD,
   FullBaseLocated.opAt 49 .MSTORE,
   FullBaseLocated.pushAt 50 1 1,
   FullBaseLocated.pushAt 51 2 1668,
   FullBaseLocated.opAt 52 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
