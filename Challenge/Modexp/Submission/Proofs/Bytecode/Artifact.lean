import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks.C8

attribute [simp]
  Challenge.EvmProof.Word.word_toNat_add
  Challenge.EvmProof.Word.word_toNat_sub
  Challenge.EvmProof.Word.word_toNat_lt
  Challenge.EvmProof.Word.word_toNat_isZero
  Challenge.EvmProof.Word.word_toNat_lor
  Challenge.EvmProof.Word.word_toNat_land

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks

def submissionInstructions : List Instr :=
  instructions0 ++
  instructions1 ++
  instructions2 ++
  instructions3 ++
  instructions4 ++
  instructions5 ++
  instructions6 ++
  instructions7 ++
  instructions8


theorem submissionInstructions_count : submissionInstructions.length = 3958 := by
  simp [submissionInstructions, count0, count1, count2, count3, count4, count5, count6, count7, count8]

theorem assemble_submissionInstructions :
    assemble submissionInstructions = submissionBytecode := by
  simp only [submissionInstructions, assemble_append, assemble0, assemble1, assemble2,
    assemble3, assemble4, assemble5, assemble6, assemble7, assemble8]
  rfl

def submissionArtifact : Challenge.EvmProof.ProgramArtifact where
  code := submissionBytecode
  instructions := submissionInstructions
  assembly_eq := assemble_submissionInstructions

theorem allWellFormed :
    Challenge.EvmProof.Stepper.AllWellFormed submissionArtifact .Osaka := by
  change submissionInstructions.all (fun i => decide
    (Challenge.EvmProof.Stepper.WellFormed .Osaka i)) = true
  simp [submissionInstructions, wellFormed0, wellFormed1, wellFormed2, wellFormed3,
    wellFormed4, wellFormed5, wellFormed6, wellFormed7, wellFormed8]

def instructionPC (index : Nat) : Nat := submissionArtifact.instructionPC index

theorem decodeAt_op_index (index : Nat) (op : Operation)
    (hget : submissionInstructions[index]? = some (.op op))
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op) :
    Decode.decodeAt submissionBytecode (instructionPC index) = some (op, none) :=
  Challenge.EvmProof.ProgramArtifact.decodeAt_op_index
    submissionArtifact index op hget hopcode hplain

theorem decodeAt_push_index (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : submissionInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val) :
    Decode.decodeAt submissionBytecode (instructionPC index) =
      some (.Push ⟨width⟩, some (value, width.val)) :=
  Challenge.EvmProof.ProgramArtifact.decodeAt_push_index
    submissionArtifact index width value hget hfit

theorem isValidJumpDest_index (index : Nat)
    (hget : submissionInstructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest submissionBytecode (instructionPC index) = true :=
  Challenge.EvmProof.ProgramArtifact.isValidJumpDest_index
    submissionArtifact index hget

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
