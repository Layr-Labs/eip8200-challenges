import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The tables and jump facts below describe the selected round06 layout.
Each table uses a proved prefix-sum anchor and a bounded local slice.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/-! Submission-local prefix-sum PC certificates. -/

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

private theorem fastPCAnchor0 :
    Artifact.submissionArtifact.instructionPC 406 = 578 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 434 = 616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 475 = 673 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 504 = 711 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 535 = 747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 541 = 755 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9b :
    Artifact.submissionArtifact.instructionPC 548 = 765 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 563 = 791 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 565 = 794 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 406 ≤ i) (hii : i ≤ 433) :
    Artifact.submissionArtifact.instructionPC i =
      [578,579,581,582,584,585,586,588,589,592,593,595,596,597,598,600,601,602,604,605,606,608,609,611,612,613,614,615][i - 406]! := by
  have hsplit : i = 406 + (i - 406) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 434 ≤ i) (hii : i ≤ 474) :
    Artifact.submissionArtifact.instructionPC i =
      [616,617,619,620,621,624,625,627,628,629,630,631,632,633,634,635,636,637,639,640,641,642,643,645,646,647,650,651,652,655,656,657,659,660,663,664,666,667,668,669,672][i - 434]! := by
  have hsplit : i = 434 + (i - 434) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 475 ≤ i) (hii : i ≤ 503) :
    Artifact.submissionArtifact.instructionPC i =
      [673,674,677,678,681,682,683,684,685,686,687,688,689,692,693,694,695,697,698,700,701,702,703,704,706,707,708,709,710][i - 475]! := by
  have hsplit : i = 475 + (i - 475) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 504 ≤ i) (hii : i ≤ 534) :
    Artifact.submissionArtifact.instructionPC i =
      [711,713,714,715,716,717,718,720,721,722,723,724,725,727,728,729,730,731,732,734,735,736,737,738,739,741,742,743,744,745,746][i - 504]! := by
  have hsplit : i = 504 + (i - 504) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 535 ≤ i) (hii : i ≤ 540) :
    Artifact.submissionArtifact.instructionPC i =
      [747,748,749,750,751,754][i - 535]! := by
  have hsplit : i = 535 + (i - 535) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 541 ≤ i) (hii : i ≤ 547) :
    Artifact.submissionArtifact.instructionPC i =
      [755,756,757,760,761,762,764][i - 541]! := by
  have hsplit : i = 541 + (i - 541) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9b (i : Nat) (hi : 548 ≤ i) (hii : i ≤ 562) :
    Artifact.submissionArtifact.instructionPC i =
      [765,766,772,774,775,776,779,780,781,782,784,785,787,788,790][i - 548]! := by
  have hsplit : i = 548 + (i - 548) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9b]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 563 ≤ i) (hii : i ≤ 564) :
    Artifact.submissionArtifact.instructionPC i =
      [791,792][i - 563]! := by
  have hsplit : i = 563 + (i - 563) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 565 ≤ i) (hii : i ≤ 577) :
    Artifact.submissionArtifact.instructionPC i =
      [794,795,796,799,800,801,804,806,807,808,809,811,812][i - 565]! := by
  have hsplit : i = 565 + (i - 565) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 533 = true :=
  Artifact.isValidJumpDest_index 372 (by rfl)

/-- The fixed-vector recogniser's entry, where the `msize` guard branch now lands. -/
theorem jumpDest795 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 765 = true :=
  Artifact.isValidJumpDest_index 548 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2389 = true :=
  Artifact.isValidJumpDest_index 1893 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 749 = true :=
  Artifact.isValidJumpDest_index 537 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 755 = true :=
  Artifact.isValidJumpDest_index 541 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 761 = true :=
  Artifact.isValidJumpDest_index 545 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3923 = true :=
  Artifact.isValidJumpDest_index 3095 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4048 = true :=
  Artifact.isValidJumpDest_index 3171 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4257 = true :=
  Artifact.isValidJumpDest_index 3322 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4246 = true :=
  Artifact.isValidJumpDest_index 3315 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
