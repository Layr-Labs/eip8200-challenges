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
    Artifact.submissionArtifact.instructionPC 423 = 599 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    Artifact.submissionArtifact.instructionPC 451 = 637 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    Artifact.submissionArtifact.instructionPC 492 = 694 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor3 :
    Artifact.submissionArtifact.instructionPC 521 = 731 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor4 :
    Artifact.submissionArtifact.instructionPC 553 = 771 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    Artifact.submissionArtifact.instructionPC 554 = 772 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    Artifact.submissionArtifact.instructionPC 560 = 780 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9b :
    Artifact.submissionArtifact.instructionPC 572 = 795 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    Artifact.submissionArtifact.instructionPC 587 = 821 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    Artifact.submissionArtifact.instructionPC 589 = 824 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 423 ≤ i) (hii : i ≤ 450) :
    Artifact.submissionArtifact.instructionPC i =
      [599,600,602,603,605,606,607,609,610,613,614,616,617,618,619,621,622,623,625,626,627,629,630,632,633,634,635,636][i - 423]! := by
  have hsplit : i = 423 + (i - 423) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 451 ≤ i) (hii : i ≤ 491) :
    Artifact.submissionArtifact.instructionPC i =
      [637,638,640,641,642,645,646,648,649,650,651,652,653,654,655,656,657,658,660,661,662,663,664,666,667,668,671,672,673,676,677,678,680,681,684,685,687,688,689,690,693][i - 451]! := by
  have hsplit : i = 451 + (i - 451) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 492 ≤ i) (hii : i ≤ 520) :
    Artifact.submissionArtifact.instructionPC i =
      [694,695,698,699,702,703,704,705,706,707,708,709,710,711,712,714,715,717,718,719,720,721,723,724,725,726,727,728,730][i - 492]! := by
  have hsplit : i = 492 + (i - 492) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC3 (i : Nat) (hi : 521 ≤ i) (hii : i ≤ 552) :
    Artifact.submissionArtifact.instructionPC i =
      [731,732,733,734,735,737,738,739,740,741,742,744,745,746,747,748,749,751,752,753,754,755,756,758,759,760,761,762,765,766,767,768][i - 521]! := by
  have hsplit : i = 521 + (i - 521) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor3]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC4 (i : Nat) (hi : 553 ≤ i) (hii : i ≤ 553) :
    Artifact.submissionArtifact.instructionPC i =
      [771][i - 553]! := by
  have hsplit : i = 553 + (i - 553) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor4]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i
  rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 554 ≤ i) (hii : i ≤ 559) :
    Artifact.submissionArtifact.instructionPC i =
      [772,773,774,775,776,779][i - 554]! := by
  have hsplit : i = 554 + (i - 554) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 560 ≤ i) (hii : i ≤ 571) :
    Artifact.submissionArtifact.instructionPC i =
      [780,781,782,783,784,785,786,789,790,791,793,794][i - 560]! := by
  have hsplit : i = 560 + (i - 560) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9b (i : Nat) (hi : 572 ≤ i) (hii : i ≤ 586) :
    Artifact.submissionArtifact.instructionPC i =
      [795,796,802,804,805,806,809,810,811,812,814,815,817,818,820][i - 572]! := by
  have hsplit : i = 572 + (i - 572) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9b]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 587 ≤ i) (hii : i ≤ 588) :
    Artifact.submissionArtifact.instructionPC i =
      [821,822][i - 587]! := by
  have hsplit : i = 587 + (i - 587) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 589 ≤ i) (hii : i ≤ 601) :
    Artifact.submissionArtifact.instructionPC i =
      [824,825,826,829,830,831,834,836,837,838,839,841,842][i - 589]! := by
  have hsplit : i = 589 + (i - 589) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 553 = true :=
  Artifact.isValidJumpDest_index 389 (by rfl)

/-- The fixed-vector recogniser's entry, where the `msize` guard branch now lands. -/
theorem jumpDest795 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 795 = true :=
  Artifact.isValidJumpDest_index 572 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2441 = true :=
  Artifact.isValidJumpDest_index 2011 (by rfl)

theorem jumpDest1802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 774 = true :=
  Artifact.isValidJumpDest_index 556 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 784 = true :=
  Artifact.isValidJumpDest_index 564 (by rfl)

theorem jumpDest1826 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 790 = true :=
  Artifact.isValidJumpDest_index 568 (by rfl)

theorem jumpDest4976 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4166 = true :=
  Artifact.isValidJumpDest_index 3325 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4333 = true :=
  Artifact.isValidJumpDest_index 3444 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4548 = true :=
  Artifact.isValidJumpDest_index 3601 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4537 = true :=
  Artifact.isValidJumpDest_index 3594 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
