import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located-instruction helpers for the appended fast path

The tables and jump facts below describe the selected round06 layout.
Each table uses a proved prefix-sum anchor and a bounded local slice.
-/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

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
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
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
    CycleSubmission.Artifact.artifact.instructionPC 404 = 578 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 432 = 616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 473 = 671 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 486 = 690 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 491 = 697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 493 = 699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 507 = 724 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 509 = 727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fastPC0 (i : Nat) (hi : 404 ≤ i) (hii : i ≤ 431) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [578,579,581,582,584,585,586,588,589,592,593,595,596,597,598,600,601,602,604,605,606,608,609,611,612,613,614,615][i - 404]! := by
  have hsplit : i = 404 + (i - 404) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor0]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC1 (i : Nat) (hi : 432 ≤ i) (hii : i ≤ 472) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [616,617,619,620,621,623,624,626,627,628,629,630,631,632,633,634,635,636,638,639,640,641,642,644,645,646,648,649,650,653,654,655,657,658,661,662,664,665,666,667,670][i - 432]! := by
  have hsplit : i = 432 + (i - 432) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor1]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC2 (i : Nat) (hi : 473 ≤ i) (hii : i ≤ 485) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [671,672,675,676,679,680,681,682,683,684,685,686,689][i - 473]! := by
  have hsplit : i = 473 + (i - 473) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor2]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC8 (i : Nat) (hi : 486 ≤ i) (hii : i ≤ 490) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [690,691,692,693,696][i - 486]! := by
  have hsplit : i = 486 + (i - 486) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor8]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9 (i : Nat) (hi : 491 ≤ i) (hii : i ≤ 492) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [697,698][i - 491]! := by
  have hsplit : i = 491 + (i - 491) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC9b (i : Nat) (hi : 493 ≤ i) (hii : i ≤ 506) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [699,705,707,708,709,712,713,714,715,717,718,720,721,723][i - 493]! := by
  have hsplit : i = 493 + (i - 493) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor9b]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC10 (i : Nat) (hi : 507 ≤ i) (hii : i ≤ 508) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [724,725][i - 507]! := by
  have hsplit : i = 507 + (i - 507) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor10]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

@[simp] theorem fastPC15 (i : Nat) (hi : 509 ≤ i) (hii : i ≤ 520) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [727,728,729,732,733,736,738,739,740,741,743,744][i - 509]! := by
  have hsplit : i = 509 + (i - 509) := by omega
  conv_lhs => rw [hsplit, instructionPC_add, fastPCAnchor15]
  rw [← PCFast.byteLength_eq_assemble]
  interval_cases i <;> rfl

theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 533 = true :=
  CycleSubmission.Global.Binding.jumpDest 370 (by rfl)

theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2317 = true :=
  CycleSubmission.Global.Binding.jumpDest 1835 (by rfl)

theorem jumpDest1812 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 697 = true :=
  CycleSubmission.Global.Binding.jumpDest 491 (by rfl)

theorem jumpDestSub : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3508 = true :=
  CycleSubmission.Global.Binding.jumpDest 2721 (by rfl)

theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3717 = true :=
  CycleSubmission.Global.Binding.jumpDest 2872 (by rfl)

theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3706 = true :=
  CycleSubmission.Global.Binding.jumpDest 2865 (by rfl)

end CycleSubmission.Global.Fast
