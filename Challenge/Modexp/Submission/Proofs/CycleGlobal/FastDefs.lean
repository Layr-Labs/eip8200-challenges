import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.ProofSupport
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
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
    CycleSubmission.Artifact.artifact.instructionPC 400 = 578 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 428 = 616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 465 = 671 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 477 = 690 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 483 = 697 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 485 = 699 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 499 = 724 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 501 = 727 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 400 ≤ i) (hii : i ≤ 427) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([578, 579, 581, 582, 584, 585, 586, 588, 589, 592, 593, 595, 596, 597, 598, 600, 601, 602, 604, 605, 606, 608, 609, 611, 612, 613, 614, 615] : List Nat)[i - 400]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 428 ≤ i) (hii : i ≤ 464) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([616, 617, 619, 620, 621, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 637, 638, 639, 642, 643, 644, 645, 648, 649, 650, 653, 654, 655, 657, 658, 661, 662, 664, 665, 666, 670] : List Nat)[i - 428]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 465 ≤ i) (hii : i ≤ 476) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([671, 672, 675, 676, 677, 678, 679, 680, 681, 682, 683, 689] : List Nat)[i - 465]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 477 ≤ i) (hii : i ≤ 482) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([690, 691, 692, 693, 695, 696] : List Nat)[i - 477]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 483 ≤ i) (hii : i ≤ 484) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([697, 698] : List Nat)[i - 483]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 485 ≤ i) (hii : i ≤ 498) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([699, 705, 707, 708, 709, 712, 713, 714, 715, 717, 718, 720, 721, 723] : List Nat)[i - 485]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 499 ≤ i) (hii : i ≤ 500) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([724, 725] : List Nat)[i - 499]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 501 ≤ i) (hii : i ≤ 509) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([727, 728, 729, 732, 733, 735, 740, 741, 742] : List Nat)[i - 501]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 533 = true :=
  CycleSubmission.Global.Binding.jumpDest 366 (by rfl)
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2317 = true :=
  CycleSubmission.Global.Binding.jumpDest 1826 (by rfl)
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3534 = true :=
  CycleSubmission.Global.Binding.jumpDest 2665 (by rfl)
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 698 = true :=
  CycleSubmission.Global.Binding.jumpDest 484 (by rfl)
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3769 = true :=
  CycleSubmission.Global.Binding.jumpDest 2838 (by rfl)
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3758 = true :=
  CycleSubmission.Global.Binding.jumpDest 2831 (by rfl)
end CycleSubmission.Global.Fast
