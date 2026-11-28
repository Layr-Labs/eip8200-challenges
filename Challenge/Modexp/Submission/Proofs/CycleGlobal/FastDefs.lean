import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
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
  ⟨hopcode,hplain,havailable⟩
def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).1)
    (hplain : YulEvmCompiler.plainOp op := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.1)
    (havailable : op.availableInFork .Osaka = true := (CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)).2.2) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.op op,hget,wfOp hopcode hplain havailable⟩
def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rw [CycleSubmission.Artifact.instruction_get]; rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := CycleSubmission.Artifact.wellFormed.valid (List.mem_of_getElem? hget)) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.push width value,hget,hwf⟩
private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,List.take_add,
    assembleBytes_append,List.length_append]
private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one,hget,Option.toList_some,assembleBytes_append,
    assembleBytes_cons,assembleBytes_nil,List.append_nil,List.length_append]
private theorem fastPCAnchor0 :
    CycleSubmission.Artifact.artifact.instructionPC 389 = 530 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor1 :
    CycleSubmission.Artifact.artifact.instructionPC 417 = 568 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor2 :
    CycleSubmission.Artifact.artifact.instructionPC 454 = 615 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor8 :
    CycleSubmission.Artifact.artifact.instructionPC 632 = 865 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9 :
    CycleSubmission.Artifact.artifact.instructionPC 632 = 865 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor9b :
    CycleSubmission.Artifact.artifact.instructionPC 633 = 866 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor10 :
    CycleSubmission.Artifact.artifact.instructionPC 643 = 888 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
private theorem fastPCAnchor15 :
    CycleSubmission.Artifact.artifact.instructionPC 644 = 890 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem fastPC0 (i : Nat) (hi : 389 ≤ i) (hii : i ≤ 416) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([530,531,533,534,536,537,538,540,541,544,545,547,548,549,550,552,553,554,556,557,558,560,561,563,564,565,566,567] : List Nat)[i - 389]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC1 (i : Nat) (hi : 417 ≤ i) (hii : i ≤ 453) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([568,569,570,571,572,574,575,576,577,578,579,580,581,582,583,584,586,587,588,590,591,592,593,595,596,597,599,600,603,604,605,606,607,611,612,613,614] : List Nat)[i - 417]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC2 (i : Nat) (hi : 454 ≤ i) (hii : i ≤ 632) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([615,616,619,620,621,622,623,624,625,626,627,628,629,631,632,633,635,638,639,640,641,644,645,646,649,650,653,656,659,660,662,663,666,667,670,671,673,674,675,676,677,680,681,682,683,685,686,687,688,691,692,693,694,695,698,699,700,701,702,703,704,706,707,708,709,712,713,714,715,716,719,720,721,722,723,724,725,727,728,729,730,733,734,735,736,737,740,741,742,743,744,745,746,748,749,750,751,754,755,756,757,758,761,762,763,764,765,766,767,768,770,771,772,773,776,777,778,779,780,783,784,785,786,787,788,789,791,792,793,794,797,798,799,800,801,804,805,806,807,808,809,810,811,812,813,814,817,818,819,820,821,824,825,826,827,828,829,830,833,834,835,838,839,842,843,844,847,850,851,852,853,854,855,858,861,862,863,864,865] : List Nat)[i - 454]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC8 (i : Nat) (hi : 632 ≤ i) (hii : i ≤ 632) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([865] : List Nat)[i - 632]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9 (i : Nat) (hi : 632 ≤ i) (hii : i ≤ 632) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([865] : List Nat)[i - 632]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC9b (i : Nat) (hi : 633 ≤ i) (hii : i ≤ 643) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([866,868,869,871,872,873,875,876,877,887,888] : List Nat)[i - 633]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem fastPC10 (i : Nat) (hi : 643 ≤ i) (hii : i ≤ 643) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([888] : List Nat)[i - 643]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i; rfl
@[simp] theorem fastPC15 (i : Nat) (hi : 644 ≤ i) (hii : i ≤ 654) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([890,891,892,895,896,929,930,931,932,933,934] : List Nat)[i - 644]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDest1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 485 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 355
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest3412 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2501 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1963
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest1812 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10322 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 7805
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDest698 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 865 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 632
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestCopyResume : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 854 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 625
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
theorem jumpDestEarlyCopy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 843 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 618
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast
