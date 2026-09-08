import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceHead

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

@[simp] private theorem advanceHeadPCs (index : Nat)
    (hlo : 2319 ≤ index) (hhi : index ≤ 2321) :
    Artifact.submissionArtifact.instructionPC index =
      [3547, 3548, 3550][index - 2319]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
theorem run (template : State)
    (word pointer accumulator modulus : UInt256) (rest : List UInt256)
    (pointerNat : Nat) (hpointerWord : pointer = UInt256.ofNat pointerNat)
    (hpointer : pointerNat < 160) (hrest : rest.length ≤ 1000)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (loopAdvancePath.take 3)
      (framed template 3547 (word :: pointer :: accumulator :: modulus :: rest)) =
    some (framed template 3551
      (UInt256.ofNat (pointerNat + 4) :: accumulator :: modulus :: rest)) := by
  have hlt : pointerNat + 4 < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 4) (b := pointerNat) (by omega)
  have hadd' : UInt256.ofNat 4 + UInt256.ofNat pointerNat =
      UInt256.ofNat (pointerNat + 4) := by
    simpa only [Nat.add_comm] using hadd
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  simp (disch := omega) [loopAdvancePath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, hpointerWord,
    advanceHeadPCs, List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc,
    hrest, hcap3, hcap4, hcap5, hadd',
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceHead
