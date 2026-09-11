import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirst
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirstModel
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosReadonly CiosCarryFirst
variable {carrySlot : UInt256}

/-- Both admitted widths have zero carry at the first limb of each row. -/
theorem run_commonFirst (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (_hpaFit : pa+32*n ≤ 9472)
    (htl : tl = UInt256.ofNat (8224+32*n))
    (hAend : aEnd = MachineState.readWord mem (pa+32*(n-1))) :
    runInstructions commonFirstProgram
      (CiosCarryFrames.firstAt (carrySlot := carrySlot) 4255 s mem bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCarryFrames.l1At (carrySlot := carrySlot) 4278 s mem bi pa pb n i 1 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have ht : tl.toNat = 8256+32*(n-1) := by
    rw [htl,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  let st : State := {s with memory := mem}
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) = st.activeWords := by
    rw [ht]
    exact activeWords_fix st _ 32 (by decide) (by omega) hact
  let pbi := UInt256.ofNat (ptrAt (pb+32*n-32) i)
  let frame := tail (carrySlot := carrySlot) pbi (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (CiosCarryFrames.l1Target n) (CiosCarryFrames.l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hl := run_load (carrySlot := carrySlot) st (UInt256.ofNat 4255) bi pbi (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (CiosCarryFrames.l1Target n) (CiosCarryFrames.l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap
  have hp := CiosNoDummyCarry.run_multiply st (advancePC 2 (UInt256.ofNat 4255))
    (aEnd) bi frame
    (by simp only [frame,tail,List.length_append,List.length_cons,List.length_nil]; omega)
  have hf := run_finish (carrySlot := carrySlot) st (advancePC 6 (advancePC 2 (UInt256.ofNat 4255)))
    (aEnd) bi pbi (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (CiosCarryFrames.l1Target n) (CiosCarryFrames.l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 15 (advancePC 6 (advancePC 2 (UInt256.ofNat 4255))) = UInt256.ofNat 4278 := by decide
  simpa only [commonFirstProgram,show (0 : UInt256) = UInt256.ofNat 0 from by decide,st,frame,pbi,tail,CiosCarryFrames.firstAt,CiosCarryFrames.l1At,l1Step,
    framed,hAend,ht,hpc,Nat.sub_zero,List.cons_append,List.nil_append] using hall


#print axioms run_commonFirst

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirstModel
