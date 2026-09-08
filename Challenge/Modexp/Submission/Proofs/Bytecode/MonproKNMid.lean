import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidStore
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidProduct
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidPointers
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMid

open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNMidDefs
open MonproKNMidStore MonproKNMidProduct MonproKNMidPointers MonproKNMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_middle (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n)) :
    runInstructions midProgram
      (MonproKNRowFrames.middle s mem paj ptj c bi pa pb n i dst ret rest) =
    some (MonproKNRowFrames.l2 s (midMem mem c) bi (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 2077 dst ret rest) := by
  have hml' : MachineState.readWord (midMem mem c) 9408 = UInt256.ofNat (32*n-32) :=
    (read_mid mem c 9408 (Or.inr (by decide))).trans hml
  have htl' : MachineState.readWord (midMem mem c) 9440 = UInt256.ofNat (8224+32*n) :=
    (read_mid mem c 9440 (Or.inr (by decide))).trans htl
  have hmu := rowMu_mid mem c n hn
  have hc0 := rowC0_mid mem c n hn hn32
  have hp0 (p : Nat) : ptrAt p 0 = p := by simp [ptrAt]
  have trace := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_store { s with memory := mem } paj ptj c bi
        (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
        dst ret rest hcap hact)
      (run_product { s with memory := midMem mem c } n bi
        (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
        dst ret rest hcap hact hn hn32 hml' htl'))
    (run_pointers { s with memory := midMem mem c } n bi
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
      dst ret rest hcap hact hn hn32 hml' htl')
  rw [MonproKNMidDefs.program_eq]
  simpa only [input, stored, product, result, baseStack, framed, MonproKNRowFrames.middle,
    MonproKNRowFrames.l2, l2Step, hp0, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using trace

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMid
