import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidStore
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidProduct
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMid

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedMidDefs
open CiosCachedMidStore CiosCachedMidProduct CiosCachedMidMemory
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hminv : inverseInvariant mem n) :
    runInstructions midProgram
      (CiosCached.midState s mem c bi pa pb n i dst ret rest) =
    some (CiosCached.l2At 4889 s (midMem mem c) bi (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 dst ret rest) := by
  have hml' : MachineState.readWord (midMem mem c) 9408 = UInt256.ofNat (32*n-32) :=
    (read_mid mem c 9408 (Or.inr (by decide))).trans hml
  have htl' : MachineState.readWord (midMem mem c) 9440 = UInt256.ofNat (8224+32*n) :=
    (read_mid mem c 9440 (Or.inr (by decide))).trans htl
  have hminv' := inverse_midMem mem c n hn32 hminv
  have hmu := rowMu_mid mem c n hn
  have hc0 := rowC0_mid mem c n hn hn32
  have trace := runInstructions_append_some _ _ _ _ _
    (run_store { s with memory := mem } c bi
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
      (l1Target n) (l2Target n) (modulusAddress n) (dst :: ret :: rest) (by simp only [List.length_cons]; omega) hact)
    (run_product { s with memory := midMem mem c } n bi
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
      (l1Target n) (l2Target n) (modulusAddress n) (dst :: ret :: rest) (by simp only [List.length_cons]; omega) hact hn hn32 hml' htl' hminv' rfl)
  rw [CiosCachedMidDefs.program_eq]
  simpa only [List.cons_append, List.nil_append, input, stored, product, baseStack, framed, CiosCached.midState,
    CiosCached.l2At, l2Step, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using trace

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMid
