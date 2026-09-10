import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTracesPart01

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open CiosCachedMidMemory Monpro

theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions fullMidProgram
      (CiosCached.midState s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 4578 s (midMem mem c) bi (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmu := rowMu_mid mem c n hn
  have hc0 := rowC0_mid mem c n hn hn32
  have trace := runInstructions_append_some _ _ _ _ _
    (CiosCachedMidStore.run_store { s with memory := mem } c bi
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
      (l1Target n) (l2Target n) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact)
    (run_cachedProduct_model { s with memory := midMem mem c }
      bi (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
      (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn32 hact
      (hc.middle hn32 c) (inverse_midMem mem c n hn32 hminv))
  change runInstructions (storeProgram ++ cachedProduct) _ = _
  simpa only [input, stored, cacheStack, baseStack, framed,
    CiosCached.midState, CiosCached.l2At, l2Step, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using trace

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
