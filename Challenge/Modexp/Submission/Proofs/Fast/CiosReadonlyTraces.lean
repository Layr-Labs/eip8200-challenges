import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryBody
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidStore

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open CiosCachedMidMemory Monpro

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions fullEntryProgram (entryState s mem pa pb dst ret rest) =
    some (outState s (mpZeroed s mem n) pa pb n 0
      (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
      (MachineState.readWord mem 9440 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 :: MachineState.readWord mem 32 :: UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  let tl := MachineState.readWord mem 9440
  let inv := MachineState.readWord mem 9376
  let m0 := MachineState.readWord mem (32*n-32)
  let aEnd := UInt256.ofNat (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by simp only [List.length_cons]; omega
  have hreads := EntryPrefix.run_load { s with memory := mem }
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32)
    hcap hact (by omega) hml
  have hAend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = aEnd := by
    dsimp [aEnd]
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  rw [hAend] at hreads
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem }
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 inv aEnd tl m96 m64 m32
    (EntryPrefix.displacement mem) rest hcap
  have hprefix := runInstructions_append_some _ _ _ _ _ hreads hshuffle
  have hmasked :
      runInstructions (EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram)
        (entryState s mem pa pb dst ret rest) =
      some (cachedEntryState s mem pa pb n inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
    simpa only [entryState, cachedEntryState, EntryPrefix.displacement,
      hs32, l1Target, l2Target, isFour, tl, inv, m0, aEnd, m96, m64, m32,
      List.cons_append, List.nil_append] using hprefix
  have hbody := CiosCached.run_entryBody s mem pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hcap' hrun hact hn hn32 hpa hpaFit hpb hpbFit hcds hs32
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

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

theorem run_exit (s : State) (pbi paEnd pbEnd flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4978 = true) :
    runInstructions fullExitProgram
      (framed s (UInt256.ofNat 4870)
        ([pbi,paEnd,pbEnd,flag,negative32,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4978) ([dst,ret] ++ rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hc15 : rest.length+15 < 1024 := by omega
  have hc16 : rest.length+16 < 1024 := by omega
  simp [fullExitProgram, dropCache, CiosCached.tailProgram, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14,hc15,hc16,
    htarget, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
