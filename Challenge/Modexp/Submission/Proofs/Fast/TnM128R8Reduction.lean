import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R8Reduction

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory WindowTwentyOneBinding TnCacheReductionTrace
open Challenge.EvmProof

def l2PC : Nat := 3630

noncomputable def reduction_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi tn : UInt256)
    (pbi hd pb ent m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache q.memory 8 tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hi : inverseInvariant q.memory 8)
    (hcache : m128 = MachineState.readWord q.memory 128)
    (hpb : pb = MachineState.readWord q.memory 192)
    (hjd : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps
      (framed {s with memory := q.memory} (UInt256.ofNat 3607)
        ([q.carry,bi,pbi,hd,pb,ent,m32,allOnes,m128,m64,m0,tl,m96,inv,tn,aEnd,dst,ret] ++ rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
      (if UInt256.isTrue (UInt256.ofNat 32+pbi) then hd
       else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8+18))
      (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent
        m32 m128 m64
        (m0 :: tl :: m96 :: inv :: (TnCacheSquareModel.fromL1 q tn 8).tn :: aEnd :: dst :: ret :: rest))) := by
  let st : State := {s with memory := q.memory}
  let flag := UInt256.lt (tn+q.carry) q.carry
  let mem2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).memory
  let carry2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).carry
  let tl4 := aEnd :: dst :: ret :: rest
  have htl4 : tl4.length ≤ 1001 := by simp only [tl4, List.length_cons]; omega
  let tail := m0 :: tl :: m96 :: inv :: (tn+q.carry) :: tl4
  have hmid := TnCacheRowTrace.run_middle8 3607 st q.carry bi pbi hd pb ent tn
    m128 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hc hi
  have hmidRun : runInstructions TnCacheRowTrace.middle8
      (framed st (UInt256.ofNat 3607)
        ([q.carry,bi,pbi,hd,pb,ent,m32,allOnes,m128,m64,m0,tl,m96,inv,tn,aEnd,dst,ret] ++ rest)) =
      some (TnCacheL2Trace.state st (UInt256.ofNat l2PC) q.memory flag
        (rowMu q.memory 8) (rowC0 q.memory 8) 8 0 pbi hd pb ent m32
        m128 m64 tail) := by
    simpa only [TnCacheL2Trace.state, l2Step, tail, tl4, st, framed, l2PC,
      List.cons_append, List.nil_append] using hmid
  have hreduce := TnMod128Chain.run_full st (l2PC) q.memory flag (rowMu q.memory 8)
    (rowC0 q.memory 8) 8 (Or.inr rfl) pbi hd pb ent (tn+q.carry) m128
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact he hcache (fun _ => hc.modulusLow) (fun _ => hpb)
  have htailrun := TnCacheRowTrace.run_tail ((l2PC)+TnMod128Chain.fullSize 8)
    {s with memory := mem2} carry2 flag pbi hd pb ent m32
    m128 m64 m0 tl m96 inv (tn+q.carry) tl4 htl4 hact hjd
  have hflag : UInt256.lt (tn+q.carry+carry2) carry2+flag =
      flag+UInt256.lt (tn+q.carry+carry2) carry2 := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add, Nat.add_comm]
  rw [hflag] at htailrun
  have hlast : runInstructions TnCacheRowTrace.tail
      (TnCacheLastTrace.lastState st (UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent m32 m128 m64 tail) =
      some (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
        (if UInt256.isTrue (UInt256.ofNat 32+pbi) then hd
         else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8+18))
        (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent
          m32 m128 m64 (m0 :: tl :: m96 :: inv :: (TnCacheSquareModel.fromL1 q tn 8).tn :: tl4))) := by
    simpa only [TnCacheLastTrace.lastState, tail, tl4, st, framed, mem2, carry2,
      TnCacheSquareModel.fromL1, flag, List.cons_append, List.nil_append] using htailrun
  have g0 := TnM128CandidateBlocks.middle8.steps
    (s := framed st (UInt256.ofNat 3607)
      ([q.carry,bi,pbi,hd,pb,ent,m32,allOnes,m128,m64,
        m0,tl,m96,inv,tn,aEnd,dst,ret] ++ rest))
    (env.transfer rfl rfl) rfl hmidRun
  have g1 : GasSteps
      (TnCacheL2Trace.state st (UInt256.ofNat (l2PC)) q.memory flag
        (rowMu q.memory 8) (rowC0 q.memory 8) 8 0 pbi hd pb ent m32
        m128 m64 tail)
      (TnCacheLastTrace.lastState st (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent m32 m128 m64 tail) := by
    exact TnM128CandidateBlocks.l2Eight.steps (env.transfer rfl rfl) rfl hreduce
  have hpc : (TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent m32 m128 m64 tail).pc =
      UInt256.ofNat 3856 := by
    change UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8) = UInt256.ofNat 3856
    rfl
  have g2 := TnM128CandidateBlocks.tail.steps
    (s := TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent m32 m128 m64 tail)
    (env.transfer rfl rfl) hpc hlast
  simpa only [st, tail, tl4] using (g0.trans g1).trans g2

end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8Reduction
