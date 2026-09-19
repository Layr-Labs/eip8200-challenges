import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R4Reduction

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory WindowTwentyOneBinding TnCacheReductionTrace
open Challenge.EvmProof

def l2PC : Nat := 3987

/-- The exact four-limb reduction of the modulus-cache candidate, preserving
its cached modulus word separately from the literal reduction entry. -/
noncomputable def reduction_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi tn : UInt256)
    (pbi hd pb ent m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache q.memory 4 tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hi : inverseInvariant q.memory 4)
    (hcache : m128 = MachineState.readWord q.memory 128)
    (hjd : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps
      (framed {s with memory := q.memory} (UInt256.ofNat 5431)
        ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 4).memory}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
       else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 4+51))
      (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
        (TnCacheSquareModel.fromL1 q tn 4).tn m128 inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  let st : State := {s with memory := q.memory}
  let flag := UInt256.lt (tn+q.carry) q.carry
  let mem2 := (l2Step q.memory (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)).memory
  let carry2 := (l2Step q.memory (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)).carry
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hmid := TnCacheRowTrace.run_middle 5431 st q.carry bi pbi hd pb ent tn
    m128 tl inv m0 aEnd m96 m64 m32 dst ret 4 rest hcap (by omega) hact hc hi
  have hmidRun : runInstructions (TnCacheRowTrace.middle ++ [.push 2 3987, .op .JUMP])
      (framed st (UInt256.ofNat 5431)
        ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
      some (TnCacheL2Trace.state st (UInt256.ofNat l2PC) q.memory flag
        (rowMu q.memory 4) (rowC0 q.memory 4) 4 0 pbi hd pb ent (tn+q.carry)
        m128 inv tail) := by
    have hj : Decode.isValidJumpDest s.executionEnv.code 3987 = true := by
      rw [env.code]
      exact TnM128CandidateArtifact.isValidJumpDest_index 3199 (by rfl)
    have h19 : rest.length+19 < 1024 := by omega
    have h20 : rest.length+20 < 1024 := by omega
    have hjump : runInstructions [.push 2 3987, .op .JUMP]
        (framed st (UInt256.ofNat 5450)
          ([rowC0 q.memory 4,rowMu q.memory 4,flag,pbi,hd,pb,ent,tn+q.carry,allOnes,
            m128,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
        some (TnCacheL2Trace.state st (UInt256.ofNat l2PC) q.memory flag
          (rowMu q.memory 4) (rowC0 q.memory 4) 4 0 pbi hd pb ent (tn+q.carry)
          m128 inv tail) := by
      simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
        TnCacheL2Trace.state, l2Step, l2PC, tail, st, h19, h20, hj,
        Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact runInstructions_append_some _ _ _ _ _ hmid hjump
  have hreduce := TnMod128Chain.run_full st (l2PC) q.memory flag (rowMu q.memory 4)
    (rowC0 q.memory 4) 4 (Or.inl rfl) pbi hd pb ent (tn+q.carry) m128
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact he hcache
  have htailrun := TnCacheRowTrace.run_tail ((l2PC)+TnMod128Chain.fullSize 4)
    {s with memory := mem2} carry2 flag pbi hd pb ent (tn+q.carry)
    m128 inv tail htail hact hjd
  have hflag : UInt256.lt (tn+q.carry+carry2) carry2+flag =
      flag+UInt256.lt (tn+q.carry+carry2) carry2 := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add, Nat.add_comm]
  rw [hflag] at htailrun
  have hlast : runInstructions TnCacheRowTrace.tail
      (TnCacheLastTrace.lastState st (UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 4))
        q.memory flag (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)
        pbi hd pb ent (tn+q.carry) m128 inv tail) =
      some (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 4).memory}
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
         else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 4+51))
        (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
          (TnCacheSquareModel.fromL1 q tn 4).tn m128 inv tail)) := by
    simpa only [TnCacheLastTrace.lastState, st, framed, mem2, carry2,
      TnCacheSquareModel.fromL1, flag] using htailrun
  have g0 := TnM128CandidateBlocks.middleCopy.steps
    (s := framed st (UInt256.ofNat 5431)
      ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,
        m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest))
    (env.transfer rfl rfl) rfl hmidRun
  have g1 : GasSteps
      (TnCacheL2Trace.state st (UInt256.ofNat l2PC) q.memory flag
        (rowMu q.memory 4) (rowC0 q.memory 4) 4 0 pbi hd pb ent (tn+q.carry)
        m128 inv tail)
      (TnCacheLastTrace.lastState st (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 4))
        q.memory flag (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)
        pbi hd pb ent (tn+q.carry) m128 inv tail) := by
    exact TnM128CandidateBlocks.l2Four.steps (env.transfer rfl rfl) rfl hreduce
  have hpc : (TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 4)) q.memory flag
      (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)
      pbi hd pb ent (tn+q.carry) m128 inv tail).pc =
      UInt256.ofNat 4087 := by
    change UInt256.ofNat (l2PC+TnMod128Chain.fullSize 4) = UInt256.ofNat 4087
    rfl
  have g2 := TnM128CandidateBlocks.tail.steps
    (s := TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 4)) q.memory flag
      (rowMu q.memory 4) (rowC0 q.memory 4) 4 (4-1)
      pbi hd pb ent (tn+q.carry) m128 inv tail)
    (env.transfer rfl rfl) hpc hlast
  simpa only [st, tail] using (g0.trans g1).trans g2

#print axioms reduction_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R4Reduction
