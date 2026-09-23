import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R8SuffixSteps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory WindowTwentyOneBinding TnCacheReductionTrace
open Challenge.EvmProof

def l2PC : Nat := 3841

/-- The current eight-limb fallthrough middle, seven reduction cells, and
long-immediate tail implement the carry-cache model for arbitrary carry words. -/
noncomputable def suffix_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (tn : UInt256)
    (pbi hd pb ent m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hcache : m128 = MachineState.readWord q.memory 128)
    (hjd : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps
      (TnCacheL2Trace.state {s with memory := q.memory} (UInt256.ofNat l2PC)
        q.memory (UInt256.lt (tn+q.carry) q.carry) (rowMu q.memory 8) (rowC0 q.memory 8)
        8 0 pbi hd pb ent (tn+q.carry) m128 inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
       else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8+51))
      (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
        (TnCacheSquareModel.fromL1 q tn 8).tn m128 inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  let st : State := {s with memory := q.memory}
  let flag := UInt256.lt (tn+q.carry) q.carry
  let mem2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).memory
  let carry2 := (l2Step q.memory (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)).carry
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hreduce := TnMod128Chain.run_full st (l2PC) q.memory flag (rowMu q.memory 8)
    (rowC0 q.memory 8) 8 (Or.inr rfl) pbi hd pb ent (tn+q.carry) m128
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact he hcache
  have htailrun := TnCacheRowTrace.run_tail ((l2PC)+TnMod128Chain.fullSize 8)
    {s with memory := mem2} carry2 flag pbi hd pb ent (tn+q.carry)
    m128 inv tail htail hact hjd
  have hflag : UInt256.lt (tn+q.carry+carry2) carry2+flag =
      flag+UInt256.lt (tn+q.carry+carry2) carry2 := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add, Nat.add_comm]
  rw [hflag] at htailrun
  have hlast : runInstructions TnCacheRowTrace.tail
      (TnCacheLastTrace.lastState st (UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent (tn+q.carry) m128 inv tail) =
      some (framed {s with memory := (TnCacheSquareModel.fromL1 q tn 8).memory}
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
         else UInt256.ofNat ((l2PC)+TnMod128Chain.fullSize 8+51))
        (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
          (TnCacheSquareModel.fromL1 q tn 8).tn m128 inv tail)) := by
    simpa only [TnCacheLastTrace.lastState, st, framed, mem2, carry2,
      TnCacheSquareModel.fromL1, flag] using htailrun
  have g1 : GasSteps
      (TnCacheL2Trace.state st (UInt256.ofNat (l2PC)) q.memory flag
        (rowMu q.memory 8) (rowC0 q.memory 8) 8 0 pbi hd pb ent (tn+q.carry)
        m128 inv tail)
      (TnCacheLastTrace.lastState st (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8))
        q.memory flag (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
        pbi hd pb ent (tn+q.carry) m128 inv tail) := by
    exact TnM128CandidateBlocks.l2Eight.steps (env.transfer rfl rfl) rfl hreduce
  have hpc : (TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent (tn+q.carry) m128 inv tail).pc =
      UInt256.ofNat 4077 := by
    change UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8) = UInt256.ofNat 4077
    rfl
  have g2 := TnM128CandidateBlocks.tail.steps
    (s := TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC+TnMod128Chain.fullSize 8)) q.memory flag
      (rowMu q.memory 8) (rowC0 q.memory 8) 8 (8-1)
      pbi hd pb ent (tn+q.carry) m128 inv tail)
    (env.transfer rfl rfl) hpc hlast
  simpa only [st, tail] using g1.trans g2

#print axioms suffix_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8SuffixSteps
