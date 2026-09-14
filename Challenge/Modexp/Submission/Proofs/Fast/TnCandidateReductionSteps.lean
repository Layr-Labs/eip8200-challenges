import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateBlocks

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateReductionSteps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory WindowTwentyOneBinding TnCacheReductionTrace
open Challenge.EvmProof

def l2PC (n : Nat) : Nat := if n = 4 then 4171 else 4023

theorem l2_end (n : Nat) (hn : n = 4 ∨ n = 8) :
    l2PC n + TnCacheL2Chain.fullSize n = 4271 := by
  rcases hn with rfl | rfl <;> rfl

/-- The candidate's actual three reduction blocks implement the cache model.
Every transition is a GasSteps transition for the exact 5,309-byte artifact. -/
noncomputable def reduction_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (q : MacState) (bi tn : UInt256)
    (n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi hd pb ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache q.memory n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache q.memory m96 m64 m32)
    (hi : inverseInvariant q.memory n)
    (hjd : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps
      (framed {s with memory := q.memory} (UInt256.ofNat 4000)
        ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,UInt256.ofNat (l2PC n),inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest))
      (framed {s with memory := (TnCacheSquareModel.fromL1 q tn n).memory}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
       else UInt256.ofNat ((l2PC n)+TnCacheL2Chain.fullSize n+21))
      (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
        (TnCacheSquareModel.fromL1 q tn n).tn (UInt256.ofNat (l2PC n)) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  have hl2 : l2PC n < 2^256 := by unfold l2PC; split <;> omega
  have hj : Decode.isValidJumpDest s.executionEnv.code (l2PC n) = true := by
    rw [env.code]
    rcases hn with rfl | rfl
    · exact TnCandidateArtifact.isValidJumpDest_index 3147 (by rfl)
    · exact TnCandidateArtifact.isValidJumpDest_index 3028 (by rfl)
  let st : State := {s with memory := q.memory}
  let flag := UInt256.lt (tn+q.carry) q.carry
  let mem2 := (l2Step q.memory (rowMu q.memory n) (rowC0 q.memory n) n (n-1)).memory
  let carry2 := (l2Step q.memory (rowMu q.memory n) (rowC0 q.memory n) n (n-1)).carry
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  have htail : tail.length ≤ 1006 := by simp only [tail, List.length_cons]; omega
  have hmid := TnCacheRowTrace.run_middle 4000 st q.carry bi pbi hd pb ent tn
    (UInt256.ofNat (l2PC n)) tl inv m0 aEnd m96 m64 m32 dst ret n rest hcap (by omega) hact hc hi
  have htarget : (UInt256.ofNat (l2PC n)).toNat = (l2PC n) := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hl2]
  have hjump : runInstructions dispatch
      (framed st (UInt256.ofNat (4000+21))
        ([rowC0 q.memory n,rowMu q.memory n,flag,pbi,hd,pb,ent,tn+q.carry,allOnes,
          UInt256.ofNat (l2PC n),inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
      some (TnCacheL2Trace.state st (UInt256.ofNat (l2PC n)) q.memory flag
        (rowMu q.memory n) (rowC0 q.memory n) n 0 pbi hd pb ent (tn+q.carry)
        (UInt256.ofNat (l2PC n)) inv tail) := by
    have h19 : rest.length+19 < 1024 := by omega
    have h20 : rest.length+20 < 1024 := by omega
    simp [dispatch, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      framed, TnCacheL2Trace.state, l2Step, tail, st, h19, h20, htarget, hj]
  have hreduce := TnCacheL2Chain.run_full st (l2PC n) q.memory flag (rowMu q.memory n)
    (rowC0 q.memory n) n hn pbi hd pb ent (tn+q.carry) (UInt256.ofNat (l2PC n))
    tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact he
  have htailrun := TnCacheRowTrace.run_tailShort ((l2PC n)+TnCacheL2Chain.fullSize n)
    {s with memory := mem2} carry2 flag pbi hd pb ent (tn+q.carry)
    (UInt256.ofNat (l2PC n)) inv tail htail hact hjd
  have hflag : UInt256.lt (tn+q.carry+carry2) carry2+flag =
      flag+UInt256.lt (tn+q.carry+carry2) carry2 := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add, Nat.add_comm]
  have h01 := runInstructions_append_some _ _ _ _ _ hmid hjump
  rw [hflag] at htailrun
  have hlast : runInstructions TnCacheRowTrace.tailShort
      (TnCacheLastTrace.lastState st (UInt256.ofNat ((l2PC n)+TnCacheL2Chain.fullSize n))
        q.memory flag (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
        pbi hd pb ent (tn+q.carry) (UInt256.ofNat (l2PC n)) inv tail) =
      some (framed {s with memory := (TnCacheSquareModel.fromL1 q tn n).memory}
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd
         else UInt256.ofNat ((l2PC n)+TnCacheL2Chain.fullSize n+21))
        (TnCacheFrameOps.frame (negative32+pbi) hd pb ent
          (TnCacheSquareModel.fromL1 q tn n).tn (UInt256.ofNat (l2PC n)) inv tail)) := by
    simpa only [TnCacheLastTrace.lastState, st, framed, mem2, carry2,
      TnCacheSquareModel.fromL1, flag] using htailrun
  have g0 := TnCandidateBlocks.middle.steps
    (s := framed st (UInt256.ofNat 4000)
      ([q.carry,bi,pbi,hd,pb,ent,tn,allOnes,UInt256.ofNat (l2PC n),inv,
        m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest))
    (env.transfer rfl rfl) rfl h01
  have g1 : GasSteps
      (TnCacheL2Trace.state st (UInt256.ofNat (l2PC n)) q.memory flag
        (rowMu q.memory n) (rowC0 q.memory n) n 0 pbi hd pb ent (tn+q.carry)
        (UInt256.ofNat (l2PC n)) inv tail)
      (TnCacheLastTrace.lastState st (UInt256.ofNat (l2PC n+TnCacheL2Chain.fullSize n))
        q.memory flag (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
        pbi hd pb ent (tn+q.carry) (UInt256.ofNat (l2PC n)) inv tail) := by
    by_cases h4 : n = 4
    · subst n
      exact TnCandidateBlocks.l2Four.steps (env.transfer rfl rfl) rfl hreduce
    · have h8 : n = 8 := hn.resolve_left h4
      subst n
      exact TnCandidateBlocks.l2Eight.steps (env.transfer rfl rfl) rfl hreduce
  have hpc : (TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC n+TnCacheL2Chain.fullSize n)) q.memory flag
      (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
      pbi hd pb ent (tn+q.carry) (UInt256.ofNat (l2PC n)) inv tail).pc =
      UInt256.ofNat 4271 := by
    change UInt256.ofNat (l2PC n+TnCacheL2Chain.fullSize n) = UInt256.ofNat 4271
    rw [l2_end n hn]
  have g2 := TnCandidateBlocks.tailShort.steps
    (s := TnCacheLastTrace.lastState st
      (UInt256.ofNat (l2PC n+TnCacheL2Chain.fullSize n)) q.memory flag
      (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
      pbi hd pb ent (tn+q.carry) (UInt256.ofNat (l2PC n)) inv tail)
    (env.transfer rfl rfl) hpc hlast
  simpa only [st, tail] using (g0.trans g1).trans g2

#print axioms reduction_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateReductionSteps
