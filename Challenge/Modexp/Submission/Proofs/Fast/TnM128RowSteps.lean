import Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Steps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128ReductionSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128RowSteps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open CiosCached CiosCachedMacCore CiosReadonly CiosCachedMidMemory TnM128ReductionSteps

def l1PC (n : Nat) : Nat := if n = 4 then 5179 else 3387

theorem l1_jump (n : Nat) (hn : n = 4 ∨ n = 8) :
    Decode.isValidJumpDest TnM128Candidate.bytecode (UInt256.ofNat (l1PC n)).toNat = true := by
  rcases hn with rfl | rfl
  · exact TnM128CandidateArtifact.isValidJumpDest_index 3959 (by rfl)
  · exact TnM128CandidateArtifact.isValidJumpDest_index 2516 (by rfl)

theorem row_jump :
    Decode.isValidJumpDest TnM128Candidate.bytecode (UInt256.ofNat 3358).toNat = true :=
  TnM128CandidateArtifact.isValidJumpDest_index 2487 (by rfl)

def result (mem : ByteArray) (tn : UInt256) (pa n : Nat) (pbi : UInt256) :
    TnCacheRowModel.CacheState :=
  TnCacheSquareModel.fromL1
    (l1Step mem (MachineState.readWord mem pbi.toNat) pa n n) tn n

/-- A complete ordinary multiply row of the selected candidate, from the row
head through both limb loops and the actual next-row branch. -/
noncomputable def row_steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (pa n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi pb tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hpbi : pbi.toNat ≤ 2784)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : ReadonlyCache s.memory n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache s.memory m96 m64 m32)
    (hi : inverseInvariant s.memory n) (hs : Snapshot s.memory pa n)
    (hcache : m128 = MachineState.readWord s.memory 128) :
    GasSteps
      (framed s (UInt256.ofNat 3358)
        (TnCacheFrameOps.frame pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC n))
          tn m128 inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)))
      (framed {s with memory := (result s.memory tn pa n pbi).memory}
        (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb)
         then UInt256.ofNat 3358 else UInt256.ofNat 3963)
        (TnCacheFrameOps.frame (negative32+pbi) (UInt256.ofNat 3358) pb
          (UInt256.ofNat (l1PC n)) (result s.memory tn pa n pbi).tn
          m128 inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  let bi := MachineState.readWord s.memory pbi.toNat
  let q1 := l1Step s.memory bi pa n 1
  let qn := l1Step s.memory bi pa n n
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  have hn' : 1 ≤ n ∧ n ≤ 8 := by omega
  have ht : tl.toNat = 2112+32*(n-1) := by
    rw [hc.lowAddress, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hj : Decode.isValidJumpDest s.executionEnv.code
      (UInt256.ofNat (l1PC n)).toNat = true := by rw [env.code]; exact l1_jump n hn
  have hhd : Decode.isValidJumpDest s.executionEnv.code
      (UInt256.ofNat 3358).toNat = true := by rw [env.code]; exact row_jump
  have hhead := TnCacheHeadTrace.run_head s 3358 pa n pbi (UInt256.ofNat 3358) pb
    (UInt256.ofNat (l1PC n)) tn m128 tl inv m0 aEnd m96 m64 m32
    dst ret rest hcap hn' hact hpbi hpa ha ht hj
  have g0 := TnM128L1Blocks.head.steps
    (s := framed s (UInt256.ofNat 3358)
      (TnCacheFrameOps.frame pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC n))
        tn m128 inv tail)) (env.transfer rfl rfl) rfl hhead
  have hs1 : Snapshot q1.memory pa n := by
    exact Snapshot.l1StepOn_pres_stage
      (q := l1Step s.memory bi pa n 0) hs bi 0 hn'.2 hpa (by omega)
  have g1 : GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat (l1PC n)) q1 bi
        pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC n)) tn m128 inv tail)
      (TnCacheL1Trace.qState s (UInt256.ofNat (middlePC n)) (l1Run q1 bi pa n 1 (n-1)) bi
        pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC n)) tn m128 inv tail) := by
    by_cases h4 : n = 4
    · subst n
      exact TnM128L1Steps.private_steps s env q1 bi pa 4 1 3 (by decide)
        pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC 4)) tn m128 inv tail
        (by simp only [tail, List.length_cons]; omega) hact (by decide) (by decide) hpa hs1
    · have h8 : n = 8 := hn.resolve_left h4
      subst n
      exact TnM128L1Steps.suffix_steps s env q1 bi pa 8 1 7 (by decide)
        pbi (UInt256.ofNat 3358) pb (UInt256.ofNat (l1PC 8)) tn m128 inv tail
        (by simp only [tail, List.length_cons]; omega) hact (by decide) (by decide) hpa hs1
  have hqn : l1Run q1 bi pa n 1 (n-1) = qn := by
    simp only [q1, qn, StagedOperand.l1Run_l1Step, show 1+(n-1) = n from by omega]
  rw [hqn] at g1
  have hm128 : m128 = MachineState.readWord qn.memory 128 := by
    rw [show MachineState.readWord qn.memory 128 = MachineState.readWord s.memory 128 from
      Monpro.readWord_l1Step_low _ _ pa n 128 n (by decide)]
    exact hcache
  have g2 := reduction_steps s env qn bi tn n hn pbi (UInt256.ofNat 3358) pb
    (UInt256.ofNat (l1PC n)) m128 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact
    (hc.l1 hn'.2 bi pa n) (he.l1 bi pa n n hn'.2)
    (inverse_l1Step s.memory bi pa n n hn'.2 hi) hm128 hhd
  have both := (g0.trans g1).trans g2
  simpa only [qn, q1, bi, tail, result] using both

#print axioms row_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128RowSteps
