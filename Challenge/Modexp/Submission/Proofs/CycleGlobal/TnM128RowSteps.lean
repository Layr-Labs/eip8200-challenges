import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128L1Steps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128ReductionSteps
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128R4Reduction

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.Global.Fast.TnM128RowSteps
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand
open CiosCached CiosCachedMacCore CiosReadonly CiosCachedMidMemory TnM128ReductionSteps

def l1PC (n : Nat) : Nat := if n = 4 then 3809 else 3347

/-- The multiply row head of each width (msplit: one loop per width). -/
def headPC (n : Nat) : Nat := if n = 4 then 3775 else 3313

theorem head_jump (n : Nat) (hn : n = 4) :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode (UInt256.ofNat (headPC n)).toNat = true := by
  subst n
  exact CycleSubmission.Global.Binding.jumpDest 2903 (by rfl)

def result (mem : ByteArray) (tn : UInt256) (pa n : Nat) (q : UInt256) :
    TnCacheRowModel.CacheState :=
  TnCacheSquareModel.fromL1
    (l1Step mem (MachineState.readWord mem (TnCacheHeadTrace.bAddr q)) pa n n) tn n

/-- A complete ordinary multiply row of the selected candidate, from the width's row head
(`b_i = mem[0xe0 - q]`) through both limb loops and the actual next-row branch. -/
noncomputable def row_steps (s : State)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (pa n : Nat) (hn : n = 4)
    (q pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hq : TnCacheHeadTrace.bAddr q ≤ 2784)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1))
    (hc : ReadonlyCache s.memory n tl inv m0)
    (he : TnCacheExtraTrace.ExtraCache s.memory m96 m64 m32)
    (hi : inverseInvariant s.memory n) (hs : Snapshot s.memory pa n)
    (hcache : m128 = MachineState.readWord s.memory 128)
    (hpb : n = 8 → pb = MachineState.readWord s.memory 192) :
    GasSteps
      (framed s (UInt256.ofNat (headPC n))
        (TnCacheFrameOps.frame q (UInt256.ofNat (headPC n)) pb ent
          m32 m128 m64
          (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)))
      (framed {s with memory := (result s.memory tn pa n q).memory}
        (if UInt256.isTrue (UInt256.ofNat 32+q)
         then UInt256.ofNat (headPC n) else UInt256.ofNat 3414)
        (TnCacheFrameOps.frame (UInt256.ofNat 32+q) (UInt256.ofNat (headPC n)) pb
          ent m32
          m128 m64
          (m0 :: tl :: m96 :: inv :: (result s.memory tn pa n q).tn :: aEnd :: dst :: ret :: rest))) := by
  let bi := MachineState.readWord s.memory (TnCacheHeadTrace.bAddr q)
  let q1 := l1Step s.memory bi pa n 1
  let qn := l1Step s.memory bi pa n n
  let tail := m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest
  have hn' : 1 ≤ n ∧ n ≤ 8 := by omega
  have hhd : Decode.isValidJumpDest s.executionEnv.code
      (UInt256.ofNat (headPC n)).toNat = true := by rw [env.code]; exact head_jump n hn
  have hhead := TnCacheHeadTrace.run_headC s (headPC n) pa n q (UInt256.ofNat (headPC n)) pb
    ent m32 m128 tl m64 m0 aEnd m96 inv tn
    dst ret rest hcap hn' hact hq hpa ha
  have hpc : headPC n + 34 = l1PC n := by
    subst n; rfl
  rw [hpc] at hhead
  have g0 : GasSteps
      (framed s (UInt256.ofNat (headPC n))
        (TnCacheFrameOps.frame q (UInt256.ofNat (headPC n)) pb ent m32 m128 m64 tail))
      (TnCacheL1Trace.qState s (UInt256.ofNat (l1PC n)) q1 bi
        q (UInt256.ofNat (headPC n)) pb ent m32 m128 m64 tail) := by
    subst n
    exact TnM128L1Blocks.head4.steps (env.transfer rfl rfl) rfl hhead
  have hs1 : Snapshot q1.memory pa n := by
    exact Snapshot.l1StepOn_pres_stage
      (q := l1Step s.memory bi pa n 0) hs bi 0 hn'.2 hpa (by omega)
  have hqn : l1Run q1 bi pa n 1 (n-1) = qn := by
    simp only [q1, qn, StagedOperand.l1Run_l1Step, show 1+(n-1) = n from by omega]
  have hm128 : m128 = MachineState.readWord qn.memory 128 := by
    rw [show MachineState.readWord qn.memory 128 = MachineState.readWord s.memory 128 from
      Monpro.readWord_l1Step_low _ _ pa n 128 n (by decide)]
    exact hcache
  have g12 : GasSteps
      (TnCacheL1Trace.qState s (UInt256.ofNat (l1PC n)) q1 bi
        q (UInt256.ofNat (headPC n)) pb ent m32 m128 m64 tail)
      (framed {s with memory := (TnCacheSquareModel.fromL1 qn tn n).memory}
        (if UInt256.isTrue (UInt256.ofNat 32+q) then UInt256.ofNat (headPC n) else UInt256.ofNat 3414)
        (TnCacheFrameOps.frame (UInt256.ofNat 32+q) (UInt256.ofNat (headPC n)) pb ent
          m32 m128 m64
          (m0 :: tl :: m96 :: inv :: (TnCacheSquareModel.fromL1 qn tn n).tn :: aEnd :: dst :: ret :: rest))) := by
    subst n
    have g1 := TnM128L1Steps.private_steps s env q1 bi pa
      q (UInt256.ofNat (headPC 4)) pb ent m32 m128 m64 tail
      (by simp only [tail, List.length_cons]; omega) hact hpa hs1
    rw [hqn] at g1
    have g2 := TnM128R4Reduction.reduction_steps s env qn tn q (UInt256.ofNat (headPC 4)) pb
      ent m128 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact
      (hc.l1 hn'.2 bi pa 4) (he.l1 bi pa 4 4 hn'.2)
      (inverse_l1Step s.memory bi pa 4 4 hn'.2 hi) hm128 hhd
    exact g1.trans g2
  have both := g0.trans g12
  simpa only [qn, q1, bi, tail, result] using both

end CycleSubmission.Global.Fast.TnM128RowSteps
