import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUnsignedRun
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- Only the exact artifact/location binding remains an integration parameter. -/
structure Blocks (artifact : ProgramArtifact) where
  entry : Block artifact .Osaka 482 entryProgram
  init : Block artifact .Osaka 486 initProgram
  cell : Block artifact .Osaka 492 cellProgram
  guard : Block artifact .Osaka 527 guardProgram
  decide : Block artifact .Osaka 532 decideProgram
  retry : Block artifact .Osaka 537 retryProgram
  finish : Block artifact .Osaka 546 finishProgram
  jumpInit : Decode.isValidJumpDest artifact.code 486 = true
  jumpLoop : Decode.isValidJumpDest artifact.code 492 = true
  jumpDone : Decode.isValidJumpDest artifact.code 546 = true

theorem lift_run {artifact : ProgramArtifact} {s : State}
    (env : Environment artifact .Osaka s) {pc : Nat} {instructions : List Instr}
    (block : Block artifact .Osaka pc instructions) {stk : List UInt256}
    {mem : ByteArray} {t : State}
    (h : runInstructions instructions (st s pc stk mem AW) = some t) :
    Reach (st s pc stk mem AW) t :=
  ⟨block.steps (env.transfer rfl rfl) rfl h⟩

theorem loop_reach {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (env : Environment artifact .Osaka s)
    (src z : Nat) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hsrc : src ≤ 8192) (hz : z ≤ 8192) :
    ∀ n, 1 ≤ n → n ≤ 1024 → ∀ mem c,
      let result := pass src z n mem c
      Reach (st s 492 (UInt256.ofNat n :: c :: UInt256.ofNat z :: ret :: UInt256.ofNat src :: rest) mem AW)
        (st s 532 (UInt256.ofNat 0 :: result.2 :: UInt256.ofNat z :: ret :: UInt256.ofNat src :: rest) result.1 AW) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _ mem c
    have g1 := lift_run env blocks.cell (run_cell s 1 src z c ret rest mem hcap (by omega) (by omega) hsrc hz)
    have g2 := lift_run env blocks.guard (run_guard_exit s
      (nextCarry (sumWord mem src z 0 c)) (UInt256.ofNat z) ret (UInt256.ofNat src) rest
      (writeByte mem 0 (sumWord mem src z 0 c)) hcap)
    simpa only [pass, Nat.sub_self] using g1.tr g2
  | succ n hn ih =>
    intro hn' mem c
    let w := sumWord mem src z n c
    let m1 := writeByte mem n w
    have hj : Decode.isValidJumpDest s.executionEnv.code 492 = true := by
      rw [env.code]
      exact blocks.jumpLoop
    have g1 := lift_run env blocks.cell
      (run_cell s (n + 1) src z c ret rest mem hcap (by omega) hn' hsrc hz)
    simp only [Nat.add_sub_cancel] at g1
    have g2 := lift_run env blocks.guard
      (run_guard_back s n (nextCarry w) (UInt256.ofNat z) ret (UInt256.ofNat src) rest m1
        hcap hn (by omega) hj)
    have g3 := ih (by omega) m1 (nextCarry w)
    simpa only [pass] using g1.tr (g2.tr g3)

theorem retry_carry (ml src : Nat) (mem : ByteArray)
    (hml : ml ≤ 1024) (hs : src = 0 ∨ ml ≤ src)
    (hzero : num mem 8192 ml = 0)
    (_hlt : num mem 0 ml + num mem src ml < 2 * num mem 1024 ml)
    (hc0 : (pass src 1024 ml mem (UInt256.ofNat 1)).2.toNat = 0) :
    (pass 1024 8192 ml (pass src 1024 ml mem (UInt256.ofNat 1)).1
      (UInt256.ofNat 1)).2.toNat = 2 := by
  let first := pass src 1024 ml mem (UInt256.ofNat 1)
  let second := pass 1024 8192 ml first.1 (UInt256.ofNat 1)
  have h1 := pass_one src 1024 ml mem hs hml
  have h2 := pass_one 1024 8192 ml first.1 (Or.inr hml) (by omega)
  have hM1 : num first.1 1024 ml = num mem 1024 ml :=
    num_congr ml (fun i _ => h1.2.2 _ (by omega))
  have hZ1 : num first.1 8192 ml = 0 := by
    rw [← hzero]
    exact num_congr ml (fun i _ => h1.2.2 _ (by omega))
  have he1 := h1.2.1
  rw [hc0, Nat.zero_mul, Nat.add_zero] at he1
  have he2 := h2.2.1
  rw [hZ1, Nat.add_zero, hM1] at he2
  change num second.1 0 ml + second.2.toNat * 256 ^ ml =
    num first.1 0 ml + num mem 1024 ml + 256 ^ ml at he2
  change num first.1 0 ml + num mem 1024 ml = _ at he1
  rw [he1] at he2
  have hR : 0 < (256 : Nat) ^ ml := pow_pos (by decide) ml
  have hS := num_lt second.1 0 ml
  have hc2 : second.2.toNat = 0 ∨ second.2.toNat = 1 ∨ second.2.toNat = 2 := by
    have := h2.1
    change second.2.toNat ≤ 2 at this
    omega
  rcases hc2 with hc | hc | hc
  · rw [hc, Nat.zero_mul, Nat.add_zero] at he2
    omega
  · rw [hc, Nat.one_mul] at he2
    omega
  · exact hc

/-- Metered execution of the exact69-byte ADDM once the seven blocks are bound. -/
theorem addm_reach {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (env : Environment artifact .Osaka s)
    (ml src retPc : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024)
    (hs : src = 0 ∨ ml ≤ src) (hsrc : src ≤ 8192) (hret : retPc < 2 ^ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code retPc = true)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hzero : num mem 8192 ml = 0)
    (hlt : num mem 0 ml + num mem src ml < 2 * num mem 1024 ml) :
    Reach (st s 482 (UInt256.ofNat retPc :: UInt256.ofNat src :: rest) mem AW)
      (st s retPc rest (addResult ml src mem) AW) := by
  let first := pass src 1024 ml mem (UInt256.ofNat 1)
  let second := pass 1024 8192 ml first.1 (UInt256.ofNat 1)
  have hji : Decode.isValidJumpDest s.executionEnv.code 486 = true := by rw [env.code]; exact blocks.jumpInit
  have hjd : Decode.isValidJumpDest s.executionEnv.code 546 = true := by rw [env.code]; exact blocks.jumpDone
  have hjr : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat retPc).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hjump
  have g0 := lift_run env blocks.entry (run_entry s (UInt256.ofNat retPc) (UInt256.ofNat src) rest mem hcap)
  have g1 := lift_run env blocks.init (run_init s ml (UInt256.ofNat 1024) (UInt256.ofNat retPc)
    (UInt256.ofNat src) rest mem hcap hm)
  have g2 := loop_reach blocks s env src 1024 (UInt256.ofNat retPc) rest hcap hsrc (by decide) ml hml1 hml mem (UInt256.ofNat 1)
  by_cases hc0 : first.2.toNat = 0
  · have g3 := lift_run env blocks.decide (run_decide_no s first.2 (UInt256.ofNat 1024)
      (UInt256.ofNat retPc) (UInt256.ofNat src) rest first.1 hcap hc0)
    have g4 := lift_run env blocks.retry (run_retry s (UInt256.ofNat retPc) (UInt256.ofNat src) rest first.1 hcap hji)
    have g5 := lift_run env blocks.init (run_init s ml (UInt256.ofNat 8192) (UInt256.ofNat retPc)
      (UInt256.ofNat 1024) rest first.1 hcap hm)
    have g6 := loop_reach blocks s env 1024 8192 (UInt256.ofNat retPc) rest hcap (by decide) (by decide)
      ml hml1 hml first.1 (UInt256.ofNat 1)
    have hc2 : second.2.toNat ≠ 0 := by
      have h := retry_carry ml src mem hml hs hzero hlt hc0
      change second.2.toNat = 2 at h
      omega
    have g7 := lift_run env blocks.decide (run_decide_yes s second.2 (UInt256.ofNat 8192)
      (UInt256.ofNat retPc) (UInt256.ofNat 1024) rest second.1 hcap hc2 hjd)
    have g8 := lift_run env blocks.finish (run_finish s (UInt256.ofNat 8192)
      (UInt256.ofNat retPc) (UInt256.ofNat 1024) rest second.1 hcap hjr)
    have hout : addResult ml src mem = second.1 := by
      unfold addResult
      exact if_pos hc0
    rw [hout]
    simpa only [st] using
      g0.tr (g1.tr (g2.tr (g3.tr (g4.tr (g5.tr (g6.tr (g7.tr g8)))))))
  · have g3 := lift_run env blocks.decide (run_decide_yes s first.2 (UInt256.ofNat 1024)
      (UInt256.ofNat retPc) (UInt256.ofNat src) rest first.1 hcap hc0 hjd)
    have g4 := lift_run env blocks.finish (run_finish s (UInt256.ofNat 1024)
      (UInt256.ofNat retPc) (UInt256.ofNat src) rest first.1 hcap hjr)
    have hout : addResult ml src mem = first.1 := by
      unfold addResult
      exact if_neg hc0
    rw [hout]
    simpa only [st] using g0.tr (g1.tr (g2.tr (g3.tr g4)))

theorem addm {artifact : ProgramArtifact} (blocks : Blocks artifact)
    (s : State) (env : Environment artifact .Osaka s)
    (ml src retPc : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024)
    (hs : src = 0 ∨ ml ≤ src) (hsrc : src ≤ 8192) (hret : retPc < 2 ^ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code retPc = true)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hzero : num mem 8192 ml = 0)
    (hlt : num mem 0 ml + num mem src ml < 2 * num mem 1024 ml) :
    ∃ mem', Reach (st s 482 (UInt256.ofNat retPc :: UInt256.ofNat src :: rest) mem AW)
        (st s retPc rest mem' AW) ∧
      num mem' 0 ml = (num mem 0 ml + num mem src ml) % num mem 1024 ml ∧
      (∀ k, ml ≤ k → bget mem' k = bget mem k) := by
  exact ⟨addResult ml src mem,
    addm_reach blocks s env ml src retPc rest mem hcap hml1 hml hs hsrc hret hjump hm hzero hlt,
    addResult_correct ml src mem hml hs hzero hlt⟩

#print axioms loop_reach
#print axioms addm

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned
