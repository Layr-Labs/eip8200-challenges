import Challenge.Modexp.Submission.Proofs.Fast.R4Runs
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.R4Bridge

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：片段合成为 `GasSteps`

* `gasSteps_red`：共享约化子程序（入口 5162，返回到栈上的 `ret`），对任意窗口 `P`、
  溢出位 `v` 成立。
* `gasSteps_row0..row3`：各积行从行头到约化入口。
* `gasSteps_r4`：整个例程，从入口到 `sq_exit`，栈不变，内存只写 `t` 窗口的五个字。

栈上的窗口排列是 `t3 t2 t1 t0 t4`（`win`）。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Trace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open R4Math R4Blocks R4Runs R4Bridge
open Challenge.EvmProof (GasSteps)

/-- 栈上的五字窗口。 -/
def win (W : W5) (tail : List UInt256) : List UInt256 :=
  W.t3 :: W.t2 :: W.t1 :: W.t0 :: W.t4 :: tail

/-! ## `SGT` 单步（任意位置） -/

def gasSteps_sgtAt (idx pcN : Nat)
    (hidx : Artifact.submissionInstructions[idx]? = some (.op .SGT))
    (hpcI : Artifact.submissionArtifact.instructionPC idx = pcN) (hlt : pcN + 1 < 2 ^ 256)
    (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hcap : rest.length ≤ 1021) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps { s with pc := UInt256.ofNat pcN, stack := a :: b :: rest }
      { s with pc := UInt256.ofNat (pcN + 1), stack := UInt256.sgt a b :: rest } := by
  have hpcNat : ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).pc.toNat =
      Artifact.submissionArtifact.instructionPC idx := by
    rw [hpcI]
    show (UInt256.ofNat pcN).toNat = pcN
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hwf : Challenge.EvmProof.Stepper.WellFormed
      ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).fork (.op .SGT) := by
    show Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT)
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  have hop := Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact
    { s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } idx (.op .SGT) hcode hpcNat hidx hwf
  have hcap' : ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).stack.length +
      Operation.pushArity .SGT ≤ 1024 + Operation.popArity .SGT := by
    show (a :: b :: rest).length + Operation.pushArity .SGT ≤ 1024 + Operation.popArity .SGT
    simp only [List.length_cons, Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt hop rfl hcap' hrun hnp
  exact h.cast rfl (by rw [Challenge.EvmProof.Word.succ_ofNat_mod])

/-! ## 合成辅助 -/

set_option hygiene false in
/-- 一个片段：由符号执行引理得到一步 `GasSteps` 并接到剩余目标前。 -/
local macro "seg " blk:term:max run:term : tactic =>
  `(tactic| refine GasSteps.trans
      (SquareRow.stepsOf $blk $run rfl hcode hfork hrun hnp) ?_)

local macro "lenOK" : tactic =>
  `(tactic| ((try simp only [List.length_cons, List.length_append, win] at *) <;> omega))

theorem jd5158 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4928 = true :=
  Artifact.isValidJumpDest_index 3871 (by rfl)

theorem jd4903 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4688 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3659 (by rfl)

theorem jd5020 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4800 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3759 (by rfl)

theorem jd5108 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4883 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3832 (by rfl)

theorem jd5274 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (5032 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3975 (by rfl)

theorem jd5038 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5038 = true :=
  Artifact.isValidJumpDest_index 3979 (by rfl)

theorem jd5077 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5077 = true :=
  Artifact.isValidJumpDest_index 4004 (by rfl)

theorem jd4580 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4580 = true :=
  Artifact.isValidJumpDest_index 3563 (by rfl)

theorem jd4248 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4248 = true :=
  Artifact.isValidJumpDest_index 3320 (by rfl)

section
variable (s : State)
  (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
  (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

include hcode hfork hrun hnp

/-! ## 约化子程序 -/

/-- **RED**：`[ret, v] ++ win P ++ K` 在 5162 → `win (red P v) ++ K` 在 `ret`。 -/
def gasSteps_red (ret v : UInt256) (P : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    GasSteps { s with pc := UInt256.ofNat 4928,
                      stack := ret :: v :: win P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := ret,
               stack := win (red n0 n1 n2 n3 np k P v) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win]
  seg block_redm (run_redm s ret v P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np rest (by omega) hk hminv hguard)
  seg block_reds1 (run_reds1 s (hcap := by lenOK) ..)
  seg block_reds2 (run_reds2 s (hcap := by lenOK) ..)
  seg block_reds3 (run_reds3 s (hcap := by lenOK) ..)
  exact SquareRow.stepsOf block_redt (run_redt s (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

/-! ## 积行 -/

/-- 行 0：`K` 在 4832（序言之后）→ `[4935, 0] ++ win (row0 …) ++ K` 在 5162。 -/
def gasSteps_row0 (k n0 n1 n2 n3 np a0 a1 a2 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (_ha0 : MachineState.readWord s.memory 2208 = a0)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 4609, stack := dHi a0 k :: (a0 * a0) :: (a0 + a0) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }
      { s with pc := UInt256.ofNat 4928,
               stack := (4688 : UInt256) :: (⟨0⟩ : UInt256) ::
                 win (row0 a0 a1 a2 a3 k) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4928 = true := by rw [hcode]; exact jd5158
  simp only [win]
  seg block_r0z1 (run_r0z1 s (hcap := by lenOK) (ha1 := ha1) (hact := hact) ..)
  seg block_r0z2 (run_r0z2 s (hcap := by lenOK) (ha2 := ha2) (hact := hact) ..)
  seg block_r0z3 (run_r0z3 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r0e (run_r0e s (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

/-- 行 1：`win P ++ K` 在 4935 → `[5052, v] ++ win (row1 …).1 ++ K` 在 5162。 -/
def gasSteps_row1 (P : W5) (k n0 n1 n2 n3 np a0 a1 a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 4688, stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 4928,
               stack := (4800 : UInt256) :: (row1 a0 a1 a2 a3 k P).2 ::
                 win (row1 a0 a1 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4928 = true := by rw [hcode]; exact jd5158
  simp only [win]
  seg block_r1h (run_r1h s (hcap := by lenOK) (ha1 := ha1) (ha0 := ha0) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 3665 4698 (by rfl) (by rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r1d (run_r1d s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  seg block_r1c2 (run_r1c2 s (hcap := by lenOK) (ha2 := ha2) (hact := hact) ..)
  seg block_r1c3 (run_r1c3 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r1e (run_r1e s (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

/-- 行 2：`win P ++ K` 在 5052 → `[5112, v] ++ win (row2 …).1 ++ K` 在 5162。 -/
def gasSteps_row2 (P : W5) (k n0 n1 n2 n3 np a1 a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 4800, stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 4928,
               stack := (4883 : UInt256) :: (row2 a1 a2 a3 k P).2 ::
                 win (row2 a1 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4928 = true := by rw [hcode]; exact jd5158
  simp only [win]
  seg block_r2h (run_r2h s (hcap := by lenOK) (ha2 := ha2) (ha1 := ha1) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 3765 4810 (by rfl) (by rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r2d (run_r2d s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  seg block_r2c3 (run_r2c3 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r2e (run_r2e s (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

/-- 行 3：`win P ++ K` 在 5112 → `[5285, v] ++ win (row3 …).1 ++ K` 落入 5162。 -/
def gasSteps_row3 (P : W5) (k n0 n1 n2 n3 np a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 4883, stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 4928,
               stack := (5032 : UInt256) :: (row3 a2 a3 k P).2 ::
                 win (row3 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win]
  seg block_r3h (run_r3h s (hcap := by lenOK) (ha3 := ha3) (ha2 := ha2) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 3838 4893 (by rfl) (by rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r3d (run_r3d s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  exact SquareRow.stepsOf block_r3e (run_r3e s (hcap := by lenOK) ..) rfl hcode hfork hrun hnp

/-! ## The n=4 tail -/

/-- Tail head and, for a nonzero overflow word, `rare4`: `win W ++ K` at 5032 →
`win (red4 W) ++ K` at `st4` (5038). -/
def gasSteps_tail (W : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    GasSteps { s with pc := UInt256.ofNat 5032,
                      stack := win W (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 5038,
               stack := win (red4 n0 n1 n2 n3 W) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := W
  if h0 : t4.toNat = 0 then
    have ht : t4 = ⟨0⟩ := Challenge.EvmProof.Word.word_ext (by rw [h0]; rfl)
    subst ht
    have hr : red4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, ⟨0⟩⟩ = ⟨t0, t1, t2, t3, ⟨0⟩⟩ := if_pos rfl
    rw [hr]
    simp only [win]
    exact SquareRow.stepsOf block_tail (run_tail_zero s t3 t2 t1 t0 _ (by lenOK)) rfl
      hcode hfork hrun hnp
  else
    have hne : t4 ≠ ⟨0⟩ := fun h => h0 (by rw [h]; rfl)
    have hr : red4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, t4⟩ = sub4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, t4⟩ :=
      if_neg hne
    rw [hr]
    simp only [win]
    have hj77 : Decode.isValidJumpDest s.executionEnv.code 5077 = true := by
      rw [hcode]; exact jd5077
    have hj38 : Decode.isValidJumpDest s.executionEnv.code 5038 = true := by
      rw [hcode]; exact jd5038
    refine GasSteps.trans (SquareRow.stepsOf block_tail
      (run_tail_rare s t3 t2 t1 t0 t4 _ (by lenOK) hne hj77) rfl hcode hfork hrun hnp) ?_
    exact SquareRow.stepsOf block_rare4
      (run_rare4 s t3 t2 t1 t0 t4 k n0 n1 n2 n3 np rest (by lenOK) hj38) rfl hcode hfork hrun hnp

/-- `st4` with rounds left: store the window (`r4Mem`), drop the constants, decrement the
counter `c` (the frame's `pdst`, under `e0..e12, aprev`) and jump back into R4. -/
def gasSteps_st4More (P : W5) (k n0 n1 n2 n3 np e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    aprev c : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hact : 88 ≤ s.activeWords.toNat) (hc : UInt256.isTrue c) :
    GasSteps { s with pc := UInt256.ofNat 5038,
                      stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
                        e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest) }
      { s with pc := UInt256.ofNat 4580,
               stack := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 ::
                 e12 :: aprev :: (e5 + c) :: rest,
               memory := r4Mem s.memory P } := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 4580 = true := by rw [hcode]; exact jd4580
  have h1 := run_st4_stores s P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np
    (e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest)
    (by lenOK) hact
  have h2 := run_st4_4_more { s with memory := r4Mem s.memory P } e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    e10 e11 e12 aprev c rest (by lenOK) hc hj
  have h := WindowNibbleKernel.runInstructions_append_some _ _ _ _ _ h1 h2
  rw [← prog_st4_split] at h
  exact SquareRow.stepsOf block_st4 h rfl hcode hfork hrun hnp

/-- `st4` on the last round: the same stores, a zero counter falls through to `m4`, which jumps
to `m4j` (4248). -/
def gasSteps_st4Last (P : W5) (k n0 n1 n2 n3 np e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    aprev c : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hact : 88 ≤ s.activeWords.toNat) (hc : ¬ UInt256.isTrue c) :
    GasSteps { s with pc := UInt256.ofNat 5038,
                      stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
                        e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest) }
      { s with pc := (4248 : UInt256),
               stack := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 ::
                 e12 :: aprev :: (e5 + c) :: rest,
               memory := r4Mem s.memory P } := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 4248 = true := by rw [hcode]; exact jd4248
  have h1 := run_st4_stores s P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np
    (e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest)
    (by lenOK) hact
  have h2 := run_st4_4_last { s with memory := r4Mem s.memory P } e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    e10 e11 e12 aprev c rest (by lenOK) hc
  have h := WindowNibbleKernel.runInstructions_append_some _ _ _ _ _ h1 h2
  rw [← prog_st4_split] at h
  have g1 := SquareRow.stepsOf block_st4 h rfl hcode hfork hrun hnp
  have g2 := SquareRow.stepsOf block_m4
    (run_m4 { s with memory := r4Mem s.memory P }
      (e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev ::
        (e5 + c) :: rest) (by lenOK) hj)
    rfl hcode hfork hrun hnp
  exact g1.trans g2

end

/-! ## 整个例程 -/

/-- **R4**：帧 `e0..e12 ++ rest` 在 4580 → `st4`（5038），栈顶为约化后的窗口 `red4 W`，内存不变。
帧槽（P1）：`e4 = n2`，`e5 = k`，`e7 = n1`，`e8 = n0`，`e11 = np`，`e12` 为进位缓存。 -/
def gasSteps_r4 (s : State) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hk : e5 = Monpro.maxWord)
    (hminv : (e8.toNat * e11.toNat + 1) % 2^256 = 0)
    (hguard : e11 ≠ UInt256.ofNat 1) :
    GasSteps
      { s with pc := UInt256.ofNat 4580,
               stack := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest }
      { s with pc := UInt256.ofNat 5038,
               stack := win (red4 e8 e7 e4 (MachineState.readWord s.memory 0)
                   (r4Final s.memory e5 e8 e7 e4 e11))
                 (e5 :: e8 :: e7 :: e4 :: MachineState.readWord s.memory 0 :: e11 ::
                   e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest) } := by
  have hj (r : UInt256) (h : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode r.toNat = true) :
      Decode.isValidJumpDest s.executionEnv.code r.toNat = true := by rw [hcode]; exact h
  -- 名字
  generalize ha0 : MachineState.readWord s.memory 2208 = a0
  generalize ha1 : MachineState.readWord s.memory 2176 = a1
  generalize ha2 : MachineState.readWord s.memory 2144 = a2
  generalize ha3 : MachineState.readWord s.memory 2112 = a3
  generalize hn3 : MachineState.readWord s.memory 0 = n3
  let E := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest
  have hE : E.length ≤ 1003 := by simp only [E, List.length_cons]; omega
  let K := fun (tail : List UInt256) => e5 :: e8 :: e7 :: e4 :: n3 :: e11 :: tail
  let W1 := red e8 e7 e4 n3 e11 e5 (row0 a0 a1 a2 a3 e5) ⟨0⟩
  let R1 := row1 a0 a1 a2 a3 e5 W1
  let W2 := red e8 e7 e4 n3 e11 e5 R1.1 R1.2
  let R2 := row2 a1 a2 a3 e5 W2
  let W3 := red e8 e7 e4 n3 e11 e5 R2.1 R2.2
  let R3 := row3 a2 a3 e5 W3
  let W4 := red e8 e7 e4 n3 e11 e5 R3.1 R3.2
  have g0 := SquareRow.stepsOf block_prodiag
    (run_prodiag s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 n3 a0 rest (by omega) hn3 ha0 hact) rfl
    hcode hfork hrun hnp
  have g1 := gasSteps_row0 s hcode hfork hrun hnp e5 e8 e7 e4 n3 e11 a0 a1 a2 a3 E hE hact ha0 ha1 ha2 ha3
  have g2 := gasSteps_red s hcode hfork hrun hnp 4688 ⟨0⟩ (row0 a0 a1 a2 a3 e5) e5 e8 e7 e4 n3 e11 E hE
    (hj _ jd4903) hk hminv hguard
  have g3 := gasSteps_row1 (hk := hk) s hcode hfork hrun hnp W1 e5 e8 e7 e4 n3 e11 a0 a1 a2 a3 E hE hact ha0 ha1 ha2 ha3
  have g4 := gasSteps_red s hcode hfork hrun hnp 4800 R1.2 R1.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5020) hk hminv hguard
  have g5 := gasSteps_row2 (hk := hk) s hcode hfork hrun hnp W2 e5 e8 e7 e4 n3 e11 a1 a2 a3 E hE hact ha1 ha2 ha3
  have g6 := gasSteps_red s hcode hfork hrun hnp 4883 R2.2 R2.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5108) hk hminv hguard
  have g7 := gasSteps_row3 (hk := hk) s hcode hfork hrun hnp W3 e5 e8 e7 e4 n3 e11 a2 a3 E hE hact ha2 ha3
  have g8 := gasSteps_red s hcode hfork hrun hnp 5032 R3.2 R3.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5274) hk hminv hguard
  have g9 := gasSteps_tail s hcode hfork hrun hnp W4 e5 e8 e7 e4 n3 e11 E (le_trans hE (by norm_num))
  refine ((((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans
    g8).trans g9).cast rfl ?_)
  have hW : r4Final s.memory e5 e8 e7 e4 e11 = W4 := by
    simp only [r4Final, final, ha0, ha1, ha2, ha3, hn3, W4, R3, W3, R2, W2, R1, W1]
  rw [hW]

end Challenge.Modexp.Submission.Proofs.Fast.R4Trace
