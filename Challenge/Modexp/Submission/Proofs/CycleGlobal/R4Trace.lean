import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTailRuns
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTailBlocks
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTrace
import Challenge.Modexp.Submission.Proofs.Fast.R4Runs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# GasSteps composition for retained-frame n=4 squaring

`gasSteps_r4Cached` runs the arithmetic core from a cached modulus/inverse frame to a reduced
five-word stack window, preserving memory exactly. The tail then stores four limbs. Its local
zero-word invariant makes those stores equal to the previous five-store memory transformer.
A nonfinal round retains the cached frame; the final round restores the original caller frame.

These are execution/correctness relations; measured numerical gas savings are recorded in the
separate benchmark evidence.
-/

namespace CycleSubmission.Global.Fast.R4Trace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open R4Math R4Blocks R4Runs R4Bridge
open Challenge.EvmProof (GasSteps)

/-- The five-word accumulator window on the stack. -/
def win (W : W5) (tail : List UInt256) : List UInt256 :=
  W.t3 :: W.t2 :: W.t1 :: W.t0 :: W.t4 :: tail

local macro "lenOK" : tactic =>
  `(tactic| ((try simp only [List.length_cons, List.length_append, win] at *) <;> omega))

section
variable (s : State)
  (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
  (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

include hcode hfork hrun hnp

/-! Final conditional subtraction and stores. -/

/-- Apply the final conditional subtraction before storing four limbs. -/
def gasSteps_tail (W : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    GasSteps { s with pc := UInt256.ofNat 4727,
                      stack := win W (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 4732,
               stack := win (red4 n0 n1 n2 n3 W) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := W
  if h0 : t4.toNat = 0 then
    have ht : t4 = ⟨0⟩ := Challenge.EvmProof.Word.word_ext (by rw [h0]; rfl)
    subst ht
    have hr : red4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, ⟨0⟩⟩ = ⟨t0, t1, t2, t3, ⟨0⟩⟩ := if_pos rfl
    rw [hr]
    simp only [win]
    exact SquareRow.stepsOf R4InlineTailBlocks.block_tail (R4InlineTailRuns.run_tail_zero s t3 t2 t1 t0 _ (by lenOK)) rfl
      hcode hfork hrun hnp
  else
    have hne : t4 ≠ ⟨0⟩ := fun h => h0 (by rw [h]; rfl)
    have hr : red4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, t4⟩ = sub4 n0 n1 n2 n3 ⟨t0, t1, t2, t3, t4⟩ :=
      if_neg hne
    rw [hr]
    simp only [win]
    have hj77 : Decode.isValidJumpDest s.executionEnv.code 4769 = true := by
      rw [hcode]; exact R4InlineTailBlocks.jd4768
    have hj38 : Decode.isValidJumpDest s.executionEnv.code 4732 = true := by
      rw [hcode]; exact R4InlineTailBlocks.jd4731
    refine GasSteps.trans (SquareRow.stepsOf R4InlineTailBlocks.block_tail
      (R4InlineTailRuns.run_tail_rare s t3 t2 t1 t0 t4 _ (by lenOK) hne hj77) rfl hcode hfork hrun hnp) ?_
    exact SquareRow.stepsOf R4InlineTailBlocks.block_rare4
      (R4InlineTailRuns.run_rare4 s t3 t2 t1 t0 t4 k n0 n1 n2 n3 np rest (by lenOK) hj38) rfl hcode hfork hrun hnp

/-- Store four limbs and reuse the retained frame. -/
def gasSteps_st4More (P : W5) (k n0 n1 n2 n3 np e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    aprev c : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hact : 88 ≤ s.activeWords.toNat) (hc : UInt256.isTrue e0)
    (hz : R4RetainedMemory.ZeroTN s.memory) (ht : P.t4 = UInt256.ofNat 0) (hke : k = e5) :
    GasSteps { s with
      pc := UInt256.ofNat 4732,
      stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
        e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest) }
      { s with
      pc := UInt256.ofNat 4037, stack := n0 :: n1 :: n2 :: n3 :: np :: (e5 + e0) :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest, memory := r4Mem s.memory P } := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 4037 = true := by
    rw [hcode]; exact R4InlineTailBlocks.jd4280
  have h1 := R4InlineTailRuns.run_st4_stores s P.t3 P.t2 P.t1 P.t0
    (P.t4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
      e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest)
    (by lenOK) hact
  change _ = some { s with
      pc := UInt256.ofNat 4749,
      stack := P.t4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
      e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest,
      memory := R4RetainedMemory.fourStores s.memory P } at h1
  rw [R4RetainedMemory.fourStores_eq_r4Mem s.memory P hz ht] at h1
  have g1 := SquareRow.stepsOf R4InlineTailBlocks.block_st4 h1 rfl hcode hfork hrun hnp
  have h2 := R4InlineTailRuns.run_tail_moreAlias116 { s with memory := r4Mem s.memory P } P.t4 k n0 n1 n2 n3 np
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 aprev c rest (by lenOK) hke hc hj
  exact g1.trans (SquareRow.stepsOf R4InlineTailBlocks.block_branch h2 rfl hcode hfork hrun hnp)

/-- Store four limbs and restore the original frame on exit. -/
def gasSteps_st4Last (P : W5) (k n0 n1 n2 n3 np e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    aprev c : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hact : 88 ≤ s.activeWords.toNat) (hc : ¬ UInt256.isTrue e0)
    (hz : R4RetainedMemory.ZeroTN s.memory) (ht : P.t4 = UInt256.ofNat 0) (hke : k = e5) :
    GasSteps { s with
      pc := UInt256.ofNat 4732,
      stack := win P (k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
        e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest) }
      { s with
      pc := UInt256.ofNat 3482, stack := c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: (e5 + e0) :: rest, memory := r4Mem s.memory P } := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 3482 = true := by
    rw [hcode]; exact CycleSubmission.Global.Fast.R4InlineTrace.jd4248
  have h1 := R4InlineTailRuns.run_st4_stores s P.t3 P.t2 P.t1 P.t0
    (P.t4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
      e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest)
    (by lenOK) hact
  change _ = some { s with
      pc := UInt256.ofNat 4749,
      stack := P.t4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: e0 :: e1 :: e2 :: e3 :: e4 ::
      e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: aprev :: c :: rest,
      memory := R4RetainedMemory.fourStores s.memory P } at h1
  rw [R4RetainedMemory.fourStores_eq_r4Mem s.memory P hz ht] at h1
  have g1 := SquareRow.stepsOf R4InlineTailBlocks.block_st4 h1 rfl hcode hfork hrun hnp
  have h2 := R4InlineTailRuns.run_tail_fallAlias116 { s with memory := r4Mem s.memory P } P.t4 k n0 n1 n2 n3 np
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 aprev c rest (by lenOK) hke hc
  have g2 := SquareRow.stepsOf R4InlineTailBlocks.block_branch h2 rfl hcode hfork hrun hnp
  have h3 := R4InlineTailRuns.run_tail_exit { s with memory := r4Mem s.memory P } n0 n1 n2 n3 np
    (e5 + e0) e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 aprev c rest (by lenOK) hj
  exact (g1.trans g2).trans (SquareRow.stepsOf R4InlineTailBlocks.block_m4 h3 rfl hcode hfork hrun hnp)

end

/-! The complete relocated R4 routine. -/

/-- Run R4 from PC 4037 to the stores at PC 4732, preserving memory.
The existing caller frame retains modulus slots `e4 = n2`, `e7 = n1`, `e8 = n0`,
max-word `e5`, inverse `e11`, and carry cache `e12`. -/
def gasSteps_r4Cached (s : State) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hk : e5 = Monpro.maxWord)
    (hminv : (e8.toNat * e11.toNat + 1) % 2^256 = 0)
    (hguard : e11 ≠ UInt256.ofNat 1) :
    GasSteps
      { s with pc := UInt256.ofNat 4037,
               stack := e8 :: e7 :: e4 :: MachineState.readWord s.memory 0 :: e11 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest }
      { s with pc := UInt256.ofNat 4732,
               stack := win (red4 e8 e7 e4 (MachineState.readWord s.memory 0)
                   (r4Final s.memory e5 e8 e7 e4 e11))
                 (e5 :: e8 :: e7 :: e4 :: MachineState.readWord s.memory 0 :: e11 ::
                   e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest) }  := by
  have hc := R4InlineTrace.gasSteps_core s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    rest hcap hcode hfork hrun hnp hact hk hminv hguard
  have ht := gasSteps_tail s hcode hfork hrun hnp
    (r4Final s.memory e5 e8 e7 e4 e11) e5 e8 e7 e4
    (MachineState.readWord s.memory 0) e11
    (e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest)
    (by simp only [List.length_cons]; omega)
  exact hc.trans ht

end CycleSubmission.Global.Fast.R4Trace
