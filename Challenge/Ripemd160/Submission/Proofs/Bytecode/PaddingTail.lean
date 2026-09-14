import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTail
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PaddingTrace

def gasSteps_entry (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Execution.atPC input 341) rho)
      (StackTail.append (Main.initializedState input) rho) := by
  apply StackTail.gasSteps Execution.path_3ee rho
  · change 0 + rho.length + 1 < 1024
    omega
  · simp [Execution.path_3ee, DataStepper.runLocatedBlock, DataStepper.runLocated,
      DataStepper.runInstr, Execution.atPC, Main.initializedState, Execution.mainStart,
      initialState]
  · rfl
  · rfl
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_push (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (padCopied input) rho)
      (StackTail.append (padFramed input) rho) := by
  have g := StaggerPersistentStart.gasSteps_push (padCopied input) (Padding.paddedWord input)
    ([DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] ++ rho)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rfl rfl rfl deployAddress_not_precompile
  simpa only [StackTail.append, padCopied, padFramed, padFrame,
    StaggerPersistentFrame.frame, List.append_assoc, List.cons_append, List.nil_append] using g

def gasSteps_prefix (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Execution.atPC input 341) rho)
      (StackTail.append (padFramed input) rho) :=
  (gasSteps_entry input rho hcap).trans
    ((tail_enter input rho hcap).trans ((tail_length input rho hcap).trans
      ((tail_copy input hfit rho hcap).trans (gasSteps_push input rho hcap))))

def gasSteps_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hnz : input.size % 64 ≠ 0)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (padFramed input) rho)
      (StackTail.append (padGuardMiss input) rho) := by
  have g := tail_guardTaken input hfit hnz rho hcap
  have hc : (padFrame input ++ rho).length ≤ 1000 := by
    rw [List.length_append, padFrame_length]
    omega
  have gp := StaggerPersistentStart.gasSteps_partial (padGuardMiss input)
    (padFrame input ++ rho) (by omega) rfl rfl rfl deployAddress_not_precompile
  have gn := StaggerPersistentStart.gasSteps_guard32_miss (padGuardMiss input)
    (padFrame input ++ rho) hc (by exact Nat.lt_trans hfit (by norm_num)) hn32
    rfl rfl rfl deployAddress_not_precompile
  exact g.trans (gp.trans gn)

def gasSteps_setup (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (padGuardMiss input) rho)
      (StackTail.append (lengthLoopState input 0) rho) := by
  have g1 := tail_sentinelAddress input rho hcap
  have g2 := tail_sentinelStore input hfit rho hcap
  rw [tail_sentinel_eq input hfit] at g2
  exact g1.trans (g2.trans (tail_footer input rho hcap))

def gasSteps_iteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hne : lengthShift input (i + 1) ≠ ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (lengthLoopState input i) rho)
      (StackTail.append (lengthLoopState input (i + 1)) rho) := by
  have g1 := tail_body input hfit i hi rho hcap
  have g2 := tail_back input i hne rho hcap
  rw [tail_back_eq input i] at g2
  exact g1.trans g2

def gasSteps_iterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hz : lengthShift input (i + 1) = ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (lengthLoopState input i) rho)
      (StackTail.append (lengthExitReturned input (i + 1)) rho) := by
  have g1 := tail_body input hfit i hi rho hcap
  have g2 := tail_exitBranch input i hz rho hcap
  rw [tail_exit_eq input i] at g2
  exact g1.trans (g2.trans (tail_exitPop input (i + 1) rho hcap))

noncomputable def gasSteps_loopFrom (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    (fuel i : Nat) → i + fuel = 9 →
      (∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩) →
      lengthShift input i ≠ ⟨0⟩ →
    GasSteps (StackTail.append (lengthLoopState input i) rho)
      (StackTail.append (padReturned input) rho)
  | 0, i, hsum, _hprior, hne => by
      have hi : i = 9 := by omega
      subst hi
      exact False.elim (hne (lengthShift_nine input hfit))
  | fuel + 1, i, hsum, hprior, hne =>
      if hz : lengthShift input (i + 1) = ⟨0⟩ then
        have hstop := lengthStop_eq_succ_of_nonzero input i (by omega) hprior hz
        have hret : lengthExitReturned input (i + 1) = padReturned input := by
          rw [← hstop]
          exact tail_returned_eq input hfit
        GasSteps.cast (gasSteps_iterationExit input hfit i (by omega) hz rho hcap)
          rfl (congrArg (fun s => StackTail.append s rho) hret)
      else
        have hprior' : ∀ j, 0 < j → j ≤ i + 1 → lengthShift input j ≠ ⟨0⟩ := by
          intro j hj hjle
          by_cases hji : j ≤ i
          · exact hprior j hj hji
          · have hjeq : j = i + 1 := by omega
            subst hjeq
            exact hz
        (gasSteps_iteration input hfit i (by omega) hz rho hcap).trans
          (gasSteps_loopFrom input hfit rho hcap fuel (i + 1) (by omega) hprior' hz)

noncomputable def gasSteps_loop (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (lengthLoopState input 0) rho)
      (StackTail.append (padReturned input) rho) :=
  if hz : lengthShift input 1 = ⟨0⟩ then
    have hstop := lengthStop_eq_succ_of_nonzero input 0 (by norm_num)
      (fun j hj hle => by omega) hz
    have hstop' : lengthStop input = 1 := by simpa using hstop
    have hret : lengthExitReturned input 1 = padReturned input := by
      rw [← hstop']
      exact tail_returned_eq input hfit
    GasSteps.cast (gasSteps_iterationExit input hfit 0 (by norm_num) hz rho hcap)
      rfl (congrArg (fun s => StackTail.append s rho) hret)
  else
    (gasSteps_iteration input hfit 0 (by norm_num) hz rho hcap).trans
      (gasSteps_loopFrom input hfit rho hcap 8 1 (by norm_num)
        (fun j hj hle => by
          have hj1 : j = 1 := by omega
          subst hj1
          exact hz) hz)

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Execution.atPC input 341) rho)
      (StackTail.append (entryState input) rho) := by
  have gp := gasSteps_prefix input hfit rho hcap
  by_cases hz : input.size % 64 = 0
  · rw [entryState_skip input hz]
    exact gp.trans (tail_guardSkip input hfit hz rho hcap)
  · rw [entryState_miss input hz]
    exact gp.trans ((gasSteps_guardMiss input hfit hn32 hz rho hcap).trans
      ((gasSteps_setup input hfit rho hcap).trans (gasSteps_loop input hfit rho hcap)))

#print axioms gasSteps_prefix
#print axioms gasSteps_pad
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTail
