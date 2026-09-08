import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNPointers
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEight

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL1Run

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNLoopPaths
open MonproKNDispatchWords MonproKNResidue MonproKNCache WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def state (s : State) (mem : ByteArray) (bi : UInt256) (pa n : Nat)
    (pbi pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (completed pc : Nat) : State :=
  MonproKNL1.state s (UInt256.ofNat pc) mem bi pa n completed
    pbi (UInt256.ofNat (pa - 32)) pbEnd destination returnPC rest

def copies {artifact : ProgramArtifact} {fork : Fork} (paths : L1Paths artifact fork)
    (s : State) (mem : ByteArray) (bi : UInt256) (pa n : Nat)
    (pbi pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32)
    (hpa : 32 ≤ pa) (hfit : pa + 32 * n ≤ 9472) :
    MonproKNEight.Copies
      (fun completed slot => state s mem bi pa n pbi pbEnd destination returnPC rest
        completed (l1PC slot))
      (state s mem bi pa n pbi pbEnd destination returnPC rest n 2008) n := by
  let walkState := state s mem bi pa n pbi pbEnd destination returnPC rest
  have step : ∀ j slot, j < n → slot < 8 →
      GasSteps (walkState j (l1PC slot)) (walkState (j+1) (l1PC slot + 38)) := by
    intro j slot hj hslot
    have hr := MonproKNL1.run_step s (UInt256.ofNat (l1PC slot)) mem bi pa n j
      pbi (UInt256.ofNat (pa - 32)) pbEnd destination returnPC rest
      hrest hactive hn hj hpa hfit
    rw [Word.ofNat_add_mod] at hr
    exact (paths.body slot hslot).steps
      (env.transfer (t := walkState j (l1PC slot)) rfl rfl) rfl hr
  have test : ∀ j, j ≤ n →
      GasSteps (walkState j 4393)
        (walkState j (if j < n then 4089 else 4400)) := by
    intro j hj
    let st := walkState j 4393
    have hcap : st.stack.length + 2 < 1024 := by
      simp only [st, walkState, state, MonproKNL1.state, List.length_append,
        List.length_cons, List.length_nil]
      omega
    have htarget : Decode.isValidJumpDest st.executionEnv.code 4089 = true := by
      change Decode.isValidJumpDest s.executionEnv.code 4089 = true
      rw [env.code]
      exact paths.jump 0 (by decide)
    have hr := MonproKNLoopTests.run_l1_test st st.stack
      (UInt256.ofNat (ptrAt (pa + 32*n - 32) j)) (UInt256.ofNat (pa-32))
      hcap rfl rfl htarget
    have hcondition := MonproKNPointers.l1_condition pa n j hpa hfit hj
    simp only [hcondition] at hr
    have hpc : (if j < n then UInt256.ofNat 4089 else UInt256.ofNat 4400) =
        UInt256.ofNat (if j < n then 4089 else 4400) := by
      by_cases hc : j < n <;> simp [hc]
    rw [hpc] at hr
    exact paths.test.steps (env.transfer (t := st) rfl rfl) rfl hr
  have leave : ∀ j, GasSteps (walkState j 4400) (walkState j 2008) := by
    intro j
    let st := walkState j 4400
    have hcap : st.stack.length + 1 < 1024 := by
      simp only [st, walkState, state, MonproKNL1.state, List.length_append,
        List.length_cons, List.length_nil]
      omega
    have htarget : Decode.isValidJumpDest st.executionEnv.code 2008 = true := by
      change Decode.isValidJumpDest s.executionEnv.code 2008 = true
      rw [env.code]
      exact paths.middle
    have hr := MonproKNLoopTests.run_l1_exit st st.stack hcap htarget
    exact paths.exit.steps (env.transfer (t := st) rfl rfl) rfl hr
  refine ⟨?_, ?_, ?_⟩
  · intro j slot hj hslot
    simpa only [l1PC_next] using step j slot (by omega) (by omega)
  · intro j hj
    have ht := test (j+1) (by omega)
    rw [if_pos hj] at ht
    exact (step j 7 (by omega) (by decide)).trans ht
  · intro j hj
    have ht := test (j+1) (by omega)
    rw [if_neg (by omega : ¬ j+1 < n)] at ht
    simpa only [hj] using
      (step j 7 (by omega) (by decide)).trans (ht.trans (leave (j+1)))

/-- A real located dispatch, one suffix, and enough whole blocks: exactly n MACs. -/
def run {artifact : ProgramArtifact} {fork : Fork} (paths : L1Paths artifact fork)
    (s : State) (mem : ByteArray) (bi : UInt256) (pa n : Nat)
    (pbi pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpositive : 2 ≤ n)
    (hpa : 32 ≤ pa) (hfit : pa + 32 * n ≤ 9472) :
    GasSteps (state s mem bi pa n pbi pbEnd destination returnPC rest 0 4070)
      (state s mem bi pa n pbi pbEnd destination returnPC rest n 2008) := by
  let st := state s mem bi pa n pbi pbEnd destination returnPC rest 0 4070
  have hcap : st.stack.length + 2 < 1024 := by
    simp only [st, state, MonproKNL1.state, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have hslot := MonproKNPointers.l1_slot pa n 0 hpa hfit hn (by omega)
  simp only [Nat.sub_zero] at hslot
  have hpc : (UInt256.ofNat (l1PC (residue n))).toNat = l1PC (residue n) := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    have := residue_lt n
    simp only [l1PC]
    omega
  have htarget : Decode.isValidJumpDest st.executionEnv.code
      (UInt256.ofNat (l1PC (residue n))).toNat = true := by
    rw [hpc]
    change Decode.isValidJumpDest s.executionEnv.code (l1PC (residue n)) = true
    rw [env.code]
    exact paths.jump _ (residue_lt n)
  have hr := MonproKNDispatch.run_l1 st st.stack
    (UInt256.ofNat (ptrAt (pa + 32*n - 32) 0)) (UInt256.ofNat (pa-32))
    (residue n) hcap rfl rfl hslot htarget
  have hd := paths.dispatch.steps (env.transfer (t := st) rfl rfl) rfl hr
  exact hd.trans (MonproKNEight.l1Trace n hpositive
    (copies paths s mem bi pa n pbi pbEnd destination returnPC rest env hrest hactive hn hpa hfit))

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL1Run
