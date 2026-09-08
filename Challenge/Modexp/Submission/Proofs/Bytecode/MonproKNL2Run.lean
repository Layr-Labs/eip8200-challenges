import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNPointers
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEight

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2Run

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNLoopPaths
open MonproKNDispatchWords MonproKNResidue MonproKNCache WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def state (s : State) (mem : ByteArray) (bi mu c0 : UInt256) (n : Nat)
    (pbi paEnd pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (completed pc : Nat) : State :=
  MonproKNL2.state s (UInt256.ofNat pc) mem bi mu c0 n completed
    pbi paEnd pbEnd destination returnPC rest

def copies {artifact : ProgramArtifact} {fork : Fork} (paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256) (n : Nat)
    (pbi paEnd pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) :
    MonproKNEight.Copies
      (fun completed slot => state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest
        completed (l2PC slot))
      (state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest (n-1) 2435) (n-1) := by
  let walkState := state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest
  have step : ∀ j slot, j+1 < n → slot < 8 →
      GasSteps (walkState j (l2PC slot)) (walkState (j+1) (l2PC slot + 41)) := by
    intro j slot hj hslot
    have hr := MonproKNL2.run_step s (UInt256.ofNat (l2PC slot)) mem bi mu c0 n j
      pbi paEnd pbEnd destination returnPC rest hrest hactive hn hj
    rw [Word.ofNat_add_mod] at hr
    exact (paths.body slot hslot).steps
      (env.transfer (t := walkState j (l2PC slot)) rfl rfl) rfl hr
  have test : ∀ j, j+1 ≤ n →
      GasSteps (walkState j 2426)
        (walkState j (if j+1 < n then 2098 else 2435)) := by
    intro j hj
    let st := walkState j 2426
    have hcap : st.stack.length + 2 < 1024 := by
      simp only [st, walkState, state, MonproKNL2.state, List.length_append,
        List.length_cons, List.length_nil]
      omega
    have htarget : Decode.isValidJumpDest st.executionEnv.code 2098 = true := by
      change Decode.isValidJumpDest s.executionEnv.code 2098 = true
      rw [env.code]
      exact paths.jump 0 (by decide)
    have hr := MonproKNLoopTests.run_l2_test st st.stack
      (UInt256.ofNat (ptrAt (8192 + 32*n) j)) hcap rfl htarget
    have hcondition := MonproKNPointers.l2_condition n j hn hj
    simp only [hcondition] at hr
    have hpc : (if j+1 < n then UInt256.ofNat 2098 else UInt256.ofNat 2435) =
        UInt256.ofNat (if j+1 < n then 2098 else 2435) := by
      by_cases hc : j+1 < n <;> simp [hc]
    rw [hpc] at hr
    exact paths.test.steps (env.transfer (t := st) rfl rfl) rfl hr
  refine ⟨?_, ?_, ?_⟩
  · intro j slot hj hslot
    simpa only [l2PC_next] using step j slot (by omega) (by omega)
  · intro j hj
    have ht := test (j+1) (by omega)
    rw [if_pos (by omega : j+1+1 < n)] at ht
    exact (step j 7 (by omega) (by decide)).trans ht
  · intro j hj
    have ht := test (j+1) (by omega)
    rw [if_neg (by omega : ¬ j+1+1 < n)] at ht
    simpa only [hj] using (step j 7 (by omega) (by decide)).trans ht

/-- Exactly n-1 MACs, even when the first suffix is shorter than eight. -/
def run {artifact : ProgramArtifact} {fork : Fork} (paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256) (n : Nat)
    (pbi paEnd pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpositive : 2 ≤ n) :
    GasSteps (state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest 0 2077)
      (state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest (n-1) 2435) := by
  let st := state s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest 0 2077
  have hcap : st.stack.length + 2 < 1024 := by
    simp only [st, state, MonproKNL2.state, List.length_append,
      List.length_cons, List.length_nil]
    omega
  have hslot := MonproKNPointers.l2_slot n 0 hn (by omega)
  simp only [Nat.sub_zero] at hslot
  have hpc : (UInt256.ofNat (l2PC (residue (n-1)))).toNat = l2PC (residue (n-1)) := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    have := residue_lt (n-1)
    simp only [l2PC]
    omega
  have htarget : Decode.isValidJumpDest st.executionEnv.code
      (UInt256.ofNat (l2PC (residue (n-1)))).toNat = true := by
    rw [hpc]
    change Decode.isValidJumpDest s.executionEnv.code (l2PC (residue (n-1))) = true
    rw [env.code]
    exact paths.jump _ (residue_lt (n-1))
  have hr := MonproKNDispatch.run_l2 st st.stack
    (UInt256.ofNat (ptrAt (8192 + 32*n) 0))
    (residue (n-1)) hcap rfl hslot htarget
  have hd := paths.dispatch.steps (env.transfer (t := st) rfl rfl) rfl hr
  exact hd.trans (MonproKNEight.l2Trace n hpositive
    (copies paths s mem bi mu c0 n pbi paEnd pbEnd destination returnPC rest env hrest hactive hn))

/-- The smallest width enters copy seven and exits after one semantic update. -/
def single {artifact : ProgramArtifact} {fork : Fork} (paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi paEnd pbEnd destination returnPC : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ s.activeWords.toNat) :
    GasSteps (state s mem bi mu c0 2 pbi paEnd pbEnd destination returnPC rest 0 2385)
      (state s mem bi mu c0 2 pbi paEnd pbEnd destination returnPC rest 1 2435) :=
  MonproKNEight.l2Single
    (copies paths s mem bi mu c0 2 pbi paEnd pbEnd destination returnPC rest
      env hrest hactive (by decide))

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2Run
