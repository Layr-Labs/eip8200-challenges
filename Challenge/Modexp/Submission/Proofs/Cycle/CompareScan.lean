import Challenge.Modexp.Submission.Proofs.Cycle.CompareExecution
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
import Challenge.Modexp.Submission.Proofs.Cycle.CompareArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.CompareScan
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open CycleSubmission.CompareExecution CycleSubmission.CompareArithmetic

noncomputable def scan1 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10373, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 1), stack := frame a n slot0 slot1 rest} := by
  have hl := step16 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 0).toNat < (n 0).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step17 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 0).toNat < (a 0).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans hg

noncomputable def scan2 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10353, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 2), stack := frame a n slot0 slot1 rest} := by
  have hl := step14 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 1).toNat < (n 1).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step15 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 1).toNat < (a 1).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan1 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan3 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10339, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 3), stack := frame a n slot0 slot1 rest} := by
  have hl := step12 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 2).toNat < (n 2).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step13 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 2).toNat < (a 2).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan2 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan4 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10321, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 4), stack := frame a n slot0 slot1 rest} := by
  have hl := step10 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 3).toNat < (n 3).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step11 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 3).toNat < (a 3).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan3 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan5 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10303, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 5), stack := frame a n slot0 slot1 rest} := by
  have hl := step8 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 4).toNat < (n 4).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step9 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 4).toNat < (a 4).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan4 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan6 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10285, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 6), stack := frame a n slot0 slot1 rest} := by
  have hl := step6 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 5).toNat < (n 5).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step7 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 5).toNat < (a 5).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan5 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan7 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10267, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 7), stack := frame a n slot0 slot1 rest} := by
  have hl := step4 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 6).toNat < (n 6).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step5 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 6).toNat < (a 6).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan6 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan8 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10249, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 8), stack := frame a n slot0 slot1 rest} := by
  have hl := step2 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 7).toNat < (n 7).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step3 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 7).toNat < (a 7).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan7 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def scan9 (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10234, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (destination a n 9), stack := frame a n slot0 slot1 rest} := by
  have hl := step0 s a n slot0 slot1 rest env hm hcap hact
  rw [destination]
  by_cases hlt : (a 8).toNat < (n 8).toNat
  · simpa only [if_pos hlt] using hl
  · simp only [if_neg hlt] at hl ⊢
    have hg := step1 s a n slot0 slot1 rest env hm hcap hact
    by_cases hgt : (n 8).toNat < (a 8).toNat
    · simp only [if_pos hgt] at hg ⊢
      exact hl.trans hg
    · simp only [if_neg hgt] at hg ⊢
      exact hl.trans (hg.trans (scan8 s a n slot0 slot1 rest env hm hcap hact))

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 8, (n i).toNat < 2^240) :
    GasSteps {s with pc := UInt256.ofNat 10234, stack := frame a n slot0 slot1 rest}
      {s with pc := UInt256.ofNat (if ControlArithmetic.value a < ControlArithmetic.value n then 10409 else 10399), stack := frame a n slot0 slot1 rest} := by
  have h := scan9 s a n slot0 slot1 rest env hm hcap hact
  rw [final_destination a n ha hn] at h
  exact h
end CycleSubmission.CompareScan
