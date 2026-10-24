import Challenge.Modexp.Submission.Proofs.Cycle.CompareScan
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeBinding
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.Canonical
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution
open CycleSubmission.ControlArithmetic (value)
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def digits (a n : Nat → UInt256) : Nat → UInt256 :=
  if value a < value n then a else output a n
def slot (a n : Nat → UInt256) (slot0 : UInt256) : UInt256 :=
  if value a < value n then slot0 else n 0
def result (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) : State :=
  if value a < value n then
    {s with pc := UInt256.ofNat 10867, stack := frame a n slot0 slot1 rest}
  else NormalizeBinding.returned s a n (UInt256.ofNat 10867) slot1 rest

noncomputable def subtraction (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10857, stack := frame a n slot0 slot1 rest}
      (NormalizeBinding.returned s a n (UInt256.ofNat 10867) slot1 rest) := by
  let ready : State := {s with
    pc := UInt256.ofNat 10866
    stack := UInt256.ofNat 11014 :: frame a n (UInt256.ofNat 10867) slot1 rest}
  have hr := canonicalsub_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  have h1 := FinalBlocks.canonicalsubBlock.steps
    (s := {s with pc := UInt256.ofNat 10857, stack := frame a n slot0 slot1 rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest ready.executionEnv.code 11014 = true := by
    rw [show ready.executionEnv.code = Artifact.bytecode from env.code]
    exact FinalBlocks.validJump11014
  have cap : ready.stack.length < 1024 := by
    simp only [ready, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jump_run ready (UInt256.ofNat 11014) (frame a n (UInt256.ofNat 10867) slot1 rest) rfl cap valid
  have h2 := FinalBlocks.canonicalJumpBlock.steps (s := ready) (env.transfer rfl rfl) rfl hj
  have h3 := NormalizeBinding.gasSteps s a n (UInt256.ofNat 10867) slot1 rest
    env hm hcap hact NormalizeBinding.validJump10867
  exact h1.trans (h2.trans h3)

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 8, (n i).toNat < 2^240) :
    GasSteps {s with pc := UInt256.ofNat 10692, stack := frame a n slot0 slot1 rest}
      (result s a n slot0 slot1 rest) := by
  have h := CompareScan.gasSteps s a n slot0 slot1 rest env hm hcap hact ha hn
  by_cases hl : value a < value n
  · simpa only [result, if_pos hl] using h
  · simp only [result, if_neg hl] at h ⊢
    exact h.trans (subtraction s a n slot0 slot1 rest env hm hcap hact)

theorem memory_output (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (hm : MemoryInput s.memory a n) :
    MemoryInput (result s a n slot0 slot1 rest).memory (digits a n) n := by
  by_cases hl : value a < value n
  · simpa only [result, digits, if_pos hl] using hm
  · simpa only [result, digits, if_neg hl, NormalizeBinding.returned] using
      NormalizeMeaning.memory_output s a n (UInt256.ofNat 10867) slot1 rest hm

theorem frame_output (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) :
    (result s a n slot0 slot1 rest).stack = frame (digits a n) n (slot a n slot0) slot1 rest := by
  by_cases hl : value a < value n <;>
    simp only [result, digits, slot, hl, ite_true, ite_false, NormalizeBinding.returned, NormalizeMeaning.result]

theorem pc_output (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) :
    (result s a n slot0 slot1 rest).pc = UInt256.ofNat 10867 := by
  unfold result; split_ifs <;> rfl
theorem executionEnv_eq (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) :
    (result s a n slot0 slot1 rest).executionEnv = s.executionEnv := by
  unfold result; split_ifs <;> rfl
theorem halt_eq (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) :
    (result s a n slot0 slot1 rest).halt = s.halt := by
  unfold result; split_ifs <;> rfl
theorem active_eq (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) :
    (result s a n slot0 slot1 rest).activeWords = s.activeWords := by
  unfold result; split_ifs <;> rfl

theorem arithmetic (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (hN : 0 < value n) (hNR : value n < (2^240)^9) (hT : value a < 2*value n) :
    value (digits a n) = value a % value n ∧
    (∀ i < 9, (digits a n i).toNat < 2^240) := by
  have hv : value (digits a n) = value a % value n := by
    by_cases hl : value a < value n
    · simp only [digits, if_pos hl, Nat.mod_eq_of_lt hl]
    · have ho : value n ≤ value a := by omega
      have hs := output_value a n ha hn ho
      change value (output a n) + value n = value a at hs
      have hc := CycleSubmission.Radix.canonicalExit (value n) (value a) hT
      rw [if_pos ho] at hc
      simp only [digits, if_neg hl]
      omega
  refine ⟨hv, ?_⟩
  have hr : value (digits a n) < (2^240)^9 := by
    rw [hv]; exact Nat.lt_trans (Nat.mod_lt _ hN) hNR
  intro i hi
  by_cases he : i = 8
  · subst i
    exact top_digit_bounded (2^240) 8 (fun j => (digits a n j).toNat) (Nat.two_pow_pos _) hr
  · have hil : i < 8 := by omega
    by_cases hl : value a < value n
    · simpa only [digits, if_pos hl] using ha i hil
    · simpa only [digits, if_neg hl] using output_low_bounded a n ha hn i hil

end CycleSubmission.Canonical
