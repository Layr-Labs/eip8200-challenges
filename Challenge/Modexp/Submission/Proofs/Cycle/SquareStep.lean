import Challenge.Modexp.Submission.Proofs.Cycle.SquareExecution
import Challenge.Modexp.Submission.Proofs.Cycle.SquareNormalize
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.SquareStep
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open CycleSubmission.ControlArithmetic
open HistoricalSearch.MixedMontgomery

def zeroWords : Nat → UInt256 := fun _ => UInt256.ofNat 0
def digits (inv : UInt256) (a n : Nat → UInt256) : Nat → UInt256 :=
  normalized (squared inv a zeroWords n) n
def middle (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  SquareExecution.state15 s inv a zeroWords n rest
def result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  SquareNormalize.completed (middle s inv a n rest) (squared inv a zeroWords n) n rest

noncomputable def gasSteps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : SquareMeaning.Memory0 s.memory inv a zeroWords n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 5695, stack := SquareMeaning.frame0 inv a zeroWords n rest}
      (result s inv a n rest) := by
  have h1 := SquareExecution.gasSteps s inv a zeroWords n rest env h hcap hact
  have hm := SquareExecution.normalizer_input s inv a zeroWords n rest h
  have h2 := SquareNormalize.gasSteps (middle s inv a n rest) (squared inv a zeroWords n) n rest
    (env.transfer rfl rfl) hm hcap hact
  have he : SquareNormalize.initial (middle s inv a n rest) (squared inv a zeroWords n) n rest =
      middle s inv a n rest :=
    SquareExecution.reset_self _ _ _ rfl (SquareExecution.output_frame s inv a zeroWords n rest)
  rw [he] at h2
  exact h1.trans h2

theorem memory_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a zeroWords n) :
    SquareMeaning.Memory0 (result s inv a n rest).memory inv (digits inv a n) zeroWords n := by
  have m := SquareExecution.memory_output s inv a zeroWords n rest h
  have hm : SquareMeaning.Memory0 (middle s inv a n rest).memory inv (squared inv a zeroWords n) zeroWords n :=
    ⟨m.at768, m.at1344, m.at1376, m.at2720, m.at1568, m.at1600, m.at32, m.at64, m.at96, m.at128, m.at160⟩
  exact SquareNormalize.memory_output _ _ _ _ _ _ hm

theorem frame_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).stack = SquareMeaning.frame0 inv (digits inv a n) zeroWords n rest :=
  SquareNormalize.frame_output _ _ _ _

theorem pc_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).pc = UInt256.ofNat 7627 := by
  unfold result SquareNormalize.completed
  split_ifs <;> rfl

theorem arithmetic (inv : UInt256) (a n : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix) (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N) :
    (∀ i < 9, (digits inv a n i).toNat < radix) ∧
    value (digits inv a n) < radix^9 ∧
    value (digits inv a n) % N =
      Challenge.Modexp.Submission.Proofs.Fast.Model.montMul N (radix^9) (value a) (value a) := by
  have hz : ∀ i < 9, (zeroWords i).toNat < radix := by
    intro i hi
    exact Nat.two_pow_pos _
  have hlow := (squareTrace inv a zeroWords n).output_low_bound ha hz hn N hn0 hinv
  have hc := (squareTrace inv a zeroWords n).normalized_contract ha hz hn N hn0 hNvalue hinv hN hNR hodd
  have hnr : value n < radix^9 := by rw [hNvalue]; exact hNR
  have hu : value (squared inv a zeroWords n) < radix^9 + value n := by
    rw [hNvalue]
    exact hc.1
  have hd := normalized_bounded (squared inv a zeroWords n) n hlow hn hnr hu
  refine ⟨hd, ?_, ?_⟩
  · rw [digits, normalized_value (squared inv a zeroWords n) n hlow hn hnr, hNvalue]
    exact hc.2.1
  · rw [digits, normalized_value (squared inv a zeroWords n) n hlow hn hnr, hNvalue]
    exact hc.2.2

theorem executionEnv_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).executionEnv = s.executionEnv := by
  unfold result SquareNormalize.completed
  split_ifs <;> rfl
theorem halt_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).halt = s.halt := by
  unfold result SquareNormalize.completed
  split_ifs <;> rfl
theorem active_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).activeWords = s.activeWords := by
  unfold result SquareNormalize.completed
  split_ifs <;> rfl

theorem calls_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).callStack = s.callStack := by
  unfold result SquareNormalize.completed
  split_ifs <;> rfl

theorem keeps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (start count : Nat) (hs : 1312 ≤ start) :
    MachineState.readPadded (result s inv a n rest).memory start count =
      MachineState.readPadded s.memory start count := by
  have h := SquareExecution.memory15_keeps s.memory inv a zeroWords n start count (Or.inr hs)
  unfold result SquareNormalize.completed
  split_ifs
  · exact h
  · exact (NormalizeMeaning.preserves (middle s inv a n rest) (squared inv a zeroWords n) n
      (UInt256.ofNat 7627) (n 1) rest start count (Or.inr (by omega)) (Or.inr (by omega))).trans h

theorem keeps_base (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (start count : Nat) (hs : 256 ≤ start) (he : start+count ≤ 768) :
    MachineState.readPadded (result s inv a n rest).memory start count =
      MachineState.readPadded s.memory start count := by
  have h := SquareExecution.memory15_keeps s.memory inv a zeroWords n start count (Or.inl ⟨hs, he⟩)
  unfold result SquareNormalize.completed
  split_ifs
  · exact h
  · exact (NormalizeMeaning.preserves (middle s inv a n rest) (squared inv a zeroWords n) n
      (UInt256.ofNat 7627) (n 1) rest start count (Or.inr (by omega)) (Or.inl he)).trans h

end CycleSubmission.SquareStep
