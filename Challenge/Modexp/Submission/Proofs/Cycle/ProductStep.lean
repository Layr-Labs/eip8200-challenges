import Challenge.Modexp.Submission.Proofs.Cycle.ProductExecution
import Challenge.Modexp.Submission.Proofs.Cycle.SquareExecution
import Challenge.Modexp.Submission.Proofs.Cycle.Canonical
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.ProductStep
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open CycleSubmission.ControlArithmetic (value)
open HistoricalSearch.MixedMontgomery

def digits (inv : UInt256) (a b n : Nat → UInt256) : Nat → UInt256 :=
  Canonical.digits (productd inv a b n) n
def middle (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  ProductExecution.state20 s inv a b n rest
def slot0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 :=
  Canonical.slot (productd inv a b n) n (productQ8 inv a b n)
def result (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  Canonical.result (middle s inv a b n rest) (productd inv a b n) n
    (productQ8 inv a b n) (productQ7 inv a b n) rest

noncomputable def gasSteps (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : ProductMeaning.Memory0 s.memory inv a b n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix) (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    GasSteps {s with pc := UInt256.ofNat 8202, stack := ProductMeaning.frame0 inv a b n rest}
      (result s inv a b n rest) := by
  have h1 := ProductExecution.gasSteps s inv a b n rest env hm hcap hact
  have hm2 := ProductExecution.normalizer_input s inv a b n rest hm
  have hlow := (productTrace inv a b n).output_low_bound ha hb hn N hn0 hinv
  have h2 := Canonical.gasSteps (middle s inv a b n rest) (productd inv a b n) n
    (productQ8 inv a b n) (productQ7 inv a b n) rest (env.transfer rfl rfl)
    hm2 hcap hact hlow (fun i hi => hn i (by omega))
  have he : {middle s inv a b n rest with
      pc := UInt256.ofNat 10692
      stack := NormalizeMeaning.frame (productd inv a b n) n
        (productQ8 inv a b n) (productQ7 inv a b n) rest} = middle s inv a b n rest :=
    SquareExecution.reset_self _ _ _ rfl (ProductExecution.output_frame s inv a b n rest)
  rw [he] at h2
  exact h1.trans h2

theorem memory_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (hm : ProductMeaning.Memory0 s.memory inv a b n) :
    NormalizeMeaning.MemoryInput (result s inv a b n rest).memory (digits inv a b n) n :=
  Canonical.memory_output _ _ _ _ _ _ (ProductExecution.normalizer_input s inv a b n rest hm)

theorem frame_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).stack = NormalizeMeaning.frame (digits inv a b n) n
      (slot0 inv a b n) (productQ7 inv a b n) rest :=
  Canonical.frame_output _ _ _ _ _ _
theorem pc_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).pc = UInt256.ofNat 10867 := Canonical.pc_output _ _ _ _ _ _
theorem executionEnv_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).executionEnv = s.executionEnv := Canonical.executionEnv_eq _ _ _ _ _ _
theorem halt_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).halt = s.halt := Canonical.halt_eq _ _ _ _ _ _
theorem active_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).activeWords = s.activeWords := Canonical.active_eq _ _ _ _ _ _

theorem calls_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a b n rest).callStack = s.callStack := by
  unfold result Canonical.result
  split_ifs <;> rfl

theorem arithmetic (inv : UInt256) (a b n : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix) (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N x : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N)
    (hB : value b < N) (hform : value a ≡ x*radix^9 [MOD N]) :
    (∀ i < 9, (digits inv a b n i).toNat < radix) ∧
    value (digits inv a b n) = value b*x % N := by
  have hA := weightedBound radix 9 (fun i => (a i).toNat) (Nat.two_pow_pos _) ha
  have hQ := weightedBound radix 9 (fun i => (productq inv a b n i).toNat)
    (Nat.two_pow_pos _) (productTrace inv a b n).q_bound
  have he := (productTrace inv a b n).exact_product ha hb hn N hn0 hinv
  change value (productd inv a b n)*radix^9 = value a*value b + value (productq inv a b n)*value n at he
  rw [hNvalue] at he
  have hR : 0 < radix^9 := Nat.pow_pos (Nat.two_pow_pos _)
  have hT := Radix.finalProductRange (radix^9) N (value a) (value b) (value (productq inv a b n))
    (value (productd inv a b n)) hR hN hA hB hQ he
  have hlow := (productTrace inv a b n).output_low_bound ha hb hn N hn0 hinv
  have hc := Canonical.arithmetic (productd inv a b n) n hlow hn
    (by rw [hNvalue]; exact hN) (by rw [hNvalue]; exact hNR) (by rw [hNvalue]; exact hT)
  have hm := Radix.finalProductContract (radix^9) N (value a) (value b) (value (productq inv a b n))
    (value (productd inv a b n)) x hR hN hA hB hQ (Radix.oddCoprime 240 N hodd) he hform
  rw [Radix.canonicalExit N (value (productd inv a b n)) hT] at hm
  refine ⟨hc.2, ?_⟩
  change value (Canonical.digits (productd inv a b n) n) = _
  rw [hc.1, hNvalue]
  exact hm

end CycleSubmission.ProductStep
