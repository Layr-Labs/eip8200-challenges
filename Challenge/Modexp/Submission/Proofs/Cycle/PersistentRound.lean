import Challenge.Modexp.Submission.Proofs.Cycle.PersistentBinding
import Challenge.Modexp.Submission.Proofs.Cycle.SquareArithmetic
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000
namespace CycleSubmission.PersistentRound
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open CycleSubmission.ControlArithmetic
open CycleSubmission.SquareStep (zeroWords)
open Challenge.Modexp.Submission.Proofs.Fast.Model
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
def result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat (if (PersistentSquareLoop.counter s).toNat = 0 then 5807 else 3487),memory := R9InvConsumeComplete.historyMemory s.memory inv a zeroWords n,stack := PersistentCounter.frame inv (UInt256.ofNat 1+PersistentSquareLoop.counter s) (squared inv a zeroWords n) zeroWords n rest}
theorem counter_result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
 PersistentSquareLoop.counter (result s inv a n rest) =
 UInt256.ofNat 1+PersistentSquareLoop.counter s := by rfl
theorem frame_result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
 (result s inv a n rest).stack = PersistentSquareLoop.frame inv (squared inv a zeroWords n) n
   (PersistentSquareLoop.counter (result s inv a n rest)::rest) := by
 rw [counter_result]
 cases rest <;> rfl
noncomputable def steps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (env : Environment Artifact.artifact .Osaka s)
 (hm : LimbMemory.Holds s.memory inv a zeroWords n)
 (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (ha : ∀ i < 8,(a i).toNat < radix) :
 GasSteps {s with pc := UInt256.ofNat 3487,stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter s::rest)}
  (result s inv a n rest) := by
 cases rest with
 | nil => simp at hcache
 | cons value rest =>
  have hv : value = inv := by simpa using hcache
  subst value
  exact PersistentBinding.round_steps s inv (PersistentSquareLoop.counter s) a zeroWords n rest env
   (by simp at hcap; omega) hact hm ha
noncomputable def certificate : PersistentSquareLoop.StepCertificate 3487 5807 := by
 intro s inv a n rest k N x hk hk16 env hm hc hcache hcap hact ha hn hn0 hNvalue hinv hN hNR hodd hN4 hsmall hform
 have hno := SquareStep.no_overflow inv a n ha hn N hn0 hNvalue hinv hN hN4 hsmall
 have harith := SquareStep.arithmetic inv a n ha hn N hn0 hNvalue hinv hN hNR hodd
 have he : SquareStep.digits inv a n = squared inv a zeroWords n := by
  simp only [SquareStep.digits,normalized,if_pos hno.1]
 rw [he] at harith
 refine ⟨result s inv a n rest,squared inv a zeroWords n,
   steps s inv a n rest env hm hcache hcap hact (fun i hi => ha i (by omega)),
   PersistentCounter.memory_output s.memory inv a zeroWords n hm,
   frame_result s inv a n rest,?_,rfl,rfl,rfl,harith.1,hno.2,?_,?_,?_,rfl⟩
 · change UInt256.ofNat (if (PersistentSquareLoop.counter s).toNat = 0 then 5807 else 3487) = _
   rw [hc]
   interval_cases k <;> rfl
 · change value (squared inv a zeroWords n) % N = ((x*x)*radix^9) % N
   rw [harith.2.2]
   exact montMul_form hN (CycleSubmission.Radix.oddCoprime 240 N hodd) hform hform
 · intro hmore
   rw [counter_result,hc]
   interval_cases k <;> rfl
 · intro start count hlo hhi
   exact PersistentMemory.keeps_base s.memory inv a zeroWords n start count hlo hhi
#print axioms steps
#print axioms certificate
end CycleSubmission.PersistentRound
