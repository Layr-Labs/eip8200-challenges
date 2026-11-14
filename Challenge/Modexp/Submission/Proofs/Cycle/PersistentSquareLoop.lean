import Challenge.Modexp.Submission.Proofs.Cycle.LimbMemory
import Challenge.Modexp.Submission.Proofs.Cycle.SquareArithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.PersistentSquareLoop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.WordArithmetic
open CycleSubmission.ControlArithmetic (value)
open CycleSubmission.SquareStep (zeroWords)
def counter (s : State) : UInt256 := s.stack.getD 15 (UInt256.ofNat 0)
def frame (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
 ((SquareMeaning.frame0 inv a zeroWords n ((a 8)::(rest.take 1++rest.drop 2))).set 10 (a 5)).set 13 (UInt256.ofNat (2^240-1))
theorem reset_self (s : State) (pc : UInt256) (stack : List UInt256)
 (hp : s.pc = pc) (hs : s.stack = stack) : {s with pc := pc,stack := stack} = s := by
 rw [← hp,← hs]
variable (startPC exitPC : Nat)
structure Outcome (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (count N x : Nat) where
  state : State
  output : Nat → UInt256
  trace : GasSteps {s with pc := UInt256.ofNat startPC,stack := frame inv a n (counter s::rest)} state
  memory : LimbMemory.Holds state.memory inv output zeroWords n
  frame : state.stack = frame inv output n (counter state::rest)
  pc : state.pc = UInt256.ofNat exitPC
  env : state.executionEnv = s.executionEnv
  halt : state.halt = s.halt
  active : state.activeWords = s.activeWords
  bounded : ∀ i < 9,(output i).toNat < radix
  small : value output + 2*N ≤ radix^9
  form : value output ≡ x^(2^count)*radix^9 [MOD N]
  keepsBase : ∀ start count,256 ≤ start → start+count ≤ 768 →
    MachineState.readPadded state.memory start count = MachineState.readPadded s.memory start count
  calls : state.callStack = s.callStack
theorem next_exponent (x k : Nat) (hk : 1 ≤ k) :
    (x*x)^(2^(k-1)) = x^(2^k) := by
  rw [← Nat.pow_two,← Nat.pow_mul,Nat.mul_comm 2,← Nat.pow_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel hk]
structure RoundOutcome (s : State) (inv : UInt256) (a n : Nat → UInt256)
    (rest : List UInt256) (k N x : Nat) where
  state : State
  output : Nat → UInt256
  trace : GasSteps {s with pc := UInt256.ofNat startPC,stack := frame inv a n (counter s::rest)} state
  memory : LimbMemory.Holds state.memory inv output zeroWords n
  frame : state.stack = frame inv output n (counter state::rest)
  pc : state.pc = if k = 1 then UInt256.ofNat exitPC else UInt256.ofNat startPC
  env : state.executionEnv = s.executionEnv
  halt : state.halt = s.halt
  active : state.activeWords = s.activeWords
  bounded : ∀ i < 9,(output i).toNat < radix
  small : value output + 2*N ≤ radix^9
  form : value output ≡ (x*x)*radix^9 [MOD N]
  counter : 1 < k → counter state = UInt256.ofNat ((k-1)-1)
  keepsBase : ∀ start count,256 ≤ start → start+count ≤ 768 →
    MachineState.readPadded state.memory start count = MachineState.readPadded s.memory start count
  calls : state.callStack = s.callStack
abbrev StepCertificate := ∀ (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (k N x : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : LimbMemory.Holds s.memory inv a zeroWords n)
    (hc : counter s = UInt256.ofNat (k-1))
    (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9,(a i).toNat < radix) (hn : ∀ i < 9,(n i).toNat < radix)
    (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N)
    (hN4 : 4*N ≤ radix^9) (hsmall : value a + 2*N ≤ radix^9)
    (hform : value a ≡ x*radix^9 [MOD N]),RoundOutcome startPC exitPC s inv a n rest k N x
noncomputable def run (step : StepCertificate startPC exitPC) (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (k N x : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : LimbMemory.Holds s.memory inv a zeroWords n)
    (hc : counter s = UInt256.ofNat (k-1))
    (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9,(a i).toNat < radix) (hn : ∀ i < 9,(n i).toNat < radix)
    (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N)
    (hN4 : 4*N ≤ radix^9) (hsmall : value a + 2*N ≤ radix^9)
    (hform : value a ≡ x*radix^9 [MOD N]) : Outcome startPC exitPC s inv a n rest k N x := by
  obtain ⟨st,out,ht,hmem,hstack,hpc,henv,hhalt,hactive,hbound,hsm,hnext,hcounter,hkeep,hcalls⟩ :=
    step s inv a n rest k N x hk hk16 env hm hc hcache hcap hact ha hn hn0 hNvalue hinv hN hNR hodd hN4 hsmall hform
  by_cases he : k = 1
  · subst k
    refine ⟨st,out,ht,hmem,hstack,?_,henv,hhalt,hactive,hbound,hsm,?_,hkeep,hcalls⟩
    · simpa only [ite_true] using hpc
    · simpa only [Nat.pow_one,Nat.pow_two] using hnext
  · have hmore : 1 < k := by omega
    have en : Environment Artifact.artifact .Osaka st := env.transfer henv hhalt
    have act : 88 ≤ st.activeWords.toNat := by rw [hactive]; exact hact
    obtain ⟨tstate,tout,ttrace,tmem,tframe,tpc,tenv,thalt,tact,tbound,tsm,tform,tkeep,tcalls⟩ :=
      run step st inv out n rest (k-1) N (x*x) (by omega) (by omega)
      en hmem (hcounter hmore) hcache hcap act hbound hn hn0 hNvalue hinv hN hNR hodd hN4 hsm hnext
    have hstart : {st with pc := UInt256.ofNat startPC,stack := frame inv out n (counter st::rest)} = st :=
      reset_self st _ _ (by simpa only [if_neg he] using hpc) hstack
    have htail : GasSteps st tstate := by
      have h := ttrace
      rw [hstart] at h
      exact h
    refine ⟨tstate,tout,ht.trans htail,tmem,tframe,tpc,
      tenv.trans henv,thalt.trans hhalt,tact.trans hactive,tbound,tsm,?_,?_,tcalls.trans hcalls⟩
    · have h := tform
      rw [next_exponent x k hk] at h
      exact h
    · intro start count hlo hhi
      exact (tkeep start count hlo hhi).trans (hkeep start count hlo hhi)
termination_by k
decreasing_by omega
#print axioms run
end CycleSubmission.PersistentSquareLoop
