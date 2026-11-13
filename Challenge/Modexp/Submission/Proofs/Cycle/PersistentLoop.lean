import Challenge.Modexp.Submission.Proofs.Cycle.PersistentRound
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000
namespace CycleSubmission.PersistentLoop
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.WordArithmetic
open CycleSubmission.ControlArithmetic (value)
open CycleSubmission.SquareStep (zeroWords)
abbrev counter := PersistentSquareLoop.counter

structure Outcome (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (count N x : Nat) where
 state : State
 output : Nat → UInt256
 trace : GasSteps {s with pc := UInt256.ofNat 5391, stack := SquareMeaning.frame0 inv a zeroWords n (counter s :: rest)} state
 memory : SquareMeaning.Memory0 state.memory inv output zeroWords n
 frame : state.stack = SquareMeaning.frame0 inv output zeroWords n (counter state :: rest)
 pc : state.pc = UInt256.ofNat 7732
 env : state.executionEnv = s.executionEnv
 halt : state.halt = s.halt
 active : state.activeWords = s.activeWords
 bounded : ∀ i < 9, (output i).toNat < radix
 small : value output+2*N ≤ radix^9
 form : value output ≡ x^(2^count)*radix^9 [MOD N]
 keepsBase : ∀ start count, 256 ≤ start → start+count ≤ 768 →
  MachineState.readPadded state.memory start count = MachineState.readPadded s.memory start count
 calls : state.callStack = s.callStack

theorem installed_counter (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
 counter (PersistentBinding.installed s inv a n rest) = counter s := by rfl

noncomputable def run (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (k N x : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
 (env : Environment Artifact.artifact .Osaka s)
 (hm : SquareMeaning.Memory0 s.memory inv a zeroWords n)
 (hc : counter s = UInt256.ofNat (k-1))
 (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (ha : ∀ i < 9, (a i).toNat < radix) (hn : ∀ i < 9, (n i).toNat < radix)
 (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
 (hinv : (N*inv.toNat+1) % 2^256 = 0)
 (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N)
 (hN4 : 4*N ≤ radix^9) (hsmall : value a+2*N ≤ radix^9)
 (hform : value a ≡ x*radix^9 [MOD N]) : Outcome s inv a n rest k N x := by
 let si := PersistentBinding.installed s inv a n rest
 have ei : Environment Artifact.artifact .Osaka si := env.transfer rfl rfl
 have hci : PersistentSquareLoop.counter si = UInt256.ofNat (k-1) := by
  change counter (PersistentBinding.installed s inv a n rest) = _
  rw [installed_counter]
  exact hc
 let loop := PersistentSquareLoop.run 5394 7723 PersistentRound.certificate si inv a n rest k N x
  hk hk16 ei hm hci hcache hcap hact ha hn hn0 hNvalue hinv hN hNR hodd hN4 hsmall hform
 have hstart : {si with pc := UInt256.ofNat 5394, stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter si :: rest)} = si := by
  apply PersistentSquareLoop.reset_self
  · rfl
  · rfl
 have ht := loop.trace
 rw [hstart] at ht
 have eout : Environment Artifact.artifact .Osaka loop.state := ei.transfer loop.env loop.halt
 have hr := PersistentBinding.restore_steps loop.state inv loop.output n rest eout hcap
 have hrestore : {loop.state with pc := UInt256.ofNat 7723, stack := PersistentSquareLoop.frame inv loop.output n (counter loop.state :: rest)} = loop.state :=
  PersistentSquareLoop.reset_self _ _ _ loop.pc loop.frame
 rw [hrestore] at hr
 let sf : State := {loop.state with pc := UInt256.ofNat 7732, stack := SquareMeaning.frame0 inv loop.output zeroWords n (counter loop.state :: rest)}
 have hcounter : counter sf = counter loop.state := by rfl
 refine ⟨sf,loop.output,(PersistentBinding.install_steps s inv a n rest env hcache hcap).trans (ht.trans hr),
  loop.memory,?_,rfl,loop.env,loop.halt,loop.active,loop.bounded,loop.small,loop.form,loop.keepsBase,loop.calls⟩
 change SquareMeaning.frame0 inv loop.output zeroWords n (counter loop.state :: rest) = _
 rw [hcounter]

#print axioms run
end CycleSubmission.PersistentLoop
