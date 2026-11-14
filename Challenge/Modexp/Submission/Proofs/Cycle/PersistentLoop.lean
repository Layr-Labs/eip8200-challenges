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
abbrev counter := CachedInverse.publicCounter
structure Outcome (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (count N x : Nat) where
 state : State
 output : Nat → UInt256
 trace : GasSteps {s with pc := UInt256.ofNat 3476,stack := CachedInverse.entryFrame inv a zeroWords n (counter s::rest)} state
 memory : SquareMeaning.Memory0 state.memory inv output zeroWords n
 frame : state.stack = SquareMeaning.frame0 inv output zeroWords n (counter state::rest)
 pc : state.pc = UInt256.ofNat 5825
 env : state.executionEnv = s.executionEnv
 halt : state.halt = s.halt
 active : state.activeWords = s.activeWords
 bounded : ∀ i < 9,(output i).toNat < radix
 small : value output+2*N ≤ radix^9
 form : value output ≡ x^(2^count)*radix^9 [MOD N]
 keepsBase : ∀ start count,256 ≤ start → start+count ≤ 768 →
  MachineState.readPadded state.memory start count = MachineState.readPadded s.memory start count
 calls : state.callStack = s.callStack
theorem installed_counter (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
 PersistentSquareLoop.counter (PersistentBinding.installed s inv a n rest) = UInt256.ofNat 0-counter s := by rfl
attribute [local irreducible] CycleSubmission.LimbMemory.store CycleSubmission.PersistentBinding.installed
noncomputable opaque run (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (k N x : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
 (env : Environment Artifact.artifact .Osaka s)
 (hm : SquareMeaning.Memory0 s.memory inv a zeroWords n)
 (hc : counter s = UInt256.ofNat (k-1))
 (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (ha : ∀ i < 9,(a i).toNat < radix) (hn : ∀ i < 9,(n i).toNat < radix)
 (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
 (hinv : (N*inv.toNat+1) % 2^256 = 0)
 (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N)
 (hN4 : 4*N ≤ radix^9) (hsmall : value a+2*N ≤ radix^9)
 (hform : value a ≡ x*radix^9 [MOD N]) : Outcome s inv a n rest k N x := by
 let si := PersistentBinding.installed s inv a n rest
 have ei : Environment Artifact.artifact .Osaka si := env.transfer (by simp only [si,PersistentBinding.installed]) (by simp only [si,PersistentBinding.installed])
 have hmi : LimbMemory.Holds si.memory inv a zeroWords n :=
  by simpa only [si,PersistentBinding.installed] using LimbMemory.install s.memory inv a zeroWords n hm
 have hci : PersistentSquareLoop.counter si = UInt256.ofNat 0-UInt256.ofNat (k-1) := by
  change PersistentSquareLoop.counter (PersistentBinding.installed s inv a n rest) = _
  rw [installed_counter,hc]
 have hacti : 88 ≤ si.activeWords.toNat := by simpa only [si,PersistentBinding.installed] using hact
 obtain ⟨st,out,ht0,hmOut,hsOut,hpOut,heOut,hhOut,haOut,hboundOut,hsmOut,hfmOut,hkeepOut,hcallsOut⟩ := PersistentSquareLoop.run 3487 5807 PersistentRound.certificate si inv a n rest k N x
  hk hk16 ei hmi hci hcache hcap hacti ha hn hn0 hNvalue hinv hN hNR hodd hN4 hsmall hform
 have hstart : {si with pc := UInt256.ofNat 3487,stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter si::rest)} = si := by
  apply PersistentSquareLoop.reset_self
  · simp only [si,PersistentBinding.installed]
  · rw [show PersistentSquareLoop.counter si = UInt256.ofNat 0-counter s from installed_counter s inv a n rest]
    simp only [si,PersistentBinding.installed]
 have ht := ht0
 rw [hstart] at ht
 have eout : Environment Artifact.artifact .Osaka st := ei.transfer heOut hhOut
 have hactout : 88 ≤ st.activeWords.toNat := by rw [haOut]; exact hacti
 have hr := PersistentBinding.restore_steps st inv out n rest eout hcap hactout hcache hmOut.at2720
 have hrestore : {st with pc := UInt256.ofNat 5807,stack := PersistentSquareLoop.frame inv out n (PersistentSquareLoop.counter st::rest)} = st :=
  PersistentSquareLoop.reset_self _ _ _ hpOut hsOut
 rw [hrestore] at hr
 let sf : State := {st with pc := UInt256.ofNat 5825,memory := LimbMemory.store st.memory 96 (out 5),stack := SquareMeaning.frame0 inv out zeroWords n (PersistentSquareLoop.counter st::rest)}
 have hcounter : counter sf = PersistentSquareLoop.counter st := by rfl
 refine ⟨sf,out,(PersistentBinding.install_steps s inv a n rest env hm hcache hcap hact).trans (ht.trans hr),
  LimbMemory.flush st.memory inv out zeroWords n hmOut,?_,rfl,
  (by simpa only [sf,si,PersistentBinding.installed] using heOut),
  (by simpa only [sf,si,PersistentBinding.installed] using hhOut),
  (by simpa only [sf,si,PersistentBinding.installed] using haOut),hboundOut,hsmOut,hfmOut,?_,
  (by simpa only [sf,si,PersistentBinding.installed] using hcallsOut)⟩
 · change SquareMeaning.frame0 inv out zeroWords n (PersistentSquareLoop.counter st::rest) = _
   rw [hcounter]
 · intro start count hlo hhi
   change MachineState.readPadded (LimbMemory.store st.memory 96 (out 5)) start count = _
   exact (LimbMemory.store_keeps_base st.memory 96 (out 5) start count hlo hhi (Or.inl (by decide))).trans
    (by simpa only [si,PersistentBinding.installed] using hkeepOut start count hlo hhi)
#print axioms run
end CycleSubmission.PersistentLoop
