import Challenge.Modexp.Submission.Proofs.Cycle.EntryContract
import Challenge.Modexp.Submission.Proofs.Cycle.UnpackBinding
import Challenge.Modexp.Submission.Proofs.Cycle.Finish
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.Core
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Model
open CycleSubmission.EntryMeaning CycleSubmission.InputWords CycleSubmission.WordArithmetic
open CycleSubmission.ControlArithmetic (value)
noncomputable def run (s : State) (f : Caller) (k N A B x : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcache : f.pbi = MachineState.readWord s.memory 2720)
    (hcounter : f.counter = UInt256.ofNat (k-1))
    (hn : FastRepresents s.memory 0 8 N) (ha : FastRepresents s.memory 2368 8 A)
    (hb : FastRepresents s.memory 256 8 B)
    (hinv : (N*(MachineState.readWord s.memory 2720).toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hform : A ≡ x*2^2048 [MOD N]) (hAtop : A < 2^2048 - 2^1938) :
    Finish.Outcome {s with pc := UInt256.ofNat 3318,stack := saved f}
      (Precompile.natToBytes (B*x^(2^k)%N) 256) := by
  have cap : (saved f).length ≤ 959 := by
    simp only [saved,List.length_cons,List.length_append,List.length_nil]
    omega
  have hNsize : N < 2^2048 := hn.1
  have hNR : N < radix^9 := Nat.lt_trans hNsize (by norm_num [radix])
  have hNK : N < 2^2048 := hn.1
  have hN4 : 4*N ≤ radix^9 := by
    have e : radix^9 = 2^2048 * 2^112 := by rw [radix,← Nat.pow_mul,← Nat.pow_add]
    rw [e]
    generalize (2:Nat)^2048 = K at hNK ⊢
    have h4 : (4:Nat) ≤ 2^112 := by norm_num
    calc 4*N ≤ 2^112 * N := Nat.mul_le_mul_right _ h4
      _ ≤ 2^112 * K := Nat.mul_le_mul_left _ (Nat.le_of_lt hNK)
      _ = K * 2^112 := Nat.mul_comm _ _
  have hsmallA : A*2^112 + 2*N ≤ radix^9 := by
    have e1 : (2:Nat)^2048 = 2^1938 * 2^110 := by rw [← Nat.pow_add]
    have e2 : radix^9 = 2^1938 * 2^222 := by rw [radix,← Nat.pow_mul,← Nat.pow_add]
    rw [e2]
    rw [e1] at hAtop hNK
    generalize (2:Nat)^1938 = K at hAtop hNK ⊢
    have h1 : A + K + 1 ≤ K * 2^110 := by omega
    have h2 : (A + K + 1) * 2^112 ≤ K * 2^110 * 2^112 := Nat.mul_le_mul_right _ h1
    have h3 : K * 2^110 * 2^112 = K * 2^222 := by rw [Nat.mul_assoc,← Nat.pow_add]
    have h4 : 2 * N ≤ (K + 1) * 2^112 := by
      have : 2 * (K * 2^110) ≤ (K+1) * 2^112 := by
        have h5 : (2:Nat)^112 = 2 * 2^110 * 2 := by norm_num
        rw [h5]; nlinarith
      omega
    have h6 : (A + K + 1) * 2^112 = A * 2^112 + (K + 1) * 2^112 := by ring
    omega
  obtain ⟨start,inv,invEq,a,n,enter,frame,pc,memory,en,halt,active,
    counter,aBound,nBound,n0,nValue,inverse,base,form,callsStart,small⟩ :=
    EntryContract.prepare s f k N A B x env hcap hact hcounter hn ha hb hinv hform hsmallA
  have envStart := env.transfer en halt
  have actStart : 88 ≤ start.activeWords.toNat := by rw [active]; exact hact
  obtain ⟨last,out,rounds,lastMem,lastFrame,lastPc,lastEnv,lastHalt,
    lastActive,lastBound,lastSmall,lastForm,keepsBase,callsLast⟩ :=
    PersistentLoop.run start inv a n (saved f) k N x hk hk16 envStart memory counter (by simpa [saved] using congrArg some (hcache.trans invEq.symm)) cap actStart
      aBound nBound n0 nValue inverse hN hNR hodd hN4 small form
  have counterStart : PersistentLoop.entryCounter start = UInt256.ofNat 0-f.counter := counter.trans (congrArg (fun word => UInt256.ofNat 0-word) hcounter.symm)
  have startReset : {start with pc := UInt256.ofNat 3476,stack := CachedInverse.entryFrame inv a SquareStep.zeroWords n (PersistentLoop.entryCounter start::saved f)} = start :=
    PersistentSquareLoop.reset_self _ _ _ pc (by rw [counterStart]; exact frame)
  rw [startReset] at rounds
  have baseLast : FastRepresents last.memory 256 8 B := by
    apply (fastRepresents_congr (a := last.memory) (b := start.memory) ?_ B).mpr base
    intro j hj
    unfold MachineState.readWord
    rw [keepsBase (256+32*j) 32 (by omega) (by omega)]
  have envLast := envStart.transfer lastEnv lastHalt
  have actLast : 88 ≤ last.activeWords.toNat := by rw [lastActive]; exact actStart
  have factor := ordinary_represents baseLast
  have hfactor : value (ordinary last.memory 256) = B := factor.2
  have capFinal : (PersistentLoop.counter last::saved f).length ≤ 960 := by
    simp only [List.length_cons]; omega
  have unpack := Unpack.gasSteps last inv out n (PersistentLoop.counter last::saved f) envLast capFinal actLast
  have lastReset : {last with pc := UInt256.ofNat 5815,stack := SquareMeaning.frame0 inv out SquareStep.zeroWords n (PersistentLoop.counter last::saved f)} = last :=
    PersistentSquareLoop.reset_self _ _ _ lastPc lastFrame
  change GasSteps {last with pc := UInt256.ofNat 5815,stack := SquareMeaning.frame0 inv out SquareStep.zeroWords n (PersistentLoop.counter last::saved f)} (Unpack.result last inv out n (PersistentLoop.counter last::saved f)) at unpack
  rw [lastReset] at unpack
  obtain ⟨done,finish,returned,bytes,callsDone⟩ := Finish.product (Unpack.result last inv out n (PersistentLoop.counter last::saved f))
    inv out (ordinary last.memory 256) n (PersistentLoop.counter last::saved f) (envLast.transfer rfl rfl)
    (Unpack.memory_output last inv out n (PersistentLoop.counter last::saved f) lastMem) capFinal actLast
    lastBound factor.1 nBound N (x^(2^k)) n0 nValue inverse hN hNsize hodd
    (by rw [hfactor]; exact hB) lastForm
  have unpackReset : {Unpack.result last inv out n (PersistentLoop.counter last::saved f) with
      pc := UInt256.ofNat 5906
      stack := ProductMeaning.frame0 inv out (ordinary last.memory 256) n (PersistentLoop.counter last::saved f)} =
      Unpack.result last inv out n (PersistentLoop.counter last::saved f) := PersistentSquareLoop.reset_self _ _ _ rfl rfl
  rw [unpackReset] at finish
  refine ⟨done,enter.trans (rounds.trans (unpack.trans finish)),returned,?_,callsDone.trans (callsLast.trans callsStart)⟩
  rw [hfactor] at bytes
  exact bytes
theorem correct_from_entry (s : State) (f : Caller) (k N A B x : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcache : f.pbi = MachineState.readWord s.memory 2720)
    (hcounter : f.counter = UInt256.ofNat (k-1))
    (hn : FastRepresents s.memory 0 8 N) (ha : FastRepresents s.memory 2368 8 A)
    (hb : FastRepresents s.memory 256 8 B)
    (hinv : (N*(MachineState.readWord s.memory 2720).toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hform : A ≡ x*2^2048 [MOD N]) (hAtop : A < 2^2048 - 2^1938)
    (hstack : s.callStack = []) :
    ∃ gas0,∀ gas,gas0 ≤ gas →
      Eval (withGas {s with pc := UInt256.ofNat 3318,stack := saved f} gas)
        (.returned (Precompile.natToBytes (B*x^(2^k)%N) 256)) :=
  (run s f k N A B x hk hk16 env hcap hact hcache hcounter hn ha hb hinv hN hodd hB hform hAtop).eventually hstack
end CycleSubmission.Core
