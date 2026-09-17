import Challenge.Modexp.Submission.LocalPatch.PointerStates

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Transport

/-- Closed candidate execution: PUSH2 32; DUP2; SUB; SWAP1.
The required peak is the old macro's peak, obtained at its second actual step.
The source endpoint's gas field is deliberately arbitrary to GasSteps. -/
def candidateTrace {code : ByteArray} (new : NewCode code)
    (a : State) (p : UInt256) (tail : List UInt256) (counter : Nat)
    (hpc : a.pc = UInt256.ofNat 2539) (hstack : a.stack = p :: tail)
    (hrun : a.halt = .Running) (hf : a.fork = .Osaka)
    (hnp : NonPrecompile a) (hcap : tail.length + 2 < 1024) :
    GasSteps (liftState code 0 counter a)
      (liftState code 0 counter (pre a p tail 5)) := by
  refine ⟨12, ?_⟩
  intro gas hgas
  let q0 := withGas (liftState code 0 counter a) gas
  let q1 : State :=
    { q0 with
        pc := UInt256.ofNat 2542
        stack := UInt256.ofNat 32 :: p :: tail
        gasAvailable := gas - 3 }
  let q2 : State :=
    { q1 with
        pc := UInt256.ofNat 2543
        stack := p :: UInt256.ofNat 32 :: p :: tail
        gasAvailable := gas - 6 }
  let q3 : State :=
    { q2 with
        pc := UInt256.ofNat 2544
        stack := (p - UInt256.ofNat 32) :: p :: tail
        gasAvailable := gas - 9 }
  let q4 : State :=
    { q3 with
        pc := UInt256.ofNat 2545
        stack := p :: (p - UInt256.ofNat 32) :: tail
        gasAvailable := gas - 12 }
  have hp0 : q0.pc.toNat = 2539 := by dsimp [q0, withGas, liftState]; rw [hpc]; rfl
  have hd0 := decoded_at (s := q0) rfl hf hp0 new.d0 (by decide)
  have hd1 := decodedOp_at (s := q1) rfl hf (show q1.pc.toNat = 2542 from rfl)
    new.d1 (by decide)
  have hd2 := decodedOp_at (s := q2) rfl hf (show q2.pc.toNat = 2543 from rfl)
    new.d2 (by decide)
  have hd3 := decodedOp_at (s := q3) rfl hf (show q3.pc.toNat = 2544 from rfl)
    new.d3 (by decide)
  have g1 : 3 ≤ q0.gasAvailable := by change 3 ≤ gas; omega
  have g2 : 3 ≤ q1.gasAvailable := by change 3 ≤ gas - 3; omega
  have g3 : 3 ≤ q2.gasAvailable := by change 3 ≤ gas - 6; omega
  have g4 : 3 ≤ q3.gasAvailable := by change 3 ≤ gas - 9; omega
  have sub6 : gas - 3 - 3 = gas - 6 := by omega
  have sub9 : gas - 6 - 3 = gas - 9 := by omega
  have sub12 : gas - 9 - 3 = gas - 12 := by omega
  have q0gas : q0.gasAvailable = gas := by rfl
  have q1gas : q1.gasAvailable = gas - 3 := by rfl
  have q2gas : q2.gasAvailable = gas - 6 := by rfl
  have q3gas : q3.gasAvailable = gas - 9 := by rfl
  have cost0 : Gas.baseCost q0.fork (.Push ⟨2, by decide⟩) = 3 := by rfl
  have cost1 : Gas.baseCost q1.fork (.Dup ⟨1, by decide⟩) = 3 := by rfl
  have cost2 : Gas.baseCost q2.fork .SUB = 3 := by rfl
  have cost3 : Gas.baseCost q3.fork (.Swap ⟨0, by decide⟩) = 3 := by rfl
  have q0pc : q0.pc = UInt256.ofNat 2539 := by
    simpa only [q0, withGas, liftState] using hpc
  have q0stack : q0.stack = p :: tail := by
    simpa only [q0, withGas, liftState] using hstack
  have pc1 : q0.pc + UInt256.ofNat (2 + 1) = UInt256.ofNat 2542 := by
    rw [q0pc]
    decide
  have pc2 : q1.pc.succ = UInt256.ofNat 2543 := by
    change (UInt256.ofNat 2542).succ = UInt256.ofNat 2543
    decide
  have pc3 : q2.pc.succ = UInt256.ofNat 2544 := by
    change (UInt256.ofNat 2543).succ = UInt256.ofNat 2544
    decide
  have pc4 : q3.pc.succ = UInt256.ofNat 2545 := by
    change (UInt256.ofNat 2544).succ = UInt256.ofNat 2545
    decide
  have hrun0 : q0.halt = .Running := by
    simpa only [q0, withGas, liftState] using hrun
  have hnp0 : NonPrecompile q0 := by
    simpa only [NonPrecompile, q0, withGas, liftState] using hnp
  have hrun1 : q1.halt = .Running := by
    simpa only [q1] using hrun0
  have hnp1 : NonPrecompile q1 := by
    simpa only [NonPrecompile, q1] using hnp0
  have hrun2 : q2.halt = .Running := by
    simpa only [q2] using hrun1
  have hnp2 : NonPrecompile q2 := by
    simpa only [NonPrecompile, q2] using hnp1
  have hrun3 : q3.halt = .Running := by
    simpa only [q3] using hrun2
  have hnp3 : NonPrecompile q3 := by
    simpa only [NonPrecompile, q3] using hnp2
  have run1 : Step q0 q1 := by
    apply Step.running hrun0 hnp0
    have h := StepRunning.pushN q0 ⟨2, by decide⟩ (UInt256.ofNat 32) 2
      (by decide) hd0 g1 (by
        change a.stack.length < 1024
        rw [hstack]
        simp only [List.length_cons]
        omega)
    simpa only [q1, q0gas, q0stack, cost0, pc1] using h
  have run2 : Step q1 q2 := by
    apply Step.running hrun1 hnp1
    have h := StepRunning.dup q1 ⟨1, by decide⟩ p hd1 g2 rfl
      (by simpa only [q1, List.length_cons, Nat.add_assoc] using hcap)
    simpa only [q2, q1gas, cost1, sub6, pc2] using h
  have run3 : Step q2 q3 := by
    apply Step.running hrun2 hnp2
    have h := StepRunning.sub q2 p (UInt256.ofNat 32) (p :: tail) hd2 g3 rfl
      (by simp [q2, Operation.pushArity, Operation.popArity]; omega)
    simpa only [q3, q2gas, cost2, sub9, pc3] using h
  have run4 : Step q3 q4 := by
    apply Step.running hrun3 hnp3
    have h := StepRunning.swap q3 ⟨0, by decide⟩
      (p :: (p - UInt256.ofNat 32) :: tail) hd3 g4
      (by simp [q3, List.exchange])
      (by simp [q3, Operation.pushArity, Operation.popArity]; omega)
    simpa only [q4, q3gas, cost3, sub12, pc4] using h
  have hend : withGas (liftState code 0 counter (pre a p tail 5)) (gas - 12) = q4 := by
    simp only [q4, q3, q2, q1, q0, withGas, liftState, pre, negative32_add]
  rw [hend]
  exact Steps.trans run1 (Steps.trans run2 (Steps.trans run3 (Steps.trans run4 (Steps.refl _))))

@[simp] theorem candidateTrace_cost {code : ByteArray} (new : NewCode code)
    (a : State) (p : UInt256) (tail : List UInt256) (counter : Nat)
    (hpc : a.pc = UInt256.ofNat 2539) (hstack : a.stack = p :: tail)
    (hrun : a.halt = .Running) (hf : a.fork = .Osaka)
    (hnp : NonPrecompile a) (hcap : tail.length + 2 < 1024) :
    (candidateTrace new a p tail counter hpc hstack hrun hf hnp hcap).cost = 12 := rfl

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
