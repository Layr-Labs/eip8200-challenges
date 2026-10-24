import Challenge.Modexp.Submission.Proofs.CRT.LoopInvariant
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 500000

namespace HistoricalSearch.CRTLoopInduction
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.LoopInvariant HistoricalSearch.PureLoop

variable (s : State) (minv : UInt256) (n : Nat → UInt256)

def nextFrame (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) : CRTLoopFrames.Frame :=
  if Q s minv n mem < R then f
  else {f with aprev := CRTAdapterMeaning.cachedTop (checked s minv n mem), counter := UInt256.ofNat (k-1)}

theorem nextFrame_rest (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) :
    (nextFrame s minv n k mem f).rest = f.rest := by
  unfold nextFrame
  split <;> rfl

theorem nextFrame_invariant (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) (N A : Nat)
    (h : Invariant (next s minv n k mem) n minv f N k A) :
    Invariant (next s minv n k mem) n minv (nextFrame s minv n k mem f) N k A := by
  unfold nextFrame
  split
  · exact h
  · exact { toStatic := h.toStatic.flow _ _ f.ret f.rest,
            operand := h.operand, counter := h.counter,
            countPositive := h.countPositive, countBound := h.countBound }

def finished (mem : ByteArray) (f : CRTLoopFrames.Frame) : State :=
  {s with pc := UInt256.ofNat 690, stack := f.rest, memory := StagedProduct.memory s mem 8}

/-- The two remaining concrete execution obligations. Both are GasSteps on the
installed bytecode, not assumptions of arithmetic correctness or test success. -/
structure Operations (N : Nat) where
  advance : ∀ (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat),
    1 ≤ k → f.rest.length ≤ 982 → Invariant mem n minv f N (k+1) A →
    Challenge.EvmProof.GasSteps (atCache s mem 5859 n minv f)
      (atCache s (next s minv n k mem) 5859 n minv (nextFrame s minv n k mem f))
  last : ∀ (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat),
    f.rest.length ≤ 982 → Invariant mem n minv f N 1 A →
    Challenge.EvmProof.GasSteps (atCache s mem 5859 n minv f)
      (finished s (finish s minv n mem) f)

/-- Actual direct and overflow-reentry rounds compose for every allowed
counter, keeping the saved stack counter separate from mutable memory1728. -/
noncomputable def run (N : Nat) (ops : Operations s minv n N)
    (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat)
    (hcap : f.rest.length ≤ 982) (h : Invariant mem n minv f N k A) :
    Challenge.EvmProof.GasSteps (atCache s mem 5859 n minv f)
      (finished s (memory s minv n k mem) f) := by
  induction k generalizing mem f A with
  | zero => have := h.countPositive; omega
  | succ k ih =>
    by_cases hk : k=0
    · subst k
      simpa only [memory, ↓reduceIte] using ops.last mem f A hcap h
    · have hkpos : 1 ≤ k := by omega
      let hr := round_invariant s minv n mem f N k A hkpos h
      let v := Classical.choose hr
      have hv := (Classical.choose_spec hr).1
      have hn := nextFrame_invariant s minv n k mem f N v hv
      have g1 := ops.advance k mem f A hkpos hcap h
      have g2 := ih (next s minv n k mem) (nextFrame s minv n k mem f) v
        (by rw [nextFrame_rest]; exact hcap) hn
      have g := g1.trans g2
      simpa only [memory, if_neg hk, finished, nextFrame_rest] using g

#print axioms nextFrame_invariant
#print axioms run
end HistoricalSearch.CRTLoopInduction
