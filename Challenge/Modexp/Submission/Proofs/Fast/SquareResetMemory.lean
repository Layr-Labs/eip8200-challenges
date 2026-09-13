import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareResetMemory
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult CarryRowModel

/-- The unused carry scratch word is already zero between actual square rounds. -/
def ZeroScratch (mem : ByteArray) : Prop :=
  ∀ i, 2048 ≤ i → i < 2080 → mem[i]?.getD 0 = 0

theorem zeroScratch_write (mem bytes : ByteArray) (dst : Nat)
    (h : ZeroScratch mem) (hd : dst + bytes.size ≤ 2048 ∨ 2080 ≤ dst) :
    ZeroScratch (MachineState.writeBytes mem bytes dst) := by
  intro i hlo hhi
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]
  exact h i hlo hhi

theorem zeroScratch_mpZeroed (s : EVM.State) (mem : ByteArray) (n : Nat) :
    ZeroScratch (mpZeroed s mem n) := by
  intro i hlo hhi
  rw [mpZeroed, MachineState.writeBytes_getElem?_getD,
    Challenge.EvmProof.Memory.readPadded_size, if_pos (by omega),
    Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
  exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega)

theorem zeroScratch_l1Run (q : MacState) (bi : UInt256) (pa n j k : Nat)
    (h : ZeroScratch q.memory) : ZeroScratch (l1Run q bi pa n j k).memory := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [l1Run, l1StepOn]
    exact zeroScratch_write _ _ _ ih (Or.inr (by omega))

theorem zeroScratch_sqL1 (mem : ByteArray) (n i : Nat) (tb : UInt256)
    (h : ZeroScratch mem) : ZeroScratch (sqL1 mem n i tb).memory := by
  apply zeroScratch_l1Run
  unfold sqPro
  exact zeroScratch_write _ _ _ h (Or.inr (by unfold tAddr; omega))

theorem zeroScratch_l2Step (mem : ByteArray) (mu c0 : UInt256) (n k : Nat)
    (h : ZeroScratch mem) : ZeroScratch (l2Step mem mu c0 n k).memory := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [l2Step]
    exact zeroScratch_write _ _ _ ih (Or.inr (by omega))

theorem zeroScratch_rowFromCarry (q : MacState) (n : Nat) (h : ZeroScratch q.memory) :
    ZeroScratch (rowFromCarry q n) := by
  unfold rowFromCarry tailCarry tailMem1
  apply zeroScratch_write _ _ _ _ (Or.inr (by decide))
  apply zeroScratch_write _ _ _ _ (Or.inr (by decide))
  unfold rowFromL2Carry
  apply zeroScratch_l2Step
  unfold midMem1
  exact zeroScratch_write _ _ _ h (Or.inr (by decide))

theorem zeroScratch_sqRowsCarry (mem : ByteArray) (n k : Nat) (h : ZeroScratch mem) :
    ZeroScratch (sqRowsCarry mem n k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    unfold sqRowsCarry sqRowCarry
    exact zeroScratch_rowFromCarry _ n (zeroScratch_sqL1 _ n k _ ih)

theorem zeroScratch_csStep (mem : ByteArray) (n k : Nat) (hn : n ≤ 8)
    (h : ZeroScratch mem) : ZeroScratch (Csub.csStep mem n k).memory := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [Csub.csStep]
    apply zeroScratch_write _ _ _ ih (Or.inl ?_)
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega

theorem zeroScratch_csub (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (h : ZeroScratch mem) : ZeroScratch (Csub.csResultMemory mem n 2368) := by
  unfold Csub.csResultMemory
  split
  · exact zeroScratch_write _ _ _ h (Or.inr (by decide))
  · unfold Csub.subResultMemory
    exact zeroScratch_write _ _ _ (zeroScratch_csStep _ n n hn h) (Or.inr (by decide))

theorem zeroScratch_sqRound (s : EVM.State) (mem : ByteArray) (n c : Nat) (hn : n ≤ 8) :
    ZeroScratch (SquareLoopMem.sqRound s n c mem) := by
  unfold SquareLoopMem.sqRound SquareLoopMem.roundDst
  apply zeroScratch_csub _ n hn
  unfold SquareLoopBlocks.countMem
  exact zeroScratch_write _ _ _
    (zeroScratch_sqRowsCarry _ n n (zeroScratch_mpZeroed s mem n)) (Or.inr (by decide))

/-- Leaving the already zero scratch word untouched gives the exact same memory. -/
theorem mpZeroed_eq_trim (s : EVM.State) (mem : ByteArray) (n : Nat) (h : ZeroScratch mem) :
    mpZeroed s mem n =
      MachineState.writeBytes mem
        (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
          (32 + 32 * n)) 2080 := by
  apply ByteArray.ext_getElem
  · simp only [mpZeroed, MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size]
    rw [if_neg (show 64 + 32 * n ≠ 0 by omega),
      if_neg (show 32 + 32 * n ≠ 0 by omega)]
    congr 1
    omega
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    simp only [mpZeroed, MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size]
    by_cases hleft : 2048 ≤ i ∧ i < 2048 + (64 + 32 * n)
    · rw [if_pos hleft]
      rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega),
        Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega)]
      by_cases hright : 2080 ≤ i ∧ i < 2080 + (32 + 32 * n)
      · rw [if_pos hright, Challenge.EvmProof.Memory.readPadded_getElem?_getD,
          if_pos (by omega), Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega)]
      · rw [if_neg hright]
        exact (h i (by omega) (by omega)).symm
    · rw [if_neg hleft, if_neg (by omega)]

#print axioms zeroScratch_sqRound
#print axioms mpZeroed_eq_trim
end Challenge.Modexp.Submission.Proofs.Fast.SquareResetMemory
