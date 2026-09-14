import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Frame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2End
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open J2Frame RecognitionAccumulator

private theorem widths_after_closed (n : Nat) (hn : Allowed n) :
    ∀ k : Fin 32, last n < k.val → J2Accumulator.width n k.val = 0 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem piece_after (input : ByteArray) (n k : Nat) (hn : Allowed n)
    (hl : last n < k) (hk : k<32) : J2Accumulator.piece input n k = 0 := by
  have hw := widths_after_closed n hn ⟨k,hk⟩ hl
  unfold J2Accumulator.piece J2Accumulator.shift
  rw [hw]
  rfl

private theorem zero_or (x : UInt256) : UInt256.lor 0 x = x := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_lor]
  exact BitVec.zero_or

theorem accumulate_after (input : ByteArray) (n m : Nat) (hn : Allowed n)
    (hl : last n+1≤m) (hm : m≤32) :
    J2Accumulator.accumulate input n m = J2Accumulator.accumulate input n (last n+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases he : m=last n
    · rw [he]
    · have hle : last n+1≤m := by omega
      rw [J2Accumulator.accumulate, piece_after input n m hn (by omega) (by omega), zero_or]
      exact ih hle (by omega)

def endFrame (s : State) (n : Nat) : J2Raw.Frame :=
  J2Raw.tailResult s (current s.executionEnv.calldata n (last n))

theorem end_acc (s : State) (n : Nat) (hn : Allowed n) :
    (endFrame s n).acc = J2Accumulator.resultAcc s.executionEnv.calldata n := by
  rw [endFrame, tail_acc s n (last n) hn (by omega) (Or.inl rfl)]
  exact (accumulate_after s.executionEnv.calldata n 32 hn (by have := last_lt n hn; omega) (by omega)).symm

#print axioms accumulate_after
#print axioms end_acc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2End
