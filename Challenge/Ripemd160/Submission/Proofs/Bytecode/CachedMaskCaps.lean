import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityStackEffect

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CavityStackEffect
open CachedMaskParams CachedMaskQuadGroup

theorem left_advances (group : Fin 5) :
    ∀ i ∈ leftCode group, PairMultiplyLift.Advances i :=
  four_advances (left group) 0

theorem right_advances :
    ∀ i ∈ rightCode, PairMultiplyLift.Advances i := four_advances right 5

theorem left0_total : total ((leftCode 0).take 399) = 0 := by decide
theorem left2_total : total ((leftCode 2).take 178) = 0 := by decide
theorem left2_middle_total : total (((leftCode 2).drop 178).take 210) = 1 := by decide
theorem left2_remaining_total : total ((leftCode 2).drop 178) = 0 := by decide
theorem right_total : total (rightCode.take 373) = 1 := by decide

theorem left_prefix_cap (group : Fin 5) (cut : Nat)
    (htotal : total ((leftCode group).take cut) = 0)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) :
    ∀ middle, runInstrSeq ((leftCode group).take cut)
      (stateAt s pc w (mask :: rho)) = some middle → middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances group i (List.mem_of_mem_take hi)
  · rw [htotal]
    simp only [stateAt, roundEntry, List.length_append, List.length_cons, List.length_nil]
    omega

theorem left2_middle_cap (s : State) (hstack : s.stack.length < 1022) :
    ∀ middle, runInstrSeq (((leftCode 2).drop 178).take 210) s = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances 2 i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
  · rw [left2_middle_total]
    omega

theorem right_prefix_cap (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256) (hstack : rho.length < 1001) :
    ∀ middle, runInstrSeq (rightCode.take 373)
      (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho)) = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact right_advances i (List.mem_of_mem_take hi)
  · rw [right_total]
    simp only [stateAt, roundEntry, List.length_append, List.length_cons, List.length_nil]
    omega

#print axioms left_prefix_cap
#print axioms left2_middle_cap
#print axioms right_prefix_cap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
