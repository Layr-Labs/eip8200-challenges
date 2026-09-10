import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineCaps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CavityStackEffect
open CachedMaskParams CachedMaskQuadGroup CachedMaskCaps

theorem first_total : total ((leftCode 4).take 213) = 1 := by decide
theorem second_total : total (((leftCode 4).drop 213).take 97) = 0 := by decide
theorem third_total : total (((leftCode 4).drop 310).take 54) = -1 := by decide

theorem second_split :
    ((leftCode 4).drop 213).take 97 ++ (leftCode 4).drop 310 =
      (leftCode 4).drop 213 := by
  rw [show (leftCode 4).drop 310 = ((leftCode 4).drop 213).drop 97 by
    rw [List.drop_drop]]
  exact List.take_append_drop 97 ((leftCode 4).drop 213)

theorem third_split :
    ((leftCode 4).drop 310).take 54 ++ (leftCode 4).drop 364 =
      (leftCode 4).drop 310 := by
  rw [show (leftCode 4).drop 364 = ((leftCode 4).drop 310).drop 54 by
    rw [List.drop_drop]]
  exact List.take_append_drop 54 ((leftCode 4).drop 310)

theorem first_cap (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1006) :
    ∀ middle, runInstrSeq ((leftCode 4).take 213)
      (stateAt s pc w (mask :: rho)) = some middle → middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances 4 i (List.mem_of_mem_take hi)
  · rw [first_total]
    simp only [stateAt, roundEntry, List.length_append, List.length_cons, List.length_nil]
    omega

theorem second_cap (s : State) (hstack : s.stack.length < 1023) :
    ∀ middle, runInstrSeq (((leftCode 4).drop 213).take 97) s = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances 4 i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
  · rw [second_total]
    omega

theorem third_cap (s : State) (hstack : s.stack.length < 1023) :
    ∀ middle, runInstrSeq (((leftCode 4).drop 310).take 54) s = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances 4 i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
  · rw [third_total]
    omega

#print axioms first_cap
#print axioms second_cap
#print axioms third_cap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineCaps
