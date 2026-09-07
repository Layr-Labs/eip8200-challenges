import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityStackEffect

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityCaps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace CavityQuadGroup CavityParams CavityStackEffect

theorem params_advances (q : Params) :
    ∀ instruction ∈ q.template, PairMultiplyLift.Advances instruction := by
  exact ConstpropQuad.specialized_advances q.function.val q.function.isLt
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) q.constant

theorem left_advances :
    ∀ instruction ∈ leftCode, PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  simp only [leftCode, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact params_advances (left 0) instruction h
  · exact params_advances (left 1) instruction h
  · exact params_advances (left 2) instruction h
  · exact params_advances (left 3) instruction h

theorem right_advances :
    ∀ instruction ∈ rightCode, PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  simp only [rightCode, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact params_advances (right 0) instruction h
  · exact params_advances (right 1) instruction h
  · exact params_advances (right 2) instruction h
  · exact params_advances (right 3) instruction h

theorem left_prefix_total : total (leftCode.take 320) = 1 := by decide
theorem right_prefix_total : total (rightCode.take 298) = 0 := by decide
theorem right_middle_total : total ((rightCode.drop 298).take 94) = 0 := by decide

theorem left_prefix_cap (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) :
    ∀ middle, runInstrSeq (leftCode.take 320) (stateAt s pc w rho) = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact left_advances i (List.mem_of_mem_take hi)
  · rw [left_prefix_total]
    simp only [stateAt, roundEntry, List.length_append, List.length_cons, List.length_nil]
    omega

theorem right_prefix_cap (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) :
    ∀ middle, runInstrSeq (rightCode.take 298) (stateAt s pc w rho) = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact right_advances i (List.mem_of_mem_take hi)
  · rw [right_prefix_total]
    simp only [stateAt, roundEntry, List.length_append, List.length_cons, List.length_nil]
    omega

#print axioms left_prefix_cap
#print axioms right_prefix_cap

theorem right_middle_cap (s : State) (hstack : s.stack.length < 1023) :
    ∀ middle, runInstrSeq ((rightCode.drop 298).take 94) s = some middle →
      middle.stack.length < 1023 := by
  apply cap_of_total
  · intro i hi
    exact right_advances i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
  · rw [right_middle_total]
    omega

#print axioms right_middle_cap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityCaps
