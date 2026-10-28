import Challenge.Ripemd160.Submission.Local20261028.PadModel
import Challenge.Ripemd160.Submission.Local20261028.PadRawRight0
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
import Challenge.Ripemd160.Submission.Local20261028.PadModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreRight0
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation PadCommon
def input (n : UInt256) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word n h4 (.k) q right k, word n h4 (.a) q right k, word n h4 (.b) q right k, word n h4 (.c) q right k, word n h4 (.d) q right k, word n h4 (.e) q right k, word n h4 (.factor) q right k, word n h4 (.lower) q right k, word n h4 (.cache 140) q right k, word n h4 (.cache 350) q right k, word n h4 (.cache 310) q right k, word n h4 (.cache 190) q right k, word n h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem output_eq (n : UInt256) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    PadRawRight0.outputStack n (input n h4 q right (UInt256.ofNat 1352829926)) rho =
      stack n h4 [ .b, .e, .d, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (PadModel.right0 n q) (right) (UInt256.ofNat 1352829926) rho := by
  simp only [PadRawRight0.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, PadValues.load,
    PadModel.initial, PadModel.pair, PadModel.pairWord, PadModel.left,
    PadModel.right0, PadModel.right1, PadModel.right2,
    PadModel.left77, PadModel.left78, PadModel.left79,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, factorPlusWord, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [PadCommon.add_comm, PadCommon.add_left_comm,
    PadCommon.add_assoc, PadCommon.mul_comm,
    PadCommon.land_comm, PadCommon.lor_comm, PadCommon.xor_comm,
    PadCommon.xor_left_comm, PadCommon.xor_assoc]
  all_goals first | rfl | trivial
#print axioms output_eq
theorem run (s : State) (n h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (halias : rho[2]? = some q.b) (haliasC : rho[1]? = some q.c)
    (haliasD : rho[0]? = some q.d) (haliasA : rho[3]? = some q.a) (hh4 : h4 = q.e)
    (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    StackRoundTrace.runInstrSeq PadRawRight0.template {s with pc := UInt256.ofNat 89, stack := stack n h4 [ .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .e ] q right (UInt256.ofNat 1352829926) rho} =
      some {s with pc := UInt256.ofNat 121, stack := stack n h4 [ .b, .e, .d, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (PadModel.right0 n q) (right) (UInt256.ofNat 1352829926) rho} := by
  have h := PadRawRight0.run_actual s (UInt256.ofNat 89) n (input n h4 q right (UInt256.ofNat 1352829926)) rho hs halias haliasC haliasD haliasA (by rfl) hh4 hr ha hcal hmem
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 89) PadRawRight0.template = UInt256.ofNat 121 := by decide +kernel
  rw [hend] at h
  rw [output_eq] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreRight0
