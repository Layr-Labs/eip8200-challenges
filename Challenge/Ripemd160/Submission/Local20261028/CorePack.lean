import Challenge.Ripemd160.Submission.Local20261028.RawPack
import Challenge.Ripemd160.Submission.Local20261028.CoreCommon
import Challenge.Ripemd160.Submission.Local20261028.CoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePack
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation CoreCommon

def suffix (h : WordLane) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [h.d, h.c, h.b, h.a, off, limit] ++ rho

def input (memory : ByteArray) (h q : WordLane) (off limit : UInt256) : RawPack.Input :=
  { rd := q.d, k := UInt256.ofNat 1352829926, rb := q.b, rc := q.c, ra := q.a, re := q.e,
    factor := factorPlusWord, lower := lowerWord,
    cache140 := word memory h.e (.cache 140) q h (UInt256.ofNat 1352829926),
    cache350 := word memory h.e (.cache 350) q h (UInt256.ofNat 1352829926),
    cache310 := word memory h.e (.cache 310) q h (UInt256.ofNat 1352829926),
    cache190 := word memory h.e (.cache 190) q h (UInt256.ofNat 1352829926),
    h4 := h.e, h1 := h.b, h2 := h.c, h3 := h.d, h0 := h.a, off := off, limit := limit }

theorem input_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    RawPack.inputStack (input memory h q off limit) rho =
      stack memory h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140,
        .cache 350, .cache 310, .cache 190, .cache 500]
        q h (UInt256.ofNat 1352829926) (suffix h off limit rho) := by
  simp [RawPack.inputStack, input, stack, CoreCommon.word, CoreModel.load, GeneralMessageLayout.addresses, suffix]

theorem output_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    RawPack.outputStack memory (input memory h q off limit) rho =
      stack memory h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower,
        .cache 140, .cache 350, .cache 310, .cache 190, .cache 500]
        (CoreModel.pair h (CoreModel.right2 memory q)) h
        (StaggerAlgorithm.physicalKey 0) (suffix h off limit rho) := by
  have hm : RawPack.pairMask = Paired144WordRound.pairWord := by decide
  have hu : RawPack.upperMask = upperWord := by decide
  have hp : UInt256.lor lowerWord upperWord = Paired144WordRound.pairWord := by decide
  simp only [RawPack.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, CoreCommon.word, CoreModel.load, GeneralMessageLayout.addresses,
    CoreModel.pair, CoreModel.pairWord, CoreModel.right2,
    RawPack.packed, RawPack.rotatedC, RawPack.roundT,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, factorPlusWord, suffix, hm, hu, hp, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [RawExpressionAC.add_assoc, RawExpressionAC.add_comm,
    RawExpressionAC.add_left_comm, RawExpressionAC.mul_comm, RawExpressionAC.land_comm,
    RawExpressionAC.lor_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm,
    RawExpressionAC.xor_left_comm]
  all_goals first | rfl | trivial

#print axioms input_eq
#print axioms output_eq
theorem run (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    StackRoundTrace.runInstrSeq RawPack.template
      {s with pc := UInt256.ofNat 901, stack := stack s.memory h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] q h (UInt256.ofNat 1352829926) (suffix h off limit rho)} =
      some {s with pc := UInt256.ofNat 1006, stack := stack s.memory h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] (CoreModel.pair h (CoreModel.right2 s.memory q)) h (StaggerAlgorithm.physicalKey 0) (suffix h off limit rho)} := by
  have raw := RawPack.run_actual s (UInt256.ofNat 901) (input s.memory h q off limit) rho hs hr ha (by rfl)
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 901) RawPack.template = UInt256.ofNat 1006 := by decide +kernel
  rw [hend, input_eq, output_eq] at raw
  exact raw
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePack
