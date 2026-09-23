import Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackModel
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon

def suffix (h : WordLane) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [h.d, h.c, h.b, h.a, off, limit] ++ rho

def input (memory : ByteArray) (h q : WordLane) (off limit : UInt256) : JointRightPackRaw.Input :=
  { rd := q.d, k := UInt256.ofNat 1352829926, rb := q.b, rc := q.c, ra := q.a, re := q.e,
    factor := factorPlusWord, lower := lowerWord,
    cache140 := word memory h.e (.cache 140) q h (UInt256.ofNat 1352829926),
    cache350 := word memory h.e (.cache 350) q h (UInt256.ofNat 1352829926),
    cache310 := word memory h.e (.cache 310) q h (UInt256.ofNat 1352829926),
    cache190 := word memory h.e (.cache 190) q h (UInt256.ofNat 1352829926),
    h4 := h.e, h1 := h.b, h2 := h.c, h3 := h.d, h0 := h.a, off := off, limit := limit }

theorem input_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    JointRightPackRaw.inputStack (input memory h q off limit) rho =
      stack memory h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140,
        .cache 350, .cache 310, .cache 190, .cache 500]
        q h (UInt256.ofNat 1352829926) (suffix h off limit rho) := by
  simp [JointRightPackRaw.inputStack, input, stack, StaggerCoreCommon.word, suffix]

theorem output_eq (memory : ByteArray) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    JointRightPackRaw.outputStack memory (input memory h q off limit) rho =
      stack memory h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower,
        .cache 140, .cache 350, .cache 310, .cache 190, .cache 500]
        (StaggerCoreModel.pair h (StaggerCoreModel.right2 memory q)) h
        (StaggerAlgorithm.physicalKey 0) (suffix h off limit rho) := by
  have hm : JointRightPackRaw.pairMask = Paired144WordRound.pairWord := by decide
  have hu : JointRightPackRaw.upperMask = upperWord := by decide
  have hp : UInt256.lor lowerWord upperWord = Paired144WordRound.pairWord := by decide
  simp only [JointRightPackRaw.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word,
    StaggerCoreModel.pair, StaggerCoreModel.pairWord, StaggerCoreModel.right2,
    JointRightPackRaw.packed, JointRightPackRaw.rotatedC, JointRightPackRaw.roundT,
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackModel
