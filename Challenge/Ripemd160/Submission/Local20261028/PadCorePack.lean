import Challenge.Ripemd160.Submission.Local20261028.PadRawPack
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
import Challenge.Ripemd160.Submission.Local20261028.PadModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCorePack
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation PadCommon

def suffix (h : WordLane) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [h.d, h.c, h.b, h.a, off, limit] ++ rho

def input (n : UInt256) (h q : WordLane) (off limit : UInt256) : PadRawPack.Input :=
  { rd := q.d, k := UInt256.ofNat 1352829926, rb := q.b, rc := q.c, ra := q.a, re := q.e,
    factor := factorPlusWord, lower := lowerWord,
    cache140 := word n h.e (.cache 140) q h (UInt256.ofNat 1352829926),
    cache350 := word n h.e (.cache 350) q h (UInt256.ofNat 1352829926),
    cache310 := word n h.e (.cache 310) q h (UInt256.ofNat 1352829926),
    cache190 := word n h.e (.cache 190) q h (UInt256.ofNat 1352829926),
    h4 := h.e, h1 := h.b, h2 := h.c, h3 := h.d, h0 := h.a, off := off, limit := limit }

theorem input_eq (n : UInt256) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    PadRawPack.inputStack (input n h q off limit) rho =
      stack n h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140,
        .cache 350, .cache 310, .cache 190, .cache 500]
        q h (UInt256.ofNat 1352829926) (suffix h off limit rho) := by
  simp [PadRawPack.inputStack, input, stack, PadCommon.word, PadValues.load, suffix]

theorem output_eq (n : UInt256) (h q : WordLane) (off limit : UInt256)
    (rho : List UInt256) :
    PadRawPack.outputStack n (input n h q off limit) rho =
      stack n h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower,
        .cache 140, .cache 350, .cache 310, .cache 190, .cache 500]
        (PadModel.pair h (PadModel.right2 n q)) h
        (StaggerAlgorithm.physicalKey 0) (suffix h off limit rho) := by
  have hm : PadRawPack.pairMask = Paired144WordRound.pairWord := by decide
  have hu : PadRawPack.upperMask = upperWord := by decide
  have hp : UInt256.lor lowerWord upperWord = Paired144WordRound.pairWord := by decide
  simp only [PadRawPack.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, PadValues.load,
    PadModel.pair, PadModel.pairWord, PadModel.right2,
    PadRawPack.packed, PadRawPack.rotatedC, PadRawPack.roundT,
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
theorem run (s : State) (n : UInt256) (h q : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    StackRoundTrace.runInstrSeq PadRawPack.template
      {s with pc := UInt256.ofNat 4638, stack := stack n h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] q h (UInt256.ofNat 1352829926) (suffix h off limit rho)} =
      some {s with pc := UInt256.ofNat 4738, stack := stack n h.e [.pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] (PadModel.pair h (PadModel.right2 n q)) h (StaggerAlgorithm.physicalKey 0) (suffix h off limit rho)} := by
  have raw := PadRawPack.run_actual s (UInt256.ofNat 4638) n (input n h q off limit) rho hs hr ha hcal hmem (by rfl)
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 4638) PadRawPack.template = UInt256.ofNat 4738 := by decide +kernel
  rw [hend, input_eq, output_eq] at raw
  exact raw
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCorePack
