import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Sites
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Exact composed signed boundary versus the frozen unsigned leader

Independent comparison at the unchanged41-byte transition span. The installed
34-instruction transition uses the signed sentinel quotient and a commuted DUP
pair. The previous leader's35-instruction DIV96/MUL14 sequence is retained
literally. Generic execution restores the identical recurrence frame and suffix;
static work falls by5gas, with no memory or dynamic copy work in either window.
These certificates bind the local window only; the full universal theorem and
canonical Comparator remain mandatory for any submitted artifact.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ComposedBoundaryCertificates
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open J2Raw StackRoundTrace RecognitionRecurrence
private theorem u_hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem u_hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem u_hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

def frozenUnsignedTemplate : List Instr := [
  .op .JUMPDEST, .op (.Swap ⟨1, by decide⟩),
  .op (.Dup ⟨5, by decide⟩), .push ⟨2, by decide⟩ (UInt256.ofNat 2), .op .SHL,
  .op (.Dup ⟨1, by decide⟩), .op .OR,
  .push ⟨1, by decide⟩ (UInt256.ofNat 96), .op (.Dup ⟨7, by decide⟩), .op .DIV,
  .push ⟨1, by decide⟩ (UInt256.ofNat 14), .op .MUL,
  .op (.Dup ⟨1, by decide⟩), .op .SUB, .op .XOR, .op .XOR,
  .op (.Swap ⟨1, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 251),
  .op (.Dup ⟨7, by decide⟩),
  .op .ADD,
  .op (.Dup ⟨0, by decide⟩),
  .op .CALLDATASIZE,
  .op .SUB,
  .op (.Dup ⟨0, by decide⟩),
  .op .CALLDATASIZE,
  .op .SAR,
  .op .AND,
  .op .ADD,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .op (.Dup ⟨1, by decide⟩),
  .op .SUB,
  .op (.Swap ⟨4, by decide⟩),
  .op .POP,
  .op (.Swap ⟨6, by decide⟩),
  .op (.Swap ⟨1, by decide⟩)
]


theorem run_frozen_unsigned (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq frozenUnsignedTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc frozenUnsignedTemplate, stack := f.off :: frame (transitionResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [frozenUnsignedTemplate, transitionResult, frame, c114,
      tw, emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, repunit_div, repunit_hdiv, ← hlen,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [repunit_div, repunit_hdiv, u_hsub_eq, u_hadd_eq, u_hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl


theorem unsigned_count : frozenUnsignedTemplate.length = 35 := by decide
theorem signed_count : transitionTemplate.length = 34 := by decide
theorem unsigned_span : (frozenUnsignedTemplate.map Instr.size).sum = 41 := by decide
theorem signed_span : (transitionTemplate.map Instr.size).sum = 41 := by decide

theorem unsigned_cost :
    (frozenUnsignedTemplate.map (Meter.instrStaticCost .Osaka)).sum = 104 := by decide
theorem signed_cost :
    (transitionTemplate.map (Meter.instrStaticCost .Osaka)).sum = 99 := by decide
theorem saving :
    (transitionTemplate.map (Meter.instrStaticCost .Osaka)).sum + 5 =
      (frozenUnsignedTemplate.map (Meter.instrStaticCost .Osaka)).sum := by decide

theorem installed :
    (Artifact.submissionArtifact.instructions.drop 3456).take 34 = transitionTemplate := by rfl

theorem run_installed (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionTemplate, stack := f.off :: frame (transitionResult f) rho} :=
  J2Raw.run_transition s pc f rho hstack hrun hlen

#print axioms run_frozen_unsigned
#print axioms run_installed
#print axioms installed
#print axioms saving
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ComposedBoundaryCertificates
