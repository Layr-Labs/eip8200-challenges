import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAbsoluteSelectorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

/-- Absolute quotient/mask addressing into disjoint 32-byte ABI digest rows.
Widened constant pushes preserve the 17-byte selector interval. -/
def prefixTemplate : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .CODESIZE,
    .op .CALLDATASIZE,
    .push ⟨9, by decide⟩ (UInt256.ofNat 10025211223323981654),
    .op .DIV, .op .AND,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0) ]

def selected (codesize : UInt256) (size : Nat) : UInt256 :=
  UInt256.land (UInt256.div (UInt256.ofNat 10025211223323981654) (UInt256.ofNat size)) codesize

theorem run_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := 0 :: selected (UInt256.ofNat s.executionEnv.code.size)
          s.executionEnv.calldata.size :: 32 :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [prefixTemplate, selected, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, hsub_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_prefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAbsoluteSelectorRaw
