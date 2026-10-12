import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawTransition
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence
private theorem comm_hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem comm_hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem comm_hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl
private theorem comm_signed_sentinel_div9 :
    UInt256.sdiv (UInt256.shiftLeft c96 (UInt256.ofNat 2)) (UInt256.ofNat 9) =
      UInt256.sub (UInt256.ofNat 0) (UInt256.mul (UInt256.ofNat 14) PatternedSwar.M) := by decide
private theorem comm_add_negative_eq_sub (a b : UInt256) :
    UInt256.add a (UInt256.sub (UInt256.ofNat 0) b) = UInt256.sub a b := by
  unfold UInt256.add UInt256.sub
  congr 1
  simp [sub_eq_add_neg, UInt256.ofNat]

/-- Experimental boundary schedule saves one SWAP while preserving the 41-byte
transition span. The four-byte shift immediate is a gas-neutral width allocation.
The raw theorem below is generic; this alternate is not yet the installed `J2Sites` slice. -/
def commutedSignedTemplate : List Instr := [
  .op .JUMPDEST, .op (.Swap ⟨1, by decide⟩),
  .op (.Dup ⟨5, by decide⟩), .push ⟨4, by decide⟩ (UInt256.ofNat 2), .op .SHL,
  .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .OR,
  .push ⟨1, by decide⟩ (UInt256.ofNat 9), .op (.Dup ⟨1, by decide⟩),
  .op (.Swap ⟨2, by decide⟩), .op .SDIV, .op .ADD,
  .op .XOR, .op .XOR, .op (.Swap ⟨1, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 251), .op (.Dup ⟨7, by decide⟩), .op .ADD,
  .op (.Dup ⟨0, by decide⟩), .op .CALLDATASIZE, .op .SUB,
  .op (.Dup ⟨0, by decide⟩), .op .CALLDATASIZE, .op .SAR, .op .AND, .op .ADD,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op (.Dup ⟨1, by decide⟩), .op .SUB,
  .op (.Swap ⟨4, by decide⟩), .op .POP, .op (.Swap ⟨6, by decide⟩), .op (.Swap ⟨1, by decide⟩)
]

theorem commuted_signed_size : (commutedSignedTemplate.map Instr.size).sum = 41 := by decide

theorem commuted_signed_count : commutedSignedTemplate.length = 34 := by decide

theorem run_commuted_signed (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq commutedSignedTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc commutedSignedTemplate, stack := f.off :: frame (transitionResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [commutedSignedTemplate, transitionResult, frame, c114,
      tw, emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, comm_signed_sentinel_div9, comm_add_negative_eq_sub, ← hlen,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [comm_signed_sentinel_div9, comm_add_negative_eq_sub, comm_hsub_eq, comm_hadd_eq, comm_hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_commuted_signed
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
