import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144DispatchRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

def template (dest : Nat) : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .CALLDATASIZE, .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_miss (s : State) (pc ptr h0 h1 h2 h3 h4 off : UInt256) (rho : List UInt256)
    (dest : Nat) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat) :
    runInstrSeq (template dest) {s with pc := pc, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} =
      some {s with pc := pcAfter pc (template dest), stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat s.executionEnv.calldata.size) off = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt hfit, if_neg hmiss]
  simp (discharger := omega) [template, runInstrSeq, Stepper.runInstr,
    hrun, hcap, heq, List.length_cons, List.getElem?_cons_zero, Nat.add_assoc, pcAfter, UInt256.succ, Instr.size,
    Word.literal_eq_ofNat, UInt256.isTrue]
  rfl

theorem run_hit (s : State) (pc ptr h0 h1 h2 h3 h4 off : UInt256) (rho : List UInt256)
    (dest : Nat) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} =
      some {s with pc := UInt256.ofNat dest, stack := ptr :: h0 :: h1 :: h2 :: h3 :: h4 :: off :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat s.executionEnv.calldata.size) off = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt hfit, if_pos hhit]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, runInstrSeq, Stepper.runInstr,
    hrun, hcap, heq, List.length_cons, List.getElem?_cons_zero, Nat.add_assoc, hvalid, Word.literal_eq_ofNat, UInt256.isTrue]

#print axioms run_miss
#print axioms run_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144DispatchRaw
