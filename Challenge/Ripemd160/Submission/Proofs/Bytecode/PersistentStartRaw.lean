import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStartRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

def initialTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0xc3d2e1f0),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x10325476),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x98badcfe),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xefcdab89),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x67452301)]

def testTemplate (dest : Nat) : List Instr :=
  [.op .CALLDATASIZE, .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_initial (s : State) (pc off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1014) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := off :: limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := PersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 9) : rho.length + n < 1024 := by omega
  simp [initialTemplate, PersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]

theorem run_positive (s : State) (pc : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1021) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256) (hpos : 0 < s.executionEnv.calldata.size)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (testTemplate dest) {s with pc := pc, stack := rho} =
      some {s with pc := UInt256.ofNat dest, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  have hne : s.executionEnv.calldata.size ≠ 0 := by omega
  have hn : s.executionEnv.calldata.size % 2^256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hfit]
    exact hne
  norm_num only at hn
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp [testTemplate, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit, UInt256.isTrue, hne, hn, hvalid]

theorem run_empty (s : State) (pc : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1021) (hrun : s.halt = .Running)
    (hempty : s.executionEnv.calldata.size = 0) :
    runInstrSeq (testTemplate dest) {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc (testTemplate dest), stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  simp [testTemplate, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    hempty, Word.word_toNat_ofNat, UInt256.isTrue]
  rfl

#print axioms run_initial
#print axioms run_positive
#print axioms run_empty
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStartRaw
