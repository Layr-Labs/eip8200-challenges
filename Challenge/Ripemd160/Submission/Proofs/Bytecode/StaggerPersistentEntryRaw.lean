import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerPersistentFrame

def dispatchTemplate (dest : Nat) : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .CALLDATASIZE, .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_miss (s : State) (pc ptr off limit : UInt256) (h : Compression.HashState) (rho : List UInt256)
    (dest : Nat) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ off.toNat) :
    runInstrSeq (dispatchTemplate dest) {s with pc := pc, stack := ptr :: frame h off limit rho} =
      some {s with pc := pcAfter pc (dispatchTemplate dest), stack := ptr :: frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat s.executionEnv.calldata.size) off = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt hfit, if_neg hmiss]
  simp (discharger := omega) [dispatchTemplate, frame, runInstrSeq, Stepper.runInstr,
    hrun, hcap, heq, List.length_cons, List.getElem?_cons_zero, Nat.add_assoc, pcAfter, UInt256.succ, Instr.size,
    Word.literal_eq_ofNat, UInt256.isTrue]
  rfl

theorem run_hit (s : State) (pc ptr off limit : UInt256) (h : Compression.HashState) (rho : List UInt256)
    (dest : Nat) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hhit : s.executionEnv.calldata.size = off.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (dispatchTemplate dest) {s with pc := pc, stack := ptr :: frame h off limit rho} =
      some {s with pc := UInt256.ofNat dest, stack := ptr :: frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat s.executionEnv.calldata.size) off = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt hfit, if_pos hhit]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [dispatchTemplate, frame, runInstrSeq, Stepper.runInstr,
    hrun, hcap, heq, List.length_cons, List.getElem?_cons_zero, Nat.add_assoc, hvalid, Word.literal_eq_ofNat, UInt256.isTrue]

def callTemplate : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 1152), .op (.Dup ⟨6, by decide⟩), .op .ADD]
def pointer (off : UInt256) : UInt256 := UInt256.add (UInt256.ofNat 1152) off

theorem run_call (s : State) (pc off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) :
    runInstrSeq callTemplate {s with pc := pc, stack := frame h off limit rho} =
      some {s with pc := pcAfter pc callTemplate, stack := pointer off :: frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [callTemplate, frame, pointer, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    List.getElem?_cons_zero, Nat.add_assoc, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
  exact Word.word_add_comm _ _
#print axioms run_call
#print axioms run_miss
#print axioms run_hit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
