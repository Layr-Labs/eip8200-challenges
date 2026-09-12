import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

def template (dest : Nat) : List Instr :=
  [.op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat 64),
   .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .POP,
   .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

def nextOffset (off : UInt256) : UInt256 := off + UInt256.ofNat 64

theorem run_continue (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat ≠ limit.toNat) :
    runInstrSeq (template dest) {s with pc := pc, stack := PersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc (template dest)
        stack := PersistentFrame.frame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (nextOffset off) limit = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [if_neg hmiss]
  change UInt256.eq (off + UInt256.ofNat 64) limit = UInt256.ofNat 0 at heq
  simp (discharger := omega) [template, PersistentFrame.frame, nextOffset, runInstrSeq,
    Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue]

theorem run_exit (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hhit : (nextOffset off).toNat = limit.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := PersistentFrame.frame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := PersistentFrame.frame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (nextOffset off) limit = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [if_pos hhit]
  change UInt256.eq (off + UInt256.ofNat 64) limit = UInt256.ofNat 1 at heq
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, PersistentFrame.frame, nextOffset, runInstrSeq,
    Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, hvalid, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue]


#print axioms run_continue
#print axioms run_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopRaw
