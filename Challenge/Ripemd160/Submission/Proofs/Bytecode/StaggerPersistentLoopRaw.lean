import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Batteries.Data.Nat.Bitwise.Lemmas
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)


private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

private theorem add64 (off : UInt256) :
    UInt256.ofNat 64 + off = off + UInt256.ofNat 64 := Word.word_add_comm _ _

def template (dest : Nat) : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .ADD, .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .XOR, .op .JUMPDEST,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

def nextOffset (off : UInt256) : UInt256 := off + UInt256.ofNat 64

theorem run_continue (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat ≠ limit.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : (UInt256.xor (nextOffset off) limit).toNat ≠ 0 := by
    rw [word_toNat_xor]
    intro hz
    exact hmiss (Nat.eq_of_xor_eq_zero hz)
  change (UInt256.xor (off + UInt256.ofNat 64) limit).toNat ≠ 0 at heq
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, StaggerPersistentFrame.frame, nextOffset, runInstrSeq,
    Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, hvalid, add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_exit (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hhit : (nextOffset off).toNat = limit.toNat) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc (template dest)
        stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have heq : (UInt256.xor (nextOffset off) limit).toNat = 0 := by
    rw [word_toNat_xor, hhit, Nat.xor_self]
  change (UInt256.xor (off + UInt256.ofNat 64) limit).toNat = 0 at heq
  simp (discharger := omega) [template, StaggerPersistentFrame.frame, nextOffset, runInstrSeq,
    Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]


#print axioms run_continue
#print axioms run_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
