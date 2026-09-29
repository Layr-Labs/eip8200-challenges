import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Batteries.Data.Nat.Bitwise.Lemmas
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

private theorem add64 (off : UInt256) :
    UInt256.ofNat 64 + off = off + UInt256.ofNat 64 := Word.word_add_comm _ _

/-- Advance the offset (it stays on top) and test for the finish first: `off' > limit`. -/
def template (dest : Nat) : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .ADD,
   .op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

/-- Swap the advanced offset back into slot 12 and test for the pad-only block. -/
def padTemplate (dest : Nat) : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .EQ,
   .push ⟨1, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

def nextOffset (off : UInt256) : UInt256 := off + UInt256.ofNat 64

/-- The advanced offset is past the limit: jump to the output with the offset still on top. -/
theorem run_gt (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hgt : limit.toNat < (nextOffset off).toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.exitFrame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hc : UInt256.gt (nextOffset off) limit = UInt256.ofNat 1 := by
    unfold UInt256.gt
    rw [if_pos hgt]
  change UInt256.gt (off + UInt256.ofNat 64) limit = UInt256.ofNat 1 at hc
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    nextOffset, runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, hvalid, add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_le (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hle : (nextOffset off).toNat ≤ limit.toNat) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc (template dest)
        stack := StaggerPersistentFrame.exitFrame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hc : UInt256.gt (nextOffset off) limit = UInt256.ofNat 0 := by
    unfold UInt256.gt
    rw [if_neg (by omega)]
  change UInt256.gt (off + UInt256.ofNat 64) limit = UInt256.ofNat 0 at hc
  simp (discharger := omega) [template, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    nextOffset, runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

/-- The offset equals the limit: jump to the pad-only block setup. -/
theorem run_hit (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : off = limit)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (padTemplate dest) {s with pc := pc, stack := StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off limit = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [if_pos (by rw [hhit])]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [padTemplate, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_miss (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hmiss : off ≠ limit) :
    runInstrSeq (padTemplate dest) {s with pc := pc, stack := StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := pcAfter pc (padTemplate dest)
        stack := StaggerPersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off limit = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [if_neg (fun h => hmiss (Word.word_ext h))]
  simp (discharger := omega) [padTemplate, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]


#print axioms run_hit
#print axioms run_miss
#print axioms run_gt
#print axioms run_le
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
