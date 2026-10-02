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

/-- Finish test on the unadvanced offset: `off > limit` jumps to the output. -/
def template (dest : Nat) : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .GT,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

/-- Advance the offset: it stays on top and the resident factor word sits in slot 12. -/
def incTemplate : List Instr :=
  [.op (.Swap ⟨10, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .ADD]

/-- Test the advanced offset (still on top) for the pad-only block. -/
def padTemplate (dest : Nat) : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .EQ,
   .push ⟨1, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

/-- Swap the advanced offset back into slot 12. -/
def backTemplate : List Instr := [.op (.Swap ⟨10, by decide⟩)]

def nextOffset (off : UInt256) : UInt256 := off + UInt256.ofNat 64

/-- The pad-only block's `PUSH20` mark word, which it leaves in slot 12 to end the loop. -/
def padMark : UInt256 := UInt256.ofNat (128 * (1 + 2 ^ 144))

/-- The block entry stack: the pad-only block (`size = 64 i < 256`) starts with the advanced
offset still on top. -/
def entryStack (input : ByteArray) (i : Nat) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : List UInt256 :=
  if input.size = i * 64 ∧ input.size < 256 then StaggerPersistentFrame.exitFrame h off limit rho
  else StaggerPersistentFrame.frame h off limit rho

/-- The slot-12 word a block leaves for the exit test. -/
def blockMark (input : ByteArray) (i : Nat) (off : UInt256) : UInt256 :=
  if input.size = i * 64 ∧ input.size < 256 then padMark else off

theorem padMark_toNat : padMark.toNat = 128 * (1 + 2 ^ 144) := by
  unfold padMark
  rw [Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

/-- The offset is past the limit: jump to the output with the frame unchanged. -/
theorem run_gt (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hgt : limit.toNat < off.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hc : UInt256.gt off limit = UInt256.ofNat 1 := by
    unfold UInt256.gt
    rw [if_pos hgt]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, StaggerPersistentFrame.frame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_le (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hle : off.toNat ≤ limit.toNat) :
    runInstrSeq (template dest) {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc (template dest)
        stack := StaggerPersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hc : UInt256.gt off limit = UInt256.ofNat 0 := by
    unfold UInt256.gt
    rw [if_neg (by omega)]
  simp (discharger := omega) [template, StaggerPersistentFrame.frame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

/-- Advance the offset by one block. -/
theorem run_inc (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq incTemplate {s with pc := pc, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc incTemplate
        stack := StaggerPersistentFrame.exitFrame h (nextOffset off) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [incTemplate, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    nextOffset, runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

/-- The advanced offset equals the limit: jump to the pad-only block with it still on top. -/
theorem run_hit (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : off = limit)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (padTemplate dest) {s with pc := pc, stack := StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.exitFrame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off limit = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [if_pos (by rw [hhit])]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [padTemplate, StaggerPersistentFrame.exitFrame,
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
        stack := StaggerPersistentFrame.exitFrame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off limit = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [if_neg (fun h => hmiss (Word.word_ext h))]
  simp (discharger := omega) [padTemplate, StaggerPersistentFrame.exitFrame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    heq, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

/-- Neither finish nor pad: the advanced offset goes back into slot 12. -/
theorem run_back (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq backTemplate {s with pc := pc, stack := StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := pcAfter pc backTemplate
        stack := StaggerPersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [backTemplate, StaggerPersistentFrame.frame, StaggerPersistentFrame.exitFrame,
    runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat]


#print axioms run_hit
#print axioms run_miss
#print axioms run_gt
#print axioms run_le
#print axioms run_inc
#print axioms run_back
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
