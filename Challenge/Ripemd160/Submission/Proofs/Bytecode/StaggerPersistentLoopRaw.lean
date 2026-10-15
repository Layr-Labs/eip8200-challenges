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

/-- Test the advanced offset (just under the `MSIZE` word on top) for the pad-only block. -/
def padTemplate (dest : Nat) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .EQ,
   .push ⟨1, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

/-- Swap the advanced offset back into slot 12. -/
def backTemplate : List Instr := [.op (.Swap ⟨10, by decide⟩)]

def nextOffset (off : UInt256) : UInt256 := off + UInt256.ofNat 64

/-- The output entry: the continuation of the pad-only block and of the 32-byte block. -/
def outPC : Nat := 4736

/-- The block entry stack: every block, the pad-only block included, starts with the frame. -/
def entryStack (_input : ByteArray) (_i : Nat) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : List UInt256 :=
  StaggerPersistentFrame.frame h off limit rho

/-- The slot-11 word a block leaves: the offset it ran with (the pad-only block keeps it too). -/
def blockMark (_input : ByteArray) (_i : Nat) (off _cont : UInt256) : UInt256 := off

/-- The slot-12 continuation a block leaves: the pad-only block installs the output entry. -/
def blockCont (input : ByteArray) (i : Nat) (cont : UInt256) : UInt256 :=
  if input.size = i * 64 ∧ input.size < 256 then UInt256.ofNat outPC else cont

/-- Block exit: `DUP13 JUMP` jumps to the continuation in slot 12. -/
def dispatchTemplate : List Instr := [.op (.Swap ⟨12, by decide⟩), .op .JUMP]

theorem run_dispatch (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont junk : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true) :
    runInstrSeq dispatchTemplate {s with pc := pc, stack := junk :: StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := cont
        stack := StaggerPersistentFrame.frame h off junk rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [dispatchTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hvalid]

/-- Generic last-block test head: `JUMPDEST PUSH1 0x80 DUP13 ADD` puts `off + 128` on top. -/
def glHeadTemplate : List Instr :=
  [.op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op (.Dup ⟨12, by decide⟩), .op .ADD]

/-- The 128 stub falls through the shared join: `PUSH1 v JUMPDEST SWAP13`. -/
def setContTemplate (v : Nat) : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat v), .op .JUMPDEST, .op (.Swap ⟨12, by decide⟩)]

theorem run_setCont (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256) (v : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq (setContTemplate v) {s with pc := pc, stack := StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := pcAfter pc (setContTemplate v)
        stack := cont :: StaggerPersistentFrame.frame h off (UInt256.ofNat v) rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [setContTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, add_eq_hAdd,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]

/-- The continuation push of the last-block stay (59) and of the 192 stub (193). -/
def pushContTemplate (v : Nat) : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat v)]

theorem run_pushCont (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256) (v : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq (pushContTemplate v) {s with pc := pc, stack := StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := pcAfter pc (pushContTemplate v)
        stack := UInt256.ofNat v :: StaggerPersistentFrame.frame h off cont rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [pushContTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, add_eq_hAdd,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]

/-- The shared join at 131, `JUMPDEST SWAP13`, installs the pushed continuation. -/
def joinSwapTemplate : List Instr :=
  [.op .JUMPDEST, .op (.Swap ⟨12, by decide⟩)]

theorem run_joinSwap (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont x : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq joinSwapTemplate {s with pc := pc, stack := x :: StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := pcAfter pc joinSwapTemplate
        stack := cont :: StaggerPersistentFrame.frame h off x rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [joinSwapTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, add_eq_hAdd,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]

theorem run_glHead (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq glHeadTemplate {s with pc := pc, stack := StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := pcAfter pc glHeadTemplate
        stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [glHeadTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

/-- Generic last-block test: `LT PUSH2 0x12b0 JUMPI` leaves for the output iff `MSIZE < off + 128`. -/
def glTestTemplate (dest : Nat) : List Instr :=
  [.op .LT, .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_glExit (s : State) (pc : UInt256) (stack : List UInt256) (m q : UInt256) (dest : Nat)
    (hstack : stack.length ≤ 1000) (hrun : s.halt = .Running)
    (hlt : m.toNat < q.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (glTestTemplate dest) {s with pc := pc, stack := m :: q :: stack} =
      some {s with pc := UInt256.ofNat dest, stack := stack} := by
  have hcap (n : Nat) (hn : n ≤ 20) : stack.length + n < 1024 := by omega
  have hc : UInt256.lt m q = UInt256.ofNat 1 := by
    unfold UInt256.lt
    rw [if_pos hlt]
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [glTestTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

theorem run_glStay (s : State) (pc : UInt256) (stack : List UInt256) (m q : UInt256) (dest : Nat)
    (hstack : stack.length ≤ 1000) (hrun : s.halt = .Running)
    (hge : ¬ m.toNat < q.toNat) :
    runInstrSeq (glTestTemplate dest) {s with pc := pc, stack := m :: q :: stack} =
      some {s with pc := pcAfter pc (glTestTemplate dest), stack := stack} := by
  have hcap (n : Nat) (hn : n ≤ 20) : stack.length + n < 1024 := by omega
  have hc : UInt256.lt m q = UInt256.ofNat 0 := by
    unfold UInt256.lt
    rw [if_neg hge]
  simp (discharger := omega) [glTestTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    hc, add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue, UInt256.isZero]

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
    (m : UInt256) (hhit : off = m)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (padTemplate dest) {s with pc := pc, stack := m :: StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := UInt256.ofNat dest
        stack := StaggerPersistentFrame.exitFrame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off m = UInt256.ofNat 1 := by
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
    (m : UInt256) (hmiss : off ≠ m) :
    runInstrSeq (padTemplate dest) {s with pc := pc, stack := m :: StaggerPersistentFrame.exitFrame h off limit rho} =
      some {s with
        pc := pcAfter pc (padTemplate dest)
        stack := StaggerPersistentFrame.exitFrame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq off m = UInt256.ofNat 0 := by
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
#print axioms run_dispatch
#print axioms run_glHead
#print axioms run_glExit
#print axioms run_glStay
#print axioms run_setCont
#print axioms run_pushCont
#print axioms run_joinSwap
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
