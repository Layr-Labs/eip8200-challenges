import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# Raw steps of the block exit at 4537 and of the loop targets

The resident tail stops at 4537 with the continuation in slot 16; `DUP16 JUMP` jumps to it and
keeps it. Each target finishes the tail itself (`ScheduledTailFrame.copyTemplate`), so the frame it
completes still carries its own address as the continuation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopPreRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerPersistentLoopRaw

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

/-! ## Block exit at 4537 and the loop targets (the tail finishes in the targets) -/

/-- Block exit: `DUP16 JUMP` jumps to the continuation in slot 16 and keeps it there. -/
def exitTemplate : List Instr := [.op (.Dup ⟨15, by decide⟩), .op .JUMP]

theorem run_exitQ (s : State) (pc : UInt256) (Q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code Q.limit.toNat = true) :
    runInstrSeq exitTemplate {s with pc := pc, stack := ScheduledTailRaw.stack3a Q rho} =
      some {s with pc := Q.limit, stack := ScheduledTailRaw.stack3a Q rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [exitTemplate, ScheduledTailRaw.stack3a,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hvalid]

/-- `PUSH1 v SWAP16 POP`: replace the continuation in slot 16 before the tail copy. -/
def setCont16Template (v : Nat) : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat v), .op (.Swap ⟨15, by decide⟩), .op .POP]

theorem run_setCont16Q (s : State) (pc : UInt256) (Q : ScheduledTailRaw.Input) (rho : List UInt256) (v : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq (setCont16Template v) {s with pc := pc, stack := ScheduledTailRaw.stack3a Q rho} =
      some {s with pc := pcAfter pc (setCont16Template v), stack := ScheduledTailRaw.stack3a {Q with limit := UInt256.ofNat v} rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [setCont16Template, ScheduledTailRaw.stack3a,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals (try rfl)

/-- Generic last-block test head at the exit stack: `JUMPDEST PUSH1 0x80 DUP16 ADD`. -/
def glHead16Template : List Instr :=
  [.op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op (.Dup ⟨15, by decide⟩), .op .ADD]

theorem run_glHead16Q (s : State) (pc : UInt256) (Q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq glHead16Template {s with pc := pc, stack := ScheduledTailRaw.stack3a Q rho} =
      some {s with pc := pcAfter pc glHead16Template, stack := (Q.off + UInt256.ofNat 128) :: ScheduledTailRaw.stack3a Q rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [glHead16Template, ScheduledTailRaw.stack3a,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hAdd, Word.word_toNat_ofNat, Word.literal_eq_ofNat]


theorem run_exit (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true) :
    runInstrSeq exitTemplate {s with pc := pc, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} =
      some {s with pc := cont, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} :=
  run_exitQ s pc _ rho hstack hrun hvalid

theorem run_setCont16 (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256) (v : Nat)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq (setCont16Template v) {s with pc := pc, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} =
      some {s with pc := pcAfter pc (setCont16Template v), stack := PersistentStaggerTailBridge.preStack memory h off (UInt256.ofNat v) rho} :=
  run_setCont16Q s pc _ rho v hstack hrun

theorem run_glHead16 (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq glHead16Template {s with pc := pc, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} =
      some {s with pc := pcAfter pc glHead16Template, stack := (off + UInt256.ofNat 128) :: PersistentStaggerTailBridge.preStack memory h off cont rho} :=
  run_glHead16Q s pc _ rho hstack hrun

/-- The shared continuation `T` after its `JUMPDEST`: finish the tail, advance the offset and jump
to the loop head (`<tail copy> SWAP11 PUSH1 0x40 ADD SWAP11 PUSH2 0x01cd JUMP`). -/
def advanceTemplate : List Instr :=
  ScheduledTailFrame.copyTemplate ++ incTemplate ++ backTemplate ++ PadJump.template 461

theorem run_advance (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true) :
    runInstrSeq advanceTemplate {s with pc := pc, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} =
      some {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (PersistentStaggerFunctional.result memory h) (nextOffset off) cont rho} := by
  have h1 := PersistentStaggerTailBridge.run_copy s pc memory h off cont rho (by omega) hrun
  have h2 := run_inc s (pcAfter pc ScheduledTailFrame.copyTemplate) (PersistentStaggerFunctional.result memory h)
    off cont rho (by omega) hrun
  have h3 := run_back s (pcAfter (pcAfter pc ScheduledTailFrame.copyTemplate) incTemplate)
    (PersistentStaggerFunctional.result memory h) (nextOffset off) cont rho (by omega) hrun
  have h4 := PadJump.run_template s (pcAfter (pcAfter (pcAfter pc ScheduledTailFrame.copyTemplate) incTemplate) backTemplate)
    (StaggerPersistentFrame.frame (PersistentStaggerFunctional.result memory h) (nextOffset off) cont rho) 461
    (by simp only [StaggerPersistentFrame.frame, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hvalid
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  simpa only [advanceTemplate, List.append_assoc, DenseScheduleTrace.pcAfter_append] using h1234

/-- The pad target after its `JUMPDEST`: the tail copy alone. -/
theorem run_padCopy (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq ScheduledTailFrame.copyTemplate {s with pc := pc, stack := PersistentStaggerTailBridge.preStack memory h off cont rho} =
      some {s with pc := pcAfter pc ScheduledTailFrame.copyTemplate, stack := StaggerPersistentFrame.frame (PersistentStaggerFunctional.result memory h) off cont rho} :=
  PersistentStaggerTailBridge.run_copy s pc memory h off cont rho hstack hrun

#print axioms run_exit
#print axioms run_setCont16
#print axioms run_glHead16
#print axioms run_advance
end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopPreRaw
