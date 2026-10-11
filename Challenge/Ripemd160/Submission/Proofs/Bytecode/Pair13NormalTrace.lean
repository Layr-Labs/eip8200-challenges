import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotNormal
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open Pair13Endian

/-- The S51 pool load at source `i` is the dual-lane broadcast of exactly the schedule word
the S48 pool produced from the same scratch halves. -/
theorem poolWord_eq_dualW (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) (i : Nat)
    (hi : i < 16) :
    Pair13PoolRaw.cleanPoolWord (Shared32Scratch.fanMemory memory low high) i =
      Pair13WriterRaw.dualW
        (StaggerScratch.poolWord (StaggerScratch.scratchMemory memory low high)) i := by
  have h := Shared32Scratch.fan_poolWord memory low high hlow i hi
  rw [Pair13WriterRaw.dualW, Shared32Scratch.dualOf] at *
  exact h

/-- `PUSH0 PUSH2 0x262 MSTORE8`: clear byte 610 (byte 16 of the terminal slot 594) after the
table stores, so the terminal round can read its message word without a lane mask. -/
def clearTemplate : List Instr :=
  [ .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 610),
    .op .MSTORE8 ]

theorem run_clear (s : State) (pc : UInt256) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) (hrun : s.halt = .Running)
    (hactive : 20 ≤ s.activeWords.toNat) :
    runInstrSeq clearTemplate {s with pc := pc, stack := stack} =
      some {s with
        pc := pcAfter pc clearTemplate
        stack := stack
        memory := PoolShapeV2.clearTerminal s.memory} := by
  have hcap (n : Nat) (hn : n ≤ 2) : stack.length + n < 1024 := by omega
  have h0 : stack.length < 1024 := by omega
  have h1 : stack.length + 1 < 1024 := by omega
  have h2 : stack.length + 1 + 1 < 1024 := by omega
  have hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 610 1) =
      s.activeWords := by
    have h : MachineState.activeWordsAfter s.activeWords.toNat 610 1 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (1 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [h]
    exact (Word.word_eq_ofNat_toNat _).symm
  simp (discharger := omega) [clearTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, h0, h1, h2, Instr.size, UInt256.succ, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hact, Word.word_toNat_ofNat, PoolShapeV2.clearTerminal]
  exact ⟨rfl, rfl⟩

abbrev normalTemplate := SecondSnapshotNormal.normalTemplate
abbrev run_normal := SecondSnapshotNormal.run_normal
abbrev exact_bytes := SecondSnapshotNormal.exact_bytes
abbrev end_pc := SecondSnapshotNormal.end_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
