import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.BackwardSnapshotRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PoolReference
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Scratch
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pair13NormalTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open HoistedInherited.Pair13Endian

/-- The S51 pool load at source `i` is the dual-lane broadcast of exactly the schedule word
the S48 pool produced from the same scratch halves. -/
theorem poolWord_eq_dualW (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) (i : Nat)
    (hi : i < 16) :
    HoistedInherited.Pair13PoolRaw.cleanPoolWord (HoistedInherited.Shared32Scratch.fanMemory memory low high) i =
      HoistedInherited.Pair13WriterRaw.dualW
        (StaggerScratch.poolWord (StaggerScratch.scratchMemory memory low high)) i := by
  have h := HoistedInherited.Shared32Scratch.fan_poolWord memory low high hlow i hi
  rw [HoistedInherited.Pair13WriterRaw.dualW, HoistedInherited.Shared32Scratch.dualOf] at *
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
        memory := HoistedInherited.PoolShapeV2.clearTerminal s.memory} := by
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
    State.activeWordsAfterUInt256, hact, Word.word_toNat_ofNat, HoistedInherited.PoolShapeV2.clearTerminal]
  exact ⟨rfl, rfl⟩

/-- The complete candidate normal path, PC 462 through PC 824. -/
def normalTemplate : List Instr :=
  (candidateTemplate ++ HoistedInherited.BackwardSnapshotRun.template) ++ HoistedInherited.BackwardSnapshotRun.writerTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 32 = UInt256.ofNat (p + 32))
    (hq0 : off = UInt256.ofNat p) (hpc : pc = UInt256.ofNat 462) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := HoistedInherited.PoolReference.dataMemory s.memory p
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let words := HoistedInherited.Pair13PoolRaw.poolWordV2 (HoistedInherited.BackwardSnapshotMemory.fanMemory s.memory low high)
  let scratch := HoistedInherited.Pair13Endian.scratchV2 s.memory low high
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  let s3 : State := {s2 with memory := HoistedInherited.BackwardSnapshotMemory.copiedFour scratch}
  have ha : 35 ≤ s1.activeWords.toNat := Stagger144Active.loaded_active_ge35 s p hp hbound
  have ha2 : 35 ≤ s2.activeWords.toNat := ha
  have ha3 : 35 ≤ s3.activeWords.toNat := ha
  have hF : F.length ≤ 900 := by simp [F, stk]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have h1 := run_candidate s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun hp hbound hq1 hq0
  have h3 := HoistedInherited.BackwardSnapshotRun.run_actual_of_small s2 (pcAfter pc candidateTemplate) F hF hrun (by omega)
  have h13 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h3
  have h4 := HoistedInherited.BackwardSnapshotRun.run_writer s3
    (pcAfter (pcAfter pc candidateTemplate) HoistedInherited.BackwardSnapshotRun.template) ret words rest hrest hrun (by omega) (by rw [hpc]; decide)
  have h134 := DenseScheduleTrace.runInstrSeq_append_running h13 (by exact hrun) h4
  have h := h134
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append,
    s1, s2, s3, scratch, HoistedInherited.Pair13Endian.scratchV2, words,
    HoistedInherited.PoolReference.dataMemory, HoistedInherited.BackwardSnapshotMemory.resultMemory, HoistedInherited.BackwardSnapshotMemory.fanMemory, low, high, rest, stk] using h

theorem writer_pc :
    pcAfter (pcAfter (UInt256.ofNat 462) candidateTemplate) HoistedInherited.BackwardSnapshotRun.template =
      UInt256.ofNat 608 := by decide

theorem end_pc : pcAfter (UInt256.ofNat 462) normalTemplate = UInt256.ofNat 824 := by decide

#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pair13NormalTrace
