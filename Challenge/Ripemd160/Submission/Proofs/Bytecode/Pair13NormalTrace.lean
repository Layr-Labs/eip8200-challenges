import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open Pair13Endian

/-- The pool load at source `i` is `dualW` of the field this artifact gives that source: the
broadcast for the seven it still masks, the raw load for the nine it does not. -/
theorem poolWord_eq_dualW (memory : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    Pair13PoolRaw.poolWord (Shared32Scratch.fanMemory memory low high) i =
      Pair13WriterRaw.dualW (Shared32Scratch.wordsJ memory low high) i :=
  Shared32Scratch.fan_poolWordJ memory low high i hi

def normalTemplate : List Instr := (template ++ Pair13PoolRaw.template) ++ Pair13WriterRaw.writerTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1152 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1120 = UInt256.ofNat p) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := Pair13WriterRaw.writerMemory
          (Shared32Scratch.fanMemory s.memory
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))))
          (Shared32Scratch.wordsJ s.memory
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let words := Shared32Scratch.wordsJ s.memory low high
  let scratch := Pair13Endian.scratch3 s.memory low high
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  let s3 : State := {s2 with memory := Pair13PoolRaw.copied scratch}
  have ha : 37 ≤ s1.activeWords.toNat := Stagger144Active.loaded_active_ge37 s p hp hbound
  have ha2 : 37 ≤ s2.activeWords.toNat := ha
  have ha3 : 37 ≤ s3.activeWords.toNat := ha
  have hF : F.length ≤ 900 := by simp [F, stk]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have hclean6 : (words 6).toNat < 2 ^ 32 := by
    show (Shared32Scratch.wordsJ s.memory low high 6).toNat < 2 ^ 32
    rw [Shared32Scratch.wordsJ, if_pos (by tauto)]
    exact Shared32Scratch.fanWord_lt _ _ 6
  have h1 := run_template s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun hp hbound hq1 hq0
  have h3 := Pair13PoolRaw.run_actual s2 (pcAfter pc template) F hF hrun (by omega)
  have hpool : Pair13PoolRaw.poolStack (Pair13PoolRaw.poolWord (Pair13PoolRaw.copied scratch)) F =
      Pair13PoolRaw.poolStack (Pair13WriterRaw.dualW words) F := by
    have hD : ∀ i, i < 16 → Pair13PoolRaw.poolWord (Pair13PoolRaw.copied scratch) i =
        Pair13WriterRaw.dualW words i := fun i hi =>
      Shared32Scratch.fan_poolWordJ s.memory low high i hi
    simp (discharger := decide) only [Pair13PoolRaw.poolStack, hD]
  rw [show s2.memory = scratch from rfl, hpool] at h3
  have h13 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h3
  have h4 := Pair13WriterRaw.run_writer s3
    (pcAfter (pcAfter pc template) Pair13PoolRaw.template) ret words rest hrest hrun (by omega) hclean6
  have h := DenseScheduleTrace.runInstrSeq_append_running h13 (by exact hrun) h4
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append, s3, s2, s1, scratch, words,
    Shared32Scratch.fanMemory, low, high, rest, stk] using h

theorem exact_bytes : assembleBytes normalTemplate = [97, 4, 128, 140, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 96, 96, 82, 91, 97, 4, 96, 140, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 128, 96, 46, 82, 96, 28, 82, 96, 16, 128, 96, 96, 96, 78, 94, 96, 112, 96, 130, 94, 117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 96, 102, 81, 91, 91, 96, 42, 81, 130, 22, 96, 46, 81, 131, 22, 96, 76, 81, 91, 91, 96, 106, 81, 91, 91, 96, 8, 81, 96, 34, 81, 135, 22, 96, 4, 81, 96, 114, 81, 91, 91, 96, 38, 81, 138, 22, 96, 80, 81, 139, 22, 96, 68, 81, 140, 22, 96, 12, 81, 91, 91, 128, 96, 144, 27, 23, 95, 81, 96, 110, 81, 91, 91, 158, 96, 72, 81, 22, 132, 96, 126, 82, 128, 97, 3, 132, 82, 139, 96, 216, 82, 130, 97, 3, 114, 82, 132, 97, 3, 96, 82, 130, 97, 3, 78, 82, 128, 97, 3, 60, 82, 131, 97, 2, 46, 82, 141, 97, 2, 172, 82, 131, 97, 3, 168, 82, 133, 96, 108, 82, 135, 97, 3, 24, 82, 135, 97, 3, 6, 82, 135, 97, 2, 28, 82, 97, 2, 244, 82, 128, 97, 2, 10, 82, 141, 96, 90, 82, 135, 96, 72, 82, 128, 96, 54, 82, 96, 36, 82, 141, 97, 2, 154, 82, 133, 97, 1, 248, 82, 131, 97, 4, 56, 82, 136, 97, 4, 38, 82, 131, 97, 1, 230, 82, 97, 3, 204, 82, 131, 97, 2, 136, 82, 131, 97, 3, 240, 82, 136, 97, 2, 118, 82, 131, 97, 2, 100, 82, 97, 2, 226, 82, 136, 97, 1, 32, 82, 97, 2, 82, 82, 136, 97, 4, 20, 82, 136, 97, 1, 158, 82, 132, 97, 1, 104, 82, 97, 2, 208, 82, 97, 1, 14, 82, 129, 97, 1, 140, 82, 97, 1, 212, 82, 96, 18, 82, 97, 1, 86, 82, 96, 198, 82, 97, 1, 68, 82, 98, 0, 0, 252, 82, 95, 82, 97, 1, 194, 82, 96, 162, 82] := by decide
theorem end_pc : pcAfter (UInt256.ofNat 480) normalTemplate = UInt256.ofNat 884 := by decide
#print axioms run_normal
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
