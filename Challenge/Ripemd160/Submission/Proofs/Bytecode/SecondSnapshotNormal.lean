import Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalWriter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotRun
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotNormal
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory Pair13Endian
def normalTemplate : List Instr :=
  (templateV2 ++ SecondSnapshotRun.template) ++ FusedTerminalWriter.writerTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (hr : SecondSnapshotCertificates.Repeat4 s.memory)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 32 = UInt256.ofNat (p + 32))
    (hq0 : off = UInt256.ofNat p) (hpc : pc = UInt256.ofNat 458) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := FusedTerminalMemory.resultMemory s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p+32)))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let words := Pair13PoolRaw.poolWordV2 (PoolShapeV2.fanMemoryV2 s.memory low high)
  let scratch := Pair13Endian.scratchV2 s.memory low high
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  let s3 : State := {s2 with memory := SecondSnapshotCertificates.copiedTwo scratch}
  have ha : 35 ≤ s1.activeWords.toNat := Stagger144Active.loaded_active_ge35 s p hp hbound
  have ha2 : 35 ≤ s2.activeWords.toNat := ha
  have ha3 : 35 ≤ s3.activeWords.toNat := ha
  have hF : F.length ≤ 900 := by simp [F, stk]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have h1 := run_templateV2 s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun hp hbound hq1 hq0
  have h3 := SecondSnapshotRun.run_actual_of_small s2 (pcAfter pc templateV2) F (SecondSnapshotCertificates.scratch_repeat _ _ _ hr) hF hrun (by omega)
  have h13 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h3
  have h4 := FusedTerminalWriter.run_writer s3
    (pcAfter (pcAfter pc templateV2) SecondSnapshotRun.template) ret words rest hrest hrun (by omega) (by rw [hpc]; decide)
  have h134 := DenseScheduleTrace.runInstrSeq_append_running h13 (by exact hrun) h4
  have h := h134
  have hmem := (SecondSnapshotCertificates.second_writer_eq scratch words).trans
    (ScratchSnapshotMemory.writer_eq scratch words)
  change FusedTerminalMemory.writerMemory (SecondSnapshotCertificates.copiedTwo scratch) words =
    FusedTerminalMemory.writerMemory (Pair13PoolRaw.copiedV2 scratch) words at hmem
  simp only [s3, ScratchSnapshotMemory.pool_eq] at h
  rw [hmem] at h
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append,
    s1, s2, s3, scratch, Pair13Endian.scratchV2, words,
    FusedTerminalMemory.resultMemory, PoolShapeV2.fanMemoryV2, low, high, rest, stk] using h

theorem exact_bytes : Challenge.EvmProof.PcEncoding.assembleBytes normalTemplate = [139,97,0,32,1,81,128,96,8,28,129,24,143,22,97,1,1,2,24,143,129,128,96,16,28,24,22,98,1,0,1,2,24,96,162,82,91,139,81,128,96,8,28,129,24,143,22,97,1,1,2,24,143,129,128,96,16,28,24,22,98,1,0,1,2,24,96,252,82,96,16,128,96,162,96,144,94,96,178,81,96,196,82,96,252,96,234,94,97,1,12,81,97,1,30,82,96,176,81,96,168,81,97,1,10,81,97,1,14,81,96,142,81,96,172,81,96,232,81,97,1,2,81,96,228,81,96,180,81,97,1,6,81,96,146,81,96,134,81,96,236,81,96,224,81,96,138,81,128,97,3,132,82,134,97,3,240,82,130,97,3,114,82,132,97,0,126,82,132,97,3,96,82,130,97,3,78,82,128,97,3,60,82,131,97,3,168,82,131,97,2,46,82,135,97,2,28,82,133,96,108,82,141,97,2,172,82,143,88,82,141,97,1,158,82,97,2,244,82,128,97,2,10,82,141,96,90,82,135,96,72,82,96,54,82,133,97,1,248,82,131,97,4,56,82,131,97,1,230,82,136,97,4,38,82,97,3,204,82,136,97,0,216,82,131,97,2,136,82,136,97,2,118,82,131,98,0,2,100,82,88,82,136,97,1,32,82,117,255,255,255,255,0,0,0,0,0,0,0,0,0,0,0,0,0,0,255,255,255,255,22,97,2,82,82,136,97,4,20,82,97,2,208,82,97,1,14,82,129,97,1,140,82,128,88,82,97,1,212,82,97,0,18,82,97,1,104,82,97,0,198,82,97,1,68,82,96,252,82,95,82,97,1,194,82,96,162,82] := by decide

theorem end_pc : pcAfter (UInt256.ofNat 458) normalTemplate = UInt256.ofNat 826 := by decide

#print axioms exact_bytes
#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotNormal
