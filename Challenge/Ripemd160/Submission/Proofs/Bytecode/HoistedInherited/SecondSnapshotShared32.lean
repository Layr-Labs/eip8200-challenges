import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalWriter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32SparseRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pair13NormalTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.BackwardSnapshotRun

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.SecondSnapshotShared32
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory HoistedInherited.Pair13Endian
open HoistedInherited.Shared32Scratch

def template : List Instr :=
  (HoistedInherited.SecondSnapshotRun.lowerTemplate ++ HoistedInherited.BackwardSnapshotRun.template) ++ HoistedInherited.BackwardSnapshotRun.writerTemplate

theorem run_table (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) (hpc : pc = UInt256.ofNat 498) :
    runInstrSeq template
      {s with
        pc := pc
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 1056) lim rho
        memory := writeWord s.memory 162 highWord} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 1056) lim rho
        memory := HoistedInherited.Shared32Table.tableMemory s.memory
        activeWords := UInt256.ofNat 35} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: UInt256.ofNat 1056 :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
    (UInt256.ofNat 1056) lim rho
  let scratch := HoistedInherited.Pair13Endian.scratchV2 s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1056)) highWord
  let s1 : State := {s with memory := writeWord s.memory 162 highWord}
  let s2 : State := {s with memory := scratch}
  let s3 : State := {s with memory := HoistedInherited.BackwardSnapshotMemory.copiedFour scratch}
  have ha : 34 ≤ s2.activeWords.toNat := by change 34 ≤ s.activeWords.toNat; rw [hactive]; decide
  have ha3 : s3.activeWords = UInt256.ofNat 34 := hactive
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have h1 := HoistedInherited.SecondSnapshotRun.run_lower s1 pc ret (UInt256.ofNat 4294967295)
    a2 a3 a4 a5 a6 a7 a8 a9 a10 lim rho hstack hrun hactive
  have hread : MachineState.readWord s1.memory 1056 = MachineState.readWord s.memory 1056 :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))
  rw [hread] at h1
  have h2 := HoistedInherited.BackwardSnapshotRun.run_actual_of_small s2 (pcAfter pc HoistedInherited.SecondSnapshotRun.lowerTemplate) F hF hrun ha
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := HoistedInherited.BackwardSnapshotRun.run_writer_grow s3
    (pcAfter (pcAfter pc HoistedInherited.SecondSnapshotRun.lowerTemplate) HoistedInherited.BackwardSnapshotRun.template)
    ret (HoistedInherited.Pair13PoolRaw.poolWordV2 (HoistedInherited.BackwardSnapshotMemory.copiedFour scratch)) rest hrest hrun ha3 (by rw [hpc]; decide)
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  simpa only [template, DenseScheduleTrace.pcAfter_append,
    s3, s2, s1, scratch, HoistedInherited.Shared32Table.tableMemory, HoistedInherited.BackwardSnapshotMemory.resultMemory,
    HoistedInherited.BackwardSnapshotMemory.fanMemory, rest, stk] using h123

theorem end_pc : pcAfter (UInt256.ofNat 498) template = UInt256.ofNat 824 := by decide

#print axioms run_table
#print axioms end_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.SecondSnapshotShared32
