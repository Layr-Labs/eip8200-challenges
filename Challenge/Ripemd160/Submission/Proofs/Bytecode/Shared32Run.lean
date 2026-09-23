import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch

def template : List Instr :=
  ((Shared32Lower.lowerTemplate ++ Pair13PoolRaw.templateV2) ++ Pair13WriterRaw.writerTemplate) ++
    Pair13NormalTrace.clearTemplate

theorem run_table (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    runInstrSeq template
      {s with
        pc := pc
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := writeWord s.memory 162 highWord} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := Shared32Table.tableMemory s.memory
        activeWords := UInt256.ofNat 35} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: UInt256.ofNat 0 :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
    (UInt256.ofNat 0) lim rho
  let scratch := Pair13Endian.scratchV2 s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1056)) highWord
  let s1 : State := {s with memory := writeWord s.memory 162 highWord}
  let s2 : State := {s with memory := scratch}
  let s3 : State := {s with memory := Pair13PoolRaw.copiedV2 scratch}
  have ha : 34 ≤ s2.activeWords.toNat := by change 34 ≤ s.activeWords.toNat; rw [hactive]; decide
  have ha3 : s3.activeWords = UInt256.ofNat 34 := hactive
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have h1 := Shared32Lower.run_lower s1 pc ret (UInt256.ofNat 4294967295)
    a2 a3 a4 a5 a6 a7 a8 a9 a10 lim rho hstack hrun hactive
  have hread : MachineState.readWord s1.memory 1056 = MachineState.readWord s.memory 1056 :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))
  rw [hread] at h1
  have h2 := Pair13PoolRaw.run_actualV2_of_small s2 (pcAfter pc Shared32Lower.lowerTemplate) F hF hrun ha
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := PoolRawWriter.run_writer_grow s3
    (pcAfter (pcAfter pc Shared32Lower.lowerTemplate) Pair13PoolRaw.templateV2)
    ret (Pair13PoolRaw.poolWordV2 (Pair13PoolRaw.copiedV2 scratch)) rest hrest hrun ha3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := Pair13NormalTrace.run_clear
    {s3 with
      memory := (PoolRawWriter.writerMemory s3.memory (Pair13PoolRaw.poolWordV2 (Pair13PoolRaw.copiedV2 scratch)))
      activeWords := UInt256.ofNat 35}
    (pcAfter (pcAfter (pcAfter pc Shared32Lower.lowerTemplate) Pair13PoolRaw.templateV2)
      PoolRawWriter.writerTemplate)
    (ret :: UInt256.ofNat 4294967295 :: rest) (by simp only [List.length_cons]; omega) hrun
    (by show 20 ≤ (UInt256.ofNat 35).toNat; decide)
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  simpa only [PoolRawWriter.template_eq, template, DenseScheduleTrace.pcAfter_append,
    s3, s2, s1, scratch, Shared32Table.tableMemory, PoolShapeV2.resultMemoryV2, PoolShapeV2.fanMemoryV2, rest, stk] using h

theorem end_pc : pcAfter (UInt256.ofNat 813) template = UInt256.ofNat 1130 := by decide

#print axioms run_table
#print axioms end_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
