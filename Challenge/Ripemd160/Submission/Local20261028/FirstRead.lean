import Challenge.Ripemd160.Submission.Local20261028.FirstCore
import Challenge.Ripemd160.Submission.Local20261028.FirstInitial
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstRead
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Paired144WordRound PairedScheduleMemory
def template := (([Instr.op .JUMPDEST] ++ CoreEndian.loadDirectTemplate) ++
  (CoreEndian.stage8 true ++ CoreEndian.stage16 true)) ++ CoreEndian.lowStoreV2
def result (s : State) : State :=
  {s with memory := writeWord s.memory 252 (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1056))}
theorem run (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := UInt256.ofNat 10108, stack := FirstCore.frame cont rho} =
      some {result s with pc := UInt256.ofNat 10141, stack := FirstCore.frame cont rho} := by
  have hcap : (FirstCore.frame cont rho).length < 1024 := by
    simp only [FirstCore.frame, StaggerPersistentFrame.frame, NormalPrepare.masks,
      List.length_append, List.length_cons, List.length_nil]
    omega
  have hj : runInstrSeq [.op .JUMPDEST] {s with pc := UInt256.ofNat 10108, stack := FirstCore.frame cont rho} =
      some {s with pc := UInt256.ofNat 10109, stack := FirstCore.frame cont rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hr, hcap]
    rfl
  have hl := CoreEndian.run_loadDirect s (UInt256.ofNat 10109) factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3) (fusedCoefficientWord 0 2)
    (Word.ofUInt32 FirstCore.initialHash.h4) (Word.ofUInt32 FirstCore.initialHash.h3) (Word.ofUInt32 FirstCore.initialHash.h2)
    (Word.ofUInt32 FirstCore.initialHash.h1) (Word.ofUInt32 FirstCore.initialHash.h0)
    (UInt256.ofNat 1056) cont rho 1056 (by omega) hr rfl (by decide)
  have hactive : DenseScheduleTemplate.activeAfterWord s.activeWords (UInt256.ofNat 1056) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 1056 ha (by decide)
  rw [hactive] at hl
  have hjl := DenseScheduleTrace.runInstrSeq_append_running hj hr hl
  have hv := CoreEndian.run_reverse s (UInt256.ofNat 10111) (MachineState.readWord s.memory 1056)
    factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3) (fusedCoefficientWord 0 2)
    (Word.ofUInt32 FirstCore.initialHash.h4) (Word.ofUInt32 FirstCore.initialHash.h3) (Word.ofUInt32 FirstCore.initialHash.h2)
    (Word.ofUInt32 FirstCore.initialHash.h1) (Word.ofUInt32 FirstCore.initialHash.h0)
    (UInt256.ofNat 1056) cont rho true (by omega) hr
  have hjlv := DenseScheduleTrace.runInstrSeq_append_running hjl hr hv
  have ht := CoreEndian.run_lowStoreV2_of_small s (UInt256.ofNat 10138)
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1056)) (FirstCore.frame cont rho)
    (by simp only [FirstCore.frame, StaggerPersistentFrame.frame, NormalPrepare.masks,
          List.length_append, List.length_cons, List.length_nil]; omega) hr ha
  exact DenseScheduleTrace.runInstrSeq_append_running hjlv hr ht
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10108).take 33 = PcEncoding.assembleBytes template := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (10048+60)).take 33 = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop157]
  decide +kernel
theorem memory_eq (s : State) (m : ByteArray) (hm : s.memory = writeWord m 162 FirstInitial.highWord) :
    (result s).memory = FirstInitial.memory m := by
  simp only [result, hm, FirstInitial.memory]
  rw [read_writeWord_disjoint _ _ _ _ (Or.inr (by decide : 162+32 ≤ 1056))]
#print axioms run
#print axioms exact_bytes
#print axioms memory_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstRead
