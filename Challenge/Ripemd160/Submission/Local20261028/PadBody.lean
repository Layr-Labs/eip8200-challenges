import Challenge.Ripemd160.Submission.Local20261028.PadPrologue
import Challenge.Ripemd160.Submission.Local20261028.PadEpilogue
import Challenge.Ripemd160.Submission.Local20261028.PadTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadBody
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace PadCommon PadFunctional
def template := ((PadPrologue.template ++ PadComposition.block 77) ++ PadEpilogue.template) ++ PadOutput.template
theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := by
  simp only [StaggerRepresentation.word_ofUInt32]
  rfl
theorem entry_eq (len : UInt256) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) :
    StaggerPersistentFrame.frame h off limit rho =
      stack len (initial h).e [.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.e]
        (initial h) (initial h) (UInt256.ofNat 1352829926) (PadCorePack.suffix (initial h) off limit rho) := by
  rw [initial_eq]
  rfl
theorem tail_eq (s : State) (len : UInt256) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    PadEpilogue.result s len (initial h).e q (PadCorePack.suffix (initial h) off limit rho) =
      {s with pc := UInt256.ofNat 8033, stack := ScheduledTailRaw.stack0 (ScheduledTailFrame.bind h (PadTail.tailInput len h (PadCoreLeft79.epilogueRaw len q) q off limit)) rho} := by
  rw [initial_eq]
  rfl
def finalState (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) : State :=
  let q := PadModel.paired len (initial h)
  PadOutput.finalState s h (PadTail.tailInput len h (PadCoreLeft79.epilogueRaw len q) q off limit) rho

theorem run (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 892) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162)
    (hv1 : Decode.isValidJumpDest s.executionEnv.code 4601 = true)
    (hv2 : Decode.isValidJumpDest s.executionEnv.code 10024 = true) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 89, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho)} =
      some (finalState s len h off limit rho) := by
  let suffix := DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho
  have hlen : (PadCorePack.suffix (initial h) off limit suffix).length ≤ 900 := by
    simp only [PadCorePack.suffix, suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have hp := PadPrologue.run s len (initial h) off limit suffix (by simp [suffix]; omega)
    hr ha hcal hmem hv1
  rw [← entry_eq] at hp
  have hm := PadComposition.run_block s len (initial h).e
    (PadModel.pair (initial h) (PadModel.prologue len (initial h)))
    (initial h) (PadCorePack.suffix (initial h) off limit suffix) hlen hr ha hcal hmem 77 (by decide)
  have hpm := DenseScheduleTrace.runInstrSeq_append_running hp hr hm
  have he := PadEpilogue.run s len (initial h).e (PadModel.paired len (initial h))
    (initial h) (PadCorePack.suffix (initial h) off limit suffix) hlen hr ha
  have hpme := DenseScheduleTrace.runInstrSeq_append_running hpm hr he
  rw [tail_eq] at hpme
  have ht := PadOutput.run s h
    (PadTail.tailInput len h (PadCoreLeft79.epilogueRaw len (PadModel.paired len (initial h)))
      (PadModel.paired len (initial h)) off limit) rho (by omega) hr hv2
  exact DenseScheduleTrace.runInstrSeq_append_running hpme hr ht

theorem hReturn_eq (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) :
    (finalState s len h off limit rho).hReturn =
      Data.Bytes.natToBytesPadded (Return32Serialize.value (PadFunctional.result len h)).toNat 32 := by
  rw [finalState, PadOutput.hReturn_eq, PadTail.combine_eq]
  rfl

#print axioms run
#print axioms hReturn_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadBody
