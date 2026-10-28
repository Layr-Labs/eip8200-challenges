import Challenge.Ripemd160.Submission.Local20261028.PadTailMath
import Challenge.Ripemd160.Submission.Local20261028.Return32SerializeMath
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadOutput
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace
open RipemdTerminalMaskWindows20261027

def loadCode : List Instr := [.push ⟨1,by decide⟩ (UInt256.ofNat 16), .op .MLOAD]
def loaded (s : State) : State := {s with activeWords := s.activeWordsAfterUInt256 16 32}
def terminalCode : List Instr :=
  [.push ⟨1,by decide⟩ (UInt256.ofNat 3), .op .MSTORE,
   .push ⟨1,by decide⟩ (UInt256.ofNat 32), .push ⟨0,by decide⟩ (UInt256.ofNat 0), .op .RETURN]
def terminal (s : State) (value : UInt256) (rho : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10107
    stack := rho
    memory := Return32Finish.outputMemory s value
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      (s.activeWordsAfterUInt256 3 32).toNat 0 32)
    halt := .Returned
    hReturn := MachineState.readPadded (Return32Finish.outputMemory s value) 0 32}

theorem run_terminal (s : State) (value : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1019) (hr : s.halt = .Running) :
    runInstrSeq terminalCode {s with pc := UInt256.ofNat 10101, stack := value::rho} =
      some (terminal s value rho) := by
  have hcap (k : Nat) (hk : k ≤ 4) : rho.length+k < 1024 := by omega
  have hbase : rho.length < 1024 := by omega
  simp (discharger := omega) [terminalCode,terminal,Return32Finish.outputMemory,
    runInstrSeq,DataStepper.runInstr,pcAfter,UInt256.succ,Instr.size,hr,hcap,hbase,
    Nat.add_assoc,State.activeWordsAfterUInt256,Word.word_toNat_ofNat,Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

def template := ((PadTailRaw.template ++ after) ++ loadCode) ++ (Return32Finish.stagesCode ++ terminalCode)
def finalState (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) : State :=
  let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
  terminal (loaded (prepared s f))
    (Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Return32Output.packedHash (ScheduledTailFrame.combine h q)))
    (q.off :: Word.ofUInt32 h.h2 :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)

theorem run (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) (hs : rho.length ≤ 960) (hr : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10024 = true) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 8033, stack := ScheduledTailRaw.stack0 (ScheduledTailFrame.bind h q) (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho)} =
      some (finalState s h q rho) := by
  let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
  have hp := PadTailRaw.run s (UInt256.ofNat 8033) (ScheduledTailFrame.bind h q)
    DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 rho (by omega) hr rfl hvalid
  have ha := after_run s (UInt256.ofNat 10042) f rho (by omega) hr
  have hend : pcAfter (UInt256.ofNat 10042) after = UInt256.ofNat 10080 := by decide +kernel
  rw [hend] at ha
  have hpa := DenseScheduleTrace.runInstrSeq_append_running hp hr ha
  have hl : runInstrSeq loadCode
      {prepared s f with pc := UInt256.ofNat 10080, stack := f 19 :: f 16 :: f 21 :: f 22 :: rho} =
      some {loaded (prepared s f) with pc := UInt256.ofNat 10083, stack := Return32Output.packedHash (ScheduledTailFrame.combine h q) :: q.off :: Word.ofUInt32 h.h2 :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho} := by
    have hcap (k : Nat) (hk : k ≤ 10) : rho.length+k < 1024 := by omega
    have hpr : (prepared s f).halt = .Running := hr
    have hm := PadTailMath.read_eq s h q DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
    change MachineState.readWord (prepared s f).memory 16 = _ at hm
    simp (discharger := omega) [loadCode,loaded,runInstrSeq,DataStepper.runInstr,
      pcAfter,UInt256.succ,Instr.size,hr,hpr,hcap,Nat.add_assoc,Word.word_toNat_ofNat,
      Word.literal_eq_ofNat,hm,State.activeWordsAfterUInt256]
    all_goals repeat first | apply And.intro | rfl
  have hpal := DenseScheduleTrace.runInstrSeq_append_running hpa hr hl
  have hst := Return32Finish.run_stages (loaded (prepared s f)) (UInt256.ofNat 10083)
    (Return32Output.packedHash (ScheduledTailFrame.combine h q)) q.off (Word.ofUInt32 h.h2)
    DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 rho (by omega) hr
  have hes : pcAfter (UInt256.ofNat 10083) Return32Finish.stagesCode = UInt256.ofNat 10101 := by decide +kernel
  rw [hes] at hst
  have ht := run_terminal (loaded (prepared s f))
    (Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Return32Output.packedHash (ScheduledTailFrame.combine h q)))
    (q.off :: Word.ofUInt32 h.h2 :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)
    (by simp; omega) hr
  exact DenseScheduleTrace.runInstrSeq_append_running hpal hr
    (DenseScheduleTrace.runInstrSeq_append_running hst hr ht)

theorem hReturn_eq (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) :
    (finalState s h q rho).hReturn =
      Data.Bytes.natToBytesPadded (Return32Serialize.value (ScheduledTailFrame.combine h q)).toNat 32 := by
  change MachineState.readPadded (MachineState.writeBytes
    (prepared s (PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16)).memory
    _ 3) 0 32 = _
  rw [PadTailMath.memory_eq]
  exact Return32Finish.hReturn_eq s (ScheduledTailFrame.combine h q) (UInt256.ofNat 10101)
    (q.off :: Word.ofUInt32 h.h2 :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)

#print axioms run_terminal
#print axioms run
#print axioms hReturn_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadOutput
