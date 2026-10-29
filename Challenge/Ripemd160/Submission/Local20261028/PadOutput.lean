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
    pc := UInt256.ofNat 10100
    stack := rho
    memory := Return32Finish.outputMemory s value
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      (s.activeWordsAfterUInt256 3 32).toNat 0 32)
    halt := .Returned
    hReturn := MachineState.readPadded (Return32Finish.outputMemory s value) 0 32}

theorem run_terminal (s : State) (value : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1019) (hr : s.halt = .Running) :
    runInstrSeq terminalCode {s with pc := UInt256.ofNat 10094, stack := value::rho} =
      some (terminal s value rho) := by
  have hcap (k : Nat) (hk : k ≤ 4) : rho.length+k < 1024 := by omega
  have hbase : rho.length < 1024 := by omega
  simp (discharger := omega) [terminalCode,terminal,Return32Finish.outputMemory,
    runInstrSeq,DataStepper.runInstr,pcAfter,UInt256.succ,Instr.size,hr,hcap,hbase,
    Nat.add_assoc,State.activeWordsAfterUInt256,Word.word_toNat_ofNat,Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

/-- The final sums are stored directly, leaving the remaining frame words on the stack. -/
def direct : List Instr :=
  [.op .ADD, .op (.Dup ⟨15,by decide⟩), .op .ADD, .op (.Swap ⟨15,by decide⟩), .op .ADD,
   .op (.Dup ⟨7,by decide⟩), .op .AND, .op (.Swap ⟨15,by decide⟩), .op .ADD,
   .push ⟨1,by decide⟩ (UInt256.ofNat 16), .op .MSTORE,
   .op (.Dup ⟨10,by decide⟩), .op .ADD, .op .ADD,
   .push ⟨1,by decide⟩ (UInt256.ofNat 12), .op .MSTORE,
   .op (.Dup ⟨9,by decide⟩), .op .ADD, .op .ADD,
   .push ⟨1,by decide⟩ (UInt256.ofNat 8), .op .MSTORE,
   .op (.Swap ⟨8,by decide⟩), .push ⟨1,by decide⟩ (UInt256.ofNat 4), .op .MSTORE,
   .op (.Swap ⟨8,by decide⟩), .push ⟨0,by decide⟩ (UInt256.ofNat 0), .op .MSTORE]
def leftover (x : Fin 23 → UInt256) (rho : List UInt256) : List UInt256 :=
  x 10 :: x 11 :: x 12 :: x 13 :: x 14 :: x 15 :: x 16 :: x 8 :: UInt256.ofNat 4294967295 ::
    x 19 :: x 20 :: x 21 :: x 22 :: rho
theorem leftover_length (x : Fin 23 → UInt256) (rho : List UInt256) :
    (leftover x rho).length = rho.length + 13 := by
  simp only [leftover, List.length_cons]
theorem direct_run (s : State) (pc : UInt256) (x : Fin 23 → UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 980) (hr : s.halt = .Running) :
    runInstrSeq direct {s with pc := pc, stack := frame x rho} =
      some {prepared s x with pc := pcAfter pc direct, stack := leftover x rho} := by
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length+n < 1024 := by omega
  simp (discharger := omega) [direct, leftover, frame, prepared, written, a, b, c, d, e,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    hr, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, State.activeWordsAfterUInt256,
    mask_first, PairedScheduleMemory.writeWord]
  all_goals repeat first | apply And.intro | rfl

/-- The two multiplication stages with the masks read from below the remaining frame words. -/
def stagesCode : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .AND,
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), .op .MUL, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 65535), .op .MUL, .op .ADD]
theorem run_stages (s : State) (pc value : UInt256) (x : Fin 23 → UInt256) (rho : List UInt256)
    (hs : rho.length < 980) (hr : s.halt = .Running) :
    runInstrSeq stagesCode {s with pc := pc, stack := value :: leftover x rho} =
      some {s with pc := pcAfter pc stagesCode, stack := Return32Finish.finish (x 21) (x 22) value :: leftover x rho} := by
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [stagesCode, leftover, Return32Finish.finish, Return32Finish.stage16,
    Return32Finish.stage8, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hr, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

def template := ((PadTailRaw.template ++ direct) ++ loadCode) ++ (stagesCode ++ terminalCode)
def finalState (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) : State :=
  let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
  terminal (loaded (prepared s f))
    (Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Return32Output.packedHash (ScheduledTailFrame.combine h q)))
    (leftover f rho)

theorem run (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) (hs : rho.length ≤ 960) (hr : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10024 = true) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 8033, stack := ScheduledTailRaw.stack0 (ScheduledTailFrame.bind h q) (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho)} =
      some (finalState s h q rho) := by
  let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
  have hp := PadTailRaw.run s (UInt256.ofNat 8033) (ScheduledTailFrame.bind h q)
    DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 rho (by omega) hr rfl hvalid
  have ha := direct_run s (UInt256.ofNat 10042) f rho (by omega) hr
  have hend : pcAfter (UInt256.ofNat 10042) direct = UInt256.ofNat 10073 := by decide +kernel
  rw [hend] at ha
  have hpa := DenseScheduleTrace.runInstrSeq_append_running hp hr ha
  have hl : runInstrSeq loadCode
      {prepared s f with pc := UInt256.ofNat 10073, stack := leftover f rho} =
      some {loaded (prepared s f) with pc := UInt256.ofNat 10076, stack := Return32Output.packedHash (ScheduledTailFrame.combine h q) :: leftover f rho} := by
    have hcap (k : Nat) (hk : k ≤ 20) : rho.length+k < 1024 := by omega
    have hpr : (prepared s f).halt = .Running := hr
    have hm := PadTailMath.read_eq s h q DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
    change MachineState.readWord (prepared s f).memory 16 = _ at hm
    simp (discharger := omega) [loadCode,loaded,runInstrSeq,DataStepper.runInstr,
      pcAfter,UInt256.succ,Instr.size,hr,hpr,hcap,Nat.add_assoc,Word.word_toNat_ofNat,
      Word.literal_eq_ofNat,hm,State.activeWordsAfterUInt256,leftover_length]
    all_goals repeat first | apply And.intro | rfl
  have hpal := DenseScheduleTrace.runInstrSeq_append_running hpa hr hl
  have hst := run_stages (loaded (prepared s f)) (UInt256.ofNat 10076)
    (Return32Output.packedHash (ScheduledTailFrame.combine h q)) f rho (by omega) hr
  have hes : pcAfter (UInt256.ofNat 10076) stagesCode = UInt256.ofNat 10094 := by decide +kernel
  have h21 : f 21 = DenseScheduleTemplate.mask8 := rfl
  have h22 : f 22 = DenseScheduleTemplate.mask16 := rfl
  rw [hes, h21, h22] at hst
  have ht := run_terminal (loaded (prepared s f))
    (Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Return32Output.packedHash (ScheduledTailFrame.combine h q)))
    (leftover f rho) (by rw [leftover_length]; omega) hr
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
  exact Return32Finish.hReturn_eq s (ScheduledTailFrame.combine h q) (UInt256.ofNat 10094)
    (leftover (PadTailRaw.fields (ScheduledTailFrame.bind h q) DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16) rho)

#print axioms direct_run
#print axioms run_stages
#print axioms run_terminal
#print axioms run
#print axioms hReturn_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadOutput
