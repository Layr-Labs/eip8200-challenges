import Challenge.Ripemd160.Submission.Proofs.Bytecode.BackwardSnapshotMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BackwardSnapshotRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory Pair13PoolRaw DenseScheduleTemplate

def firstCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 146), .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .MSTORE ]
def secondCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 178), .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 196), .op .MSTORE ]
def thirdCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 236), .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 218), .op .MSTORE ]
def fourthCopy : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 268), .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 286), .op .MSTORE ]
def copyTemplate : List Instr := firstCopy ++ secondCopy ++ thirdCopy ++ fourthCopy
def template : List Instr := copyTemplate ++ loadTemplateV2

theorem run_first (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq firstCopy {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc firstCopy
        stack := rho
        memory := BackwardSnapshotMemory.firstPrefix s.memory} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [firstCopy, BackwardSnapshotMemory.firstPrefix, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hbase, hcap, State.activeWordsAfterUInt256, hactiveAt,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_second (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq secondCopy {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc secondCopy
        stack := rho
        memory := MachineState.writeBytes s.memory (MachineState.readPadded s.memory 178 32) 196} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [secondCopy, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hbase, hcap, State.activeWordsAfterUInt256, hactiveAt,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_third (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq thirdCopy {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc thirdCopy
        stack := rho
        memory := MachineState.writeBytes s.memory (MachineState.readPadded s.memory 236 32) 218} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [thirdCopy, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hbase, hcap, State.activeWordsAfterUInt256, hactiveAt,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_fourth (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq fourthCopy {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc fourthCopy
        stack := rho
        memory := MachineState.writeBytes s.memory (MachineState.readPadded s.memory 268 32) 286} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [fourthCopy, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hbase, hcap, State.activeWordsAfterUInt256, hactiveAt,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_copy (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq copyTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc copyTemplate
        stack := rho
        memory := BackwardSnapshotMemory.copiedFour s.memory} := by
  let s1 : State := {s with memory := BackwardSnapshotMemory.firstPrefix s.memory}
  let s2 : State := {s1 with memory := MachineState.writeBytes s1.memory (MachineState.readPadded s1.memory 178 32) 196}
  let s3 : State := {s2 with memory := MachineState.writeBytes s2.memory (MachineState.readPadded s2.memory 236 32) 218}
  have h1 := run_first s pc rho hstack hrun hactive
  have h2 := run_second s1 (pcAfter pc firstCopy) rho hstack hrun hactive
  have h3 := run_third s2 (pcAfter (pcAfter pc firstCopy) secondCopy) rho hstack hrun hactive
  have h4 := run_fourth s3
    (pcAfter (pcAfter (pcAfter pc firstCopy) secondCopy) thirdCopy) rho hstack hrun hactive
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  simpa only [copyTemplate, DenseScheduleTrace.pcAfter_append, s1, s2, s3,
    BackwardSnapshotMemory.copiedFour, BackwardSnapshotMemory.thirdPrefix, BackwardSnapshotMemory.secondPrefix, BackwardSnapshotMemory.firstPrefix] using h

theorem run_load (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq loadTemplateV2 {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc loadTemplateV2
        stack := poolStack (poolWordV2 s.memory) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [loadTemplateV2, poolStack, poolWordV2, rawLoadV2, poolAddrV2,
     runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero,
     hcap, State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_actual_of_small (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := poolStack (poolWordV2 (BackwardSnapshotMemory.copiedFour s.memory)) rho
        memory := BackwardSnapshotMemory.copiedFour s.memory} := by
  let s1 : State := {s with memory := BackwardSnapshotMemory.copiedFour s.memory}
  have h1 := run_copy s pc rho hstack hrun hactive
  have h2 := run_load s1 (pcAfter pc copyTemplate) rho hstack hrun hactive
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [template, DenseScheduleTrace.pcAfter_append, s1] using h

theorem end_pc : pcAfter (UInt256.ofNat 530) template = UInt256.ofNat 608 := by decide
/-! ### Fixed-PC writer with the two padding stores exchanged -/

private theorem writer_add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b

private theorem writer_neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem writer_neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

def writerTemplate0 : List Instr := [
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 900),
  .op .MSTORE,
  .op (.Dup ⟨11, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 216),
  .op .MSTORE,
  .op (.Dup ⟨2, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 882),
  .op .MSTORE,
  .op (.Dup ⟨4, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 126),
  .op .MSTORE,
  .op (.Dup ⟨4, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 864),
  .op .MSTORE,
  .op (.Dup ⟨2, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 846),
  .op .MSTORE ]

theorem writer_run_chunk0 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 608) :
    runInstrSeq writerTemplate0 {s with pc := pc, stack := Pc792Writer.stack0 words rho} =
      some {s with
        pc := pcAfter pc writerTemplate0
        stack := Pc792Writer.outputStack0 words rho
        memory := BackwardSnapshotMemory.writerMemory0 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  have hactiveNat (address : Nat) (haddress : address ≤ 1088) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, writer_add_literals, writerTemplate0, Pc792Writer.stack0, Pc792Writer.outputStack0, BackwardSnapshotMemory.writerMemory0, BackwardSnapshotMemory.writerWrites0, Pair13WriterRaw.writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [writer_neutral_hadd, writer_neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [writer_add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem writer_run_chunk0_of_small (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 608) :
    runInstrSeq writerTemplate0 {s with pc := pc, stack := Pc792Writer.stack0 words rho} =
      some {s with
        pc := pcAfter pc writerTemplate0
        stack := Pc792Writer.outputStack0 words rho
        memory := BackwardSnapshotMemory.writerMemory0 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  have hactiveNat (address : Nat) (haddress : address ≤ 1056) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, writer_add_literals, writerTemplate0, Pc792Writer.stack0, Pc792Writer.outputStack0, BackwardSnapshotMemory.writerMemory0, BackwardSnapshotMemory.writerWrites0, Pair13WriterRaw.writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [writer_neutral_hadd, writer_neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [writer_add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

def writerTemplate3 : List Instr := [
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1062),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 972),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 648),
  .op .MSTORE,
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 630),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨3, by decide⟩ (UInt256.ofNat 612),
  .op .MSTORE,
  .op .PC,
  .op .MSTORE,
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 288),
  .op .MSTORE ]

theorem writer_run_chunk3 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 708) :
    runInstrSeq writerTemplate3 {s with pc := pc, stack := Pc792Writer.stack3 words rho} =
      some {s with
        pc := pcAfter pc writerTemplate3
        stack := Pc792Writer.outputStack3 words rho
        memory := BackwardSnapshotMemory.writerMemory3 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  have hactiveNat (address : Nat) (haddress : address ≤ 1088) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, writer_add_literals, writerTemplate3, Pc792Writer.stack3, Pc792Writer.outputStack3, BackwardSnapshotMemory.writerMemory3, BackwardSnapshotMemory.writerWrites3, Pair13WriterRaw.writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [writer_neutral_hadd, writer_neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [writer_add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
def writerTemplate : List Instr :=
  writerTemplate0 ++ Pc792Writer.template1 ++ Pc792Writer.template2 ++
    writerTemplate3 ++ Pc792Writer.template4 ++ Pc792Writer.template5

theorem run_writer (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 608) :
    runInstrSeq writerTemplate {s with
      pc := pc
      stack := Pair13PoolRaw.poolStack words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := FusedTerminalMemory.writerMemory s.memory words} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  let s0 := s
  let pc0 := pc
  have h0 := writer_run_chunk0 s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by exact hpc)
  let s1 : State := {s0 with memory := BackwardSnapshotMemory.writerMemory0 s0.memory words}
  let pc1 := pcAfter pc0 writerTemplate0
  have h1 := Pc792Writer.run_chunk1 s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := Pc792Writer.memory1 s1.memory words}
  let pc2 := pcAfter pc1 Pc792Writer.template1
  have h2 := Pc792Writer.run_chunk2 s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc2, pc1, pc0, hpc]; decide)
  let s3 : State := {s2 with memory := Pc792Writer.memory2 s2.memory words}
  let pc3 := pcAfter pc2 Pc792Writer.template2
  have h3 := writer_run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
  let s4 : State := {s3 with memory := BackwardSnapshotMemory.writerMemory3 s3.memory words}
  let pc4 := pcAfter pc3 writerTemplate3
  have h4 := Pc792Writer.run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  let s5 : State := {s4 with memory := Pc792Writer.memory4 s4.memory words}
  let pc5 := pcAfter pc4 Pc792Writer.template4
  have h5 := Pc792Writer.run_chunk5 s5 pc5 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc5, pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem := BackwardSnapshotMemory.writer_chunks_eq s.memory words
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    Pc792Writer.stack0, Pair13PoolRaw.poolStack, Pc792Writer.outputStack0, Pc792Writer.outputStack1, Pc792Writer.outputStack2,
    Pc792Writer.outputStack3, Pc792Writer.outputStack4, Pc792Writer.outputStack5, List.nil_append, hmem] using h05
theorem run_writer_grow (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) (hpc : pc = UInt256.ofNat 608) :
    runInstrSeq writerTemplate {s with
      pc := pc
      stack := Pair13PoolRaw.poolStack words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := FusedTerminalMemory.writerMemory s.memory words
        activeWords := UInt256.ofNat 35} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  have ha : 34 ≤ s.activeWords.toNat := by rw [hactive]; decide
  let s0 := s
  let pc0 := pc
  have h0 := writer_run_chunk0_of_small s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
    (by exact hpc)
  let s1 : State := {s0 with memory := BackwardSnapshotMemory.writerMemory0 s0.memory words}
  let pc1 := pcAfter pc0 writerTemplate0
  have h1 := Pc792Writer.run_chunk1_of_small s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
    (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := Pc792Writer.memory1 s1.memory words}
  let pc2 := pcAfter pc1 Pc792Writer.template1
  have h2 := Pc792Writer.run_chunk2_grow s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc2, pc1, pc0, hpc]; decide)
  let s3 : State := {s2 with memory := Pc792Writer.memory2 s2.memory words, activeWords := UInt256.ofNat 35}
  let pc3 := pcAfter pc2 Pc792Writer.template2
  have h3 := writer_run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
  let s4 : State := {s3 with memory := BackwardSnapshotMemory.writerMemory3 s3.memory words}
  let pc4 := pcAfter pc3 writerTemplate3
  have h4 := Pc792Writer.run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  let s5 : State := {s4 with memory := Pc792Writer.memory4 s4.memory words}
  let pc5 := pcAfter pc4 Pc792Writer.template4
  have h5 := Pc792Writer.run_chunk5 s5 pc5 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc5, pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem := BackwardSnapshotMemory.writer_chunks_eq s.memory words
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    Pc792Writer.stack0, Pair13PoolRaw.poolStack, Pc792Writer.outputStack0, Pc792Writer.outputStack1, Pc792Writer.outputStack2,
    Pc792Writer.outputStack3, Pc792Writer.outputStack4, Pc792Writer.outputStack5, List.nil_append, hmem] using h05
/-- Exact writer bytes from the fixed-PC guard candidate. -/
theorem writer_bytes : PcEncoding.assembleBytes writerTemplate =
    [128, 97, 3, 132, 82, 139, 96, 216, 82, 130, 97, 3, 114, 82, 132, 96, 126, 82, 132, 97, 3, 96, 82, 130, 97, 3, 78, 82, 128, 97, 3, 60, 82, 131, 97, 3, 168, 82, 131, 97, 2, 46, 82, 135, 97, 2, 28, 82, 133, 96, 108, 82, 141, 97, 2, 172, 82, 143, 88, 82, 141, 97, 1, 158, 82, 97, 2, 244, 82, 128, 97, 2, 10, 82, 141, 96, 90, 82, 135, 96, 72, 82, 96, 54, 82, 133, 97, 1, 248, 82, 131, 97, 4, 56, 82, 131, 97, 1, 230, 82, 136, 97, 4, 38, 82, 97, 3, 204, 82, 131, 97, 3, 240, 82, 131, 97, 2, 136, 82, 136, 97, 2, 118, 82, 131, 98, 0, 2, 100, 82, 88, 82, 136, 97, 1, 32, 82, 117, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 22, 97, 2, 82, 82, 136, 97, 4, 20, 82, 97, 2, 208, 82, 97, 1, 14, 82, 129, 97, 1, 140, 82, 128, 88, 82, 97, 1, 212, 82, 96, 18, 82, 97, 1, 104, 82, 96, 198, 82, 97, 1, 68, 82, 96, 252, 82, 95, 82, 97, 1, 194, 82, 96, 162, 82] := by decide

/-- The three PC-valued stores still execute at exactly 666, 738 and 792. -/
theorem writer_pc_boundaries :
    pcAfter (UInt256.ofNat 608) (writerTemplate.take 37) = UInt256.ofNat 666 ∧
    pcAfter (UInt256.ofNat 608) (writerTemplate.take 81) = UInt256.ofNat 738 ∧
    pcAfter (UInt256.ofNat 608) (writerTemplate.take 101) = UInt256.ofNat 792 := by decide

theorem writer_end_pc : pcAfter (UInt256.ofNat 608) writerTemplate = UInt256.ofNat 824 := by decide

#print axioms run_writer
#print axioms run_writer_grow
#print axioms run_copy
#print axioms run_actual_of_small
end Challenge.Ripemd160.Submission.Proofs.Bytecode.BackwardSnapshotRun
