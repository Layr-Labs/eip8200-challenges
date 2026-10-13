import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory Pair13PoolRaw DenseScheduleTemplate

def firstCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .MCOPY ]
def secondCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 178), .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 196), .op .MSTORE ]
def thirdCopy : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .push ⟨1, by decide⟩ (UInt256.ofNat 234), .op .MCOPY ]
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
        stack := UInt256.ofNat 16 :: rho
        memory := copyV2 s.memory 162 144} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveCopy (o1 o2 : Nat) (h1 : o1 ≤ 1000) (h2 : o2 ≤ 1000) :
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat o1 16) o2 16) = s.activeWords :=
    copy_active_preserved s.activeWords o1 o2 hactive h1 h2
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [firstCopy, copyV2, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hbase, hcap, State.activeWordsAfterUInt256_2, hactiveCopy,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

theorem run_second (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 901) (hrun : s.halt = .Running)
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
    runInstrSeq thirdCopy {s with pc := pc, stack := UInt256.ofNat 16 :: rho} =
      some {s with
        pc := pcAfter pc thirdCopy
        stack := rho
        memory := copyV2 s.memory 252 234} := by
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveCopy (o1 o2 : Nat) (h1 : o1 ≤ 1000) (h2 : o2 ≤ 1000) :
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat o1 16) o2 16) = s.activeWords :=
    copy_active_preserved s.activeWords o1 o2 hactive h1 h2
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [thirdCopy, copyV2, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
     Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun,
     hcap, State.activeWordsAfterUInt256_2, hactiveCopy,
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
        memory := SecondSnapshotCertificates.copiedTwo s.memory} := by
  let s1 : State := {s with memory := copyV2 s.memory 162 144}
  let s2 : State := {s1 with memory := MachineState.writeBytes s1.memory (MachineState.readPadded s1.memory 178 32) 196}
  let s3 : State := {s2 with memory := copyV2 s2.memory 252 234}
  have h1 := run_first s pc rho hstack hrun hactive
  have h2 := run_second s1 (pcAfter pc firstCopy) (UInt256.ofNat 16 :: rho)
    (by simp; omega) hrun hactive
  have h3 := run_third s2 (pcAfter (pcAfter pc firstCopy) secondCopy) rho hstack hrun hactive
  have h4 := run_fourth s3
    (pcAfter (pcAfter (pcAfter pc firstCopy) secondCopy) thirdCopy) rho hstack hrun hactive
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  simpa only [copyTemplate, DenseScheduleTrace.pcAfter_append, s1, s2, s3,
    SecondSnapshotCertificates.copiedTwo, SecondSnapshotCertificates.secondPrefix] using h

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
    (hr : SecondSnapshotCertificates.Repeat4 s.memory)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := poolStack (poolWordV2 (copiedV2 s.memory)) rho
        memory := SecondSnapshotCertificates.copiedTwo s.memory} := by
  let s1 : State := {s with memory := SecondSnapshotCertificates.copiedTwo s.memory}
  have h1 := run_copy s pc rho hstack hrun hactive
  have h2 := run_load s1 (pcAfter pc copyTemplate) rho hstack hrun hactive
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [template, DenseScheduleTrace.pcAfter_append, s1, SecondSnapshotCertificates.second_pool_eq s.memory hr, ScratchSnapshotMemory.pool_eq] using h

theorem end_pc : pcAfter (UInt256.ofNat 528) template = UInt256.ofNat 607 := by decide
#print axioms run_copy
#print axioms run_actual_of_small
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotRun
