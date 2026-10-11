import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchSnapshotMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchSnapshotRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory Pair13PoolRaw DenseScheduleTemplate

def copyTemplate : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .MCOPY,
    .push ⟨1, by decide⟩ (UInt256.ofNat 178),
    .push ⟨1, by decide⟩ (UInt256.ofNat 196), .op .MCOPY,
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .push ⟨1, by decide⟩ (UInt256.ofNat 234), .op .MCOPY,
    .push ⟨2, by decide⟩ (UInt256.ofNat 268), .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 286), .op .MSTORE ]

def template : List Instr := copyTemplate ++ loadTemplateV2

theorem run_copy (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq copyTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc copyTemplate
        stack := rho
        memory := ScratchSnapshotMemory.copied32 s.memory} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  have hactiveCopy (o1 o2 : Nat) (h1 : o1 ≤ 1000) (h2 : o2 ≤ 1000) :
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat o1 16) o2 16) = s.activeWords :=
    copy_active_preserved s.activeWords o1 o2 hactive h1 h2
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [copyTemplate, ScratchSnapshotMemory.copied32, ScratchSnapshotMemory.prefixMemory, copyV2,
     runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero,
     hcap, State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
     hactiveAt, hactiveCopy, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | exact ScratchSnapshotMemory.snapshotWord _ _ _ | rfl

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
  all_goals repeat first | apply And.intro | rfl

theorem run_actual_of_small (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := poolStack (poolWordV2 (copiedV2 s.memory)) rho
        memory := ScratchSnapshotMemory.copied32 s.memory} := by
  let s1 : State := {s with memory := ScratchSnapshotMemory.copied32 s.memory}
  have h1 := run_copy s pc rho hstack hrun hactive
  have h2 := run_load s1 (pcAfter pc copyTemplate) rho hstack hrun hactive
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [template, DenseScheduleTrace.pcAfter_append, s1, ScratchSnapshotMemory.pool_eq] using h

theorem end_pc : pcAfter (UInt256.ofNat 527) template = UInt256.ofNat 606 := by decide
#print axioms run_copy
#print axioms run_actual_of_small
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchSnapshotRun
