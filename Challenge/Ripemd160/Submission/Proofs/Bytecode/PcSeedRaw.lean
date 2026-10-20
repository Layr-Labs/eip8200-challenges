import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalXorRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
open DenseScheduleTrace (runInstrSeq_append_running)

def offsets : List Nat := [968, 944, 912, 880, 848, 816, 784, 752, 720, 688, 656, 624, 592, 560, 528, 496, 464, 432, 400, 368, 336, 304, 272, 240, 208, 176, 144, 112, 80, 32]
def seed (input : ByteArray) : UInt256 :=
  UInt256.eq (MachineState.readWord input 0) (MachineState.readWord input 59)
def seedTemplate : List Instr :=
  [.op .PC, .push ⟨2, by decide⟩ 9426, .op .JUMP]
def entry59 : List Instr :=
  [.op .JUMPDEST, .op .CALLDATALOAD, .op (.Dup ⟨1, by decide⟩), .op .EQ]
def scanPrefix : List Instr :=
  entry59 ++ UnrolledRepeatRaw.scanTemplate offsets.dropLast
def terminalTemplate : List Instr :=
  [.push ⟨1, by decide⟩ 32, .op .CALLDATALOAD, .op .MUL, .op .XOR]
def template : List Instr := scanPrefix ++ terminalTemplate
def mismatch (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.mul (MachineState.readWord input 32)
    (UnrolledRepeatRaw.foldAcc input (MachineState.readWord input 0) (seed input)
      offsets.dropLast)) (MachineState.readWord input 0)

theorem run_seed (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9426 = true) :
    runInstrSeq seedTemplate {s with
      pc := UInt256.ofNat 59
      stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
    some {s with
      pc := UInt256.ofNat 9426
      stack := [UInt256.ofNat 59,
        MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hcap2 : rho.length + 1 + 1 < 1024 := by omega
  have hcap3 : rho.length + 1 + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [seedTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hcap, hcap2, hcap3, UInt256.succ, Instr.size, Word.word_toNat_ofNat,
    hv, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Word.literal_eq_ofNat]

theorem run_entry59 (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq entry59 {s with
      pc := pc
      stack := [UInt256.ofNat 59, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with
        pc := pcAfter pc entry59
        stack := [seed s.executionEnv.calldata,
          MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hcap2 : rho.length + 1 + 1 < 1024 := by omega
  have hcap3 : rho.length + 1 + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [entry59, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, hcap2, hcap3, seed, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.word_toNat_ofNat, DirectGuard.equality_comm,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Word.literal_eq_ofNat]
  repeat first | apply And.intro | rfl

theorem run_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq scanPrefix {s with
      pc := pc
      stack := [UInt256.ofNat 59, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with
        pc := pcAfter pc scanPrefix
        stack := [UnrolledRepeatRaw.foldAcc s.executionEnv.calldata
          (MachineState.readWord s.executionEnv.calldata 0)
          (seed s.executionEnv.calldata) offsets.dropLast,
          MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
  have he := run_entry59 s pc rho hs hrun
  have hc := UnrolledRepeatRaw.run_scan s
    (pcAfter pc entry59) (seed s.executionEnv.calldata)
    (MachineState.readWord s.executionEnv.calldata 0) offsets.dropLast
    (by decide) rho hs hrun
  simpa only [scanPrefix, DenseScheduleTrace.pcAfter_append] using
    runInstrSeq_append_running he hrun hc

theorem run_terminal (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq terminalTemplate {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc terminalTemplate
        stack := [UInt256.xor (UInt256.mul (MachineState.readWord s.executionEnv.calldata 32) a) r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [terminalTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, DirectGuard.xor_comm']
  repeat first | apply And.intro | rfl

theorem run (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with
      pc := UInt256.ofNat 9426
      stack := [UInt256.ofNat 59, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9632
        stack := [mismatch s.executionEnv.calldata] ++ rho} := by
  have hp := run_prefix s (UInt256.ofNat 9426) rho hs hrun
  have ht := run_terminal s (pcAfter (UInt256.ofNat 9426) scanPrefix)
    (UnrolledRepeatRaw.foldAcc s.executionEnv.calldata
      (MachineState.readWord s.executionEnv.calldata 0) (seed s.executionEnv.calldata)
      offsets.dropLast) (MachineState.readWord s.executionEnv.calldata 0) rho hs hrun
  have hpc : pcAfter (pcAfter (UInt256.ofNat 9426) scanPrefix) terminalTemplate =
    UInt256.ofNat 9632 := by decide
  simpa only [template, hpc, mismatch] using runInstrSeq_append_running hp hrun ht
#print axioms run_seed
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedRaw
