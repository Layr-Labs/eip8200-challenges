import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace RipemdSubmissionTables20261028
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace

private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a+b) := by
  apply Word.word_ext
  change (a % 2^256 + b % 2^256) % 2^256 = (a+b) % 2^256
  exact (Nat.add_mod a b (2^256)).symm

private theorem hadd_literals (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a+b) := add_literals a b

private theorem active_preserved35 (current : UInt256) (address : Nat)
    (hc : 35 ≤ current.toNat) (ha : address ≤ 1088) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

private theorem active_preserved34 (current : UInt256) (address : Nat)
    (hc : 34 ≤ current.toNat) (ha : address ≤ 1056) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

namespace General0
def template : List Instr := [
    .push ⟨1, by decide⟩ (UInt256.ofNat 146),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 178),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 196),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 236),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 218),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((MachineState.readWord (s.memory) 146)))) 196 ((MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((MachineState.readWord (s.memory) 146)))) 178)))) 218 ((MachineState.readWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((MachineState.readWord (s.memory) 146)))) 196 ((MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((MachineState.readWord (s.memory) 146)))) 178)))) 236)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 530).take 18 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+18)).take 18 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 530), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 548), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General0

namespace General1
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 268),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 286),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 232),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 262),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 266),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 180),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 138),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 236),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 168),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 228),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 142),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 134),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 258),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 146),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 176),
    .op .MLOAD,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 828),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [(MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 176), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 224), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 172), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 146), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 258), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 134), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 142), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 228), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 168), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 236), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 138), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 180), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 266), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 262), (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 828 ((MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 286 ((MachineState.readWord (s.memory) 268)))) 236)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 548).take 61 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+36)).take 61 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 548), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 609), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General1

namespace General2
def template : List Instr := [
    .op (.Dup ⟨12, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 684),
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 108),
    .op .MSTORE,
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28, x 29] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28, x 29] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 684 (x 12))) 666 (x 11))) 108 (x 4))) 648 (x 6))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 609).take 21 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (576+33)).take 21 = _
  rw [← List.drop_drop, CandidateBytes.drop9]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 609), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 630), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General2

namespace General3
def template : List Instr := [
    .op .PC,
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 558),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28, x 29] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28, x 29] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 630 (x 0))) 18 (x 12))) 558 (x 5))) 414 (x 4))) 540 (x 7))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 630).take 21 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (576+54)).take 21 = _
  rw [← List.drop_drop, CandidateBytes.drop9]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 630), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 651), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General3

namespace General4
def template : List Instr := [
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 216),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 252 (x 5))) 522 (x 0))) 90 (x 0))) 216 (x 1))) 72 (x 3))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 651).take 19 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (640+11)).take 19 = _
  rw [← List.drop_drop, CandidateBytes.drop10]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 651), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 670), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General4

namespace General5
def template : List Instr := [
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 594),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 846),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 936),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 972),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 594 (x 0))) 846 (x 0))) 54 (x 5))) 936 (x 2))) 972 (x 6))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 670).take 23 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (640+30)).take 23 = _
  rw [← List.drop_drop, CandidateBytes.drop10]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 670), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 693), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General5

namespace General6
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .push ⟨4, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .push ⟨32, by decide⟩ (UInt256.ofNat 198),
    .op .MSTORE,
    .op (.Dup ⟨6, by decide⟩),
    .op .PC,
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 504),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 360 (x 0))) 756 (x 1))) 198 (x 2))) 738 (x 9))) 504 (x 3))) 486 (x 4))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 693).take 56 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (640+53)).take 56 = _
  rw [← List.drop_drop, CandidateBytes.drop10]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 693), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 749), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General6

namespace General7
def template : List Instr := [
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨5, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE,
    .push ⟨32, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .op .PC,
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 468 (x 5))) 450 (x 0))) 792 (x 2))) 864 (x 1))) 1008 (x 3))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 749).take 54 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (704+45)).take 54 = _
  rw [← List.drop_drop, CandidateBytes.drop11]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 749), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 803), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General7

namespace General8
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 900),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 720),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 900 (x 0))) 612 (x 1))) 396 (x 2))) 720 (x 3))) 324 (x 4))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 803).take 20 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (768+35)).take 20 = _
  rw [← List.drop_drop, CandidateBytes.drop12]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 803), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 823), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved35 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end General8

end RipemdSubmissionTables20261028
