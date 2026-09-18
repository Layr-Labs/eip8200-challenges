import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolRawWriter
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory
open Pair13PoolRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

open Pair13WriterRaw (writeChain)

def template0 : List Instr :=
  [ .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 126),
    .op .MSTORE,
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
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 846),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 828),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 558),
    .op .MSTORE ]

def stack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 9,
    words 0,
    words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 9,
    words 0,
    words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def writes0 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (126, words 11),
    (900, words 9),
    (216, words 10),
    (882, words 3),
    (864, words 11),
    (846, words 3),
    (828, words 9),
    (558, words 8) ]

def memory0 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes0 words)

theorem run_chunk0_of_small (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template0 {s with pc := pc, stack := stack0 words rho} =
      some {s with
        pc := pcAfter pc template0
        stack := outputStack0 words rho
        memory := memory0 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template0, stack0, outputStack0, memory0, writes0, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_chunk0 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template0 {s with pc := pc, stack := stack0 words rho} =
      some {s with
        pc := pcAfter pc template0
        stack := outputStack0 words rho
        memory := memory0 s.memory words} := by
  exact run_chunk0_of_small s pc words rho hstack hrun (by omega)

#print axioms run_chunk0

def template1 : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 684),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 936),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 108),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 792),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE ]

def stack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 9,
    words 0,
    words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 0,
    words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def writes1 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (684, words 6),
    (936, words 8),
    (108, words 5),
    (792, words 1),
    (540, words 1),
    (756, words 9),
    (522, words 0) ]

def memory1 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes1 words)

theorem run_chunk1_of_small (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template1 {s with pc := pc, stack := stack1 words rho} =
      some {s with
        pc := pcAfter pc template1
        stack := outputStack1 words rho
        memory := memory1 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template1, stack1, outputStack1, memory1, writes1, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_chunk1 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template1 {s with pc := pc, stack := stack1 words rho} =
      some {s with
        pc := pcAfter pc template1
        stack := outputStack1 words rho
        memory := memory1 s.memory words} := by
  exact run_chunk1_of_small s pc words rho hstack hrun (by omega)

#print axioms run_chunk1

def template2 : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 504),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1080),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1062),
    .op .MSTORE ]

def stack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 0,
    words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def writes2 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (90, words 12),
    (72, words 4),
    (54, words 0),
    (666, words 14),
    (504, words 1),
    (1080, words 5),
    (1062, words 13) ]

def memory2 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes2 words)

theorem run_chunk2 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template2 {s with pc := pc, stack := stack2 words rho} =
      some {s with
        pc := pcAfter pc template2
        stack := outputStack2 words rho
        memory := memory2 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template2, stack2, outputStack2, memory2, writes2, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_chunk2_grow (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    runInstrSeq template2 {s with pc := pc, stack := stack2 words rho} =
      some {s with
        pc := pcAfter pc template2
        stack := outputStack2 words rho
        memory := memory2 s.memory words
        activeWords := UInt256.ofNat 35} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template2, stack2, outputStack2, memory2, writes2, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactive, MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk2

def template3 : List Instr :=
  [ .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 972),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 630),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 738),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE ]

def stack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3,
    words 8,
    words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def writes3 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (486, words 5),
    (972, words 3),
    (648, words 15),
    (1008, words 15),
    (630, words 10),
    (612, words 15),
    (738, words 8),
    (288, words 7) ]

def memory3 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes3 words)

theorem run_chunk3 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template3 {s with pc := pc, stack := stack3 words rho} =
      some {s with
        pc := pcAfter pc template3
        stack := outputStack3 words rho
        memory := memory3 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template3, stack3, outputStack3, memory3, writes3, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3

def template4 : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 594),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1044),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 720),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE ]

def stack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 11,
    words 5,
    words 15,
    words 1,
    words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def writes4 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (594, words 11),
    (1044, words 6),
    (414, words 6),
    (720, words 5),
    (270, words 15),
    (396, words 4),
    (468, words 1) ]

def memory4 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes4 words)

theorem run_chunk4 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template4 {s with pc := pc, stack := stack4 words rho} =
      some {s with
        pc := pcAfter pc template4
        stack := outputStack4 words rho
        memory := memory4 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template4, stack4, outputStack4, memory4, writes4, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk4

def template5 : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 18),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 198),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE ]

def stack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 4,
    words 2,
    words 13,
    words 10,
    words 7,
    words 6,
    words 12,
    words 14 ] ++ rho
def outputStack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  rho
def writes5 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (18, words 4),
    (360, words 2),
    (198, words 13),
    (324, words 10),
    (252, words 7),
    (0, words 6),
    (450, words 12),
    (162, words 14) ]

def memory5 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes5 words)

theorem run_chunk5 (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template5
        {s with pc := pc, stack := stack5 words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc template5
        stack := outputStack5 words (ret :: UInt256.ofNat 4294967295 :: rest)
        memory := memory5 s.memory words} := by
  have hbase : rest.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template5, stack5, outputStack5, memory5, writes5, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk5


def writerTemplate : List Instr := template0 ++ template1 ++ template2 ++ template3 ++ template4 ++ template5

def rawWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (126, words 11),
    (900, words 9),
    (216, words 10),
    (882, words 3),
    (864, words 11),
    (846, words 3),
    (828, words 9),
    (558, words 8),
    (684, words 6),
    (936, words 8),
    (108, words 5),
    (792, words 1),
    (540, words 1),
    (756, words 9),
    (522, words 0),
    (90, words 12),
    (72, words 4),
    (54, words 0),
    (666, words 14),
    (504, words 1),
    (1080, words 5),
    (1062, words 13),
    (486, words 5),
    (972, words 3),
    (648, words 15),
    (1008, words 15),
    (630, words 10),
    (612, words 15),
    (738, words 8),
    (288, words 7),
    (594, words 11),
    (1044, words 6),
    (414, words 6),
    (720, words 5),
    (270, words 15),
    (396, words 4),
    (468, words 1),
    (18, words 4),
    (360, words 2),
    (198, words 13),
    (324, words 10),
    (252, words 7),
    (0, words 6),
    (450, words 12),
    (162, words 14) ]

def writerMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (rawWrites words)

theorem run_writer (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq writerTemplate
        {s with
          pc := pc
          stack := Pair13PoolRaw.poolStack (words) (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := writerMemory s.memory words} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0 s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1 s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2 s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s3 : State := {s2 with memory := memory2 s2.memory words}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s4 : State := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s5 : State := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 ret words rest hstack hrun hactive
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem : memory5 (memory4 (memory3 (memory2 (memory1
      (memory0 s.memory words) words) words) words) words) words
      = writerMemory s.memory words := by
    rfl
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, Pair13PoolRaw.poolStack, outputStack5, hmem] using h05
theorem run_writer_grow (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    runInstrSeq writerTemplate
        {s with
          pc := pc
          stack := Pair13PoolRaw.poolStack (words) (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := writerMemory s.memory words
        activeWords := UInt256.ofNat 35} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  have ha : 34 ≤ s.activeWords.toNat := by rw [hactive]; decide
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0_of_small s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1_of_small s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2_grow s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s3 : State := {s2 with memory := memory2 s2.memory words, activeWords := UInt256.ofNat 35}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun
    (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
  let s4 : State := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun
    (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
  let s5 : State := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 ret words rest hstack hrun
    (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem : memory5 (memory4 (memory3 (memory2 (memory1
      (memory0 s.memory words) words) words) words) words) words
      = writerMemory s.memory words := by
    rfl
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, Pair13PoolRaw.poolStack, outputStack5, hmem] using h05

theorem template_eq : writerTemplate = Pair13WriterRaw.writerTemplate := rfl
#print axioms run_writer
#print axioms run_writer_grow
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolRawWriter
