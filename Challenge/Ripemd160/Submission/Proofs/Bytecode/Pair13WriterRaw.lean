import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory
open Pair13PoolRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

def writeChain (memory : ByteArray) (writes : List (Nat × UInt256)) : ByteArray :=
  writes.foldl (fun acc item => writeWord acc item.1 item.2) memory

def template0 : List Instr :=
  [ .op (.Dup ⟨12, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1080),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1062),
    .op .MSTORE,
    .op (.Dup ⟨15, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 1044),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 972),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 936),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 900),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 882),
    .op .MSTORE ]
def stack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3, words 9, words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3, words 9, words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def writes0 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (1080, words 5),
    (1062, words 13),
    (1044, (UInt256.mul (coefficient) (words 6))),
    (1008, (UInt256.mul (coefficient) (words 15))),
    (972, (UInt256.mul (coefficient) (words 3))),
    (936, (UInt256.mul (coefficient) (words 8))),
    (900, words 9),
    (882, words 3) ]
def memory0 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes0 words)

theorem run_chunk0 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template0 {s with pc := pc, stack := stack0 words rho} =
      some {s with pc := pcAfter pc template0, stack := outputStack0 words rho, memory := memory0 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template0, stack0, outputStack0, memory0, writes0, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk0

def template1 : List Instr :=
  [ .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 846),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 828),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 792),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 774),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 738),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 720),
    .op .MSTORE ]
def stack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3, words 9, words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def writes1 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (864, words 11),
    (846, words 3),
    (828, (UInt256.mul (coefficient) (words 9))),
    (792, words 1),
    (774, words 1),
    (756, words 9),
    (738, words 8),
    (720, (UInt256.mul (coefficient) (words 5))) ]
def memory1 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes1 words)

theorem run_chunk1 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template1 {s with pc := pc, stack := stack1 words rho} =
      some {s with pc := pcAfter pc template1, stack := outputStack1 words rho, memory := memory1 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template1, stack1, outputStack1, memory1, writes1, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.mul_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk1

def template2 : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 684),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 630),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .op (.Dup ⟨9, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 594),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 558),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE ]
def stack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def writes2 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (684, words 6),
    (666, words 14),
    (648, words 15),
    (630, words 10),
    (612, words 15),
    (594, (UInt256.mul (coefficient) (words 11))),
    (558, words 8),
    (540, words 1) ]
def memory2 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes2 words)

theorem run_chunk2 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template2 {s with pc := pc, stack := stack2 words rho} =
      some {s with pc := pcAfter pc template2, stack := outputStack2 words rho, memory := memory2 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template2, stack2, outputStack2, memory2, writes2, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk2

def template3 : List Instr :=
  [ .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 504),
    .op .MSTORE,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE,
    .op (.Dup ⟨9, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE ]
def stack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def writes3 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (522, words 0),
    (504, words 1),
    (486, words 5),
    (468, words 1),
    (450, (UInt256.mul (coefficient) (words 12))),
    (414, words 6),
    (396, (UInt256.mul (coefficient) (words 4))),
    (360, words 2) ]
def memory3 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes3 words)

theorem run_chunk3 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template3 {s with pc := pc, stack := stack3 words rho} =
      some {s with pc := pcAfter pc template3, stack := outputStack3 words rho, memory := memory3 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template3, stack3, outputStack3, memory3, writes3, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3

def template4 : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 342),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 216),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 198),
    .op .MSTORE,
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE ]
def stack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def writes4 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (342, words 2),
    (324, (UInt256.mul (coefficient) (words 10))),
    (288, words 7),
    (270, words 15),
    (252, (UInt256.mul (coefficient) (words 7))),
    (216, words 10),
    (198, (UInt256.mul (coefficient) (words 13))),
    (162, (UInt256.mul (words 14) (coefficient))) ]
def memory4 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes4 words)

theorem run_chunk4 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template4 {s with pc := pc, stack := stack4 words rho} =
      some {s with pc := pcAfter pc template4, stack := outputStack4 words rho, memory := memory4 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template4, stack4, outputStack4, memory4, writes4, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk4

def template5 : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 126),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 108),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MSTORE,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE ]
def stack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def outputStack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  rho
def writes5 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (126, words 11),
    (108, words 5),
    (90, words 12),
    (72, words 4),
    (54, words 0),
    (36, words 0),
    (18, words 4),
    (0, words 6) ]
def memory5 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes5 words)

theorem run_chunk5 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template5 {s with pc := pc, stack := stack5 words rho} =
      some {s with pc := pcAfter pc template5, stack := outputStack5 words rho, memory := memory5 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template5, stack5, outputStack5, memory5, writes5, writeChain, coefficient,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk5

def writerTemplate : List Instr := template0 ++ template1 ++ template2 ++ template3 ++ template4 ++ template5
def writerWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (1080, words 5),
    (1062, words 13),
    (1044, (UInt256.mul (coefficient) (words 6))),
    (1008, (UInt256.mul (coefficient) (words 15))),
    (972, (UInt256.mul (coefficient) (words 3))),
    (936, (UInt256.mul (coefficient) (words 8))),
    (900, words 9),
    (882, words 3),
    (864, words 11),
    (846, words 3),
    (828, (UInt256.mul (coefficient) (words 9))),
    (792, words 1),
    (774, words 1),
    (756, words 9),
    (738, words 8),
    (720, (UInt256.mul (coefficient) (words 5))),
    (684, words 6),
    (666, words 14),
    (648, words 15),
    (630, words 10),
    (612, words 15),
    (594, (UInt256.mul (coefficient) (words 11))),
    (558, words 8),
    (540, words 1),
    (522, words 0),
    (504, words 1),
    (486, words 5),
    (468, words 1),
    (450, (UInt256.mul (coefficient) (words 12))),
    (414, words 6),
    (396, (UInt256.mul (coefficient) (words 4))),
    (360, words 2),
    (342, words 2),
    (324, (UInt256.mul (coefficient) (words 10))),
    (288, words 7),
    (270, words 15),
    (252, (UInt256.mul (coefficient) (words 7))),
    (216, words 10),
    (198, (UInt256.mul (coefficient) (words 13))),
    (162, (UInt256.mul (words 14) (coefficient))),
    (126, words 11),
    (108, words 5),
    (90, words 12),
    (72, words 4),
    (54, words 0),
    (36, words 0),
    (18, words 4),
    (0, words 6) ]
def writerMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writerWrites words)

theorem run_writer (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq writerTemplate {s with pc := pc, stack := poolStack words rho} =
      some {s with pc := pcAfter pc writerTemplate, stack := rho, memory := writerMemory s.memory words} := by
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0 s0 pc0 words rho hstack hrun hactive
  let s1 := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1 s1 pc1 words rho hstack hrun hactive
  let s2 := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2 s2 pc2 words rho hstack hrun hactive
  let s3 := {s2 with memory := memory2 s2.memory words}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words rho hstack hrun hactive
  let s4 := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words rho hstack hrun hactive
  let s5 := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 words rho hstack hrun hactive
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5, stack0, poolStack, outputStack5,
    memory0, memory1, memory2, memory3, memory4, memory5, writes0, writes1, writes2, writes3, writes4, writes5,
    writerMemory, writerWrites, writeChain, List.foldl_cons, List.foldl_nil] using h05
#print axioms run_writer

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
