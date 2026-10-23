import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pc792Writer
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory HoistedInherited.Pair13PoolRaw
open HoistedInherited.Pair13WriterRaw (writeChain)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b

def template0 : List Instr := [
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 900),
  .op .MSTORE,
  .op (.Dup ⟨6, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
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
def stack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 9, words 0, words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 9, words 0, words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def writes0 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (900, words 9),
  (1008, words 15),
  (882, words 3),
  (126, words 11),
  (864, words 11),
  (846, words 3) ]
def memory0 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes0 words)
theorem run_chunk0 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 607) :
    runInstrSeq template0 {s with pc := pc, stack := stack0 words rho} =
      some {s with
        pc := pcAfter pc template0
        stack := outputStack0 words rho
        memory := memory0 s.memory words} := by
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
    [hpc, add_literals, template0, stack0, outputStack0, memory0, writes0, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk0

def template1 : List Instr := [
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 828),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 936),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 558),
  .op .MSTORE,
  .op (.Dup ⟨7, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 540),
  .op .MSTORE,
  .op (.Dup ⟨5, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 108),
  .op .MSTORE,
  .op (.Dup ⟨13, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 684),
  .op .MSTORE,
  .op (.Dup ⟨15, by decide⟩),
  .op .PC,
  .op .MSTORE,
  .op (.Dup ⟨13, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 414),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 756),
  .op .MSTORE,
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 522),
  .op .MSTORE ]
def stack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 9, words 0, words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 0, words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def writes1 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (828, words 9),
  (936, words 8),
  (558, words 8),
  (540, words 1),
  (108, words 5),
  (684, words 6),
  (666, words 14),
  (414, words 6),
  (756, words 9),
  (522, words 0) ]
def memory1 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes1 words)
theorem run_chunk1 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 636) :
    runInstrSeq template1 {s with pc := pc, stack := stack1 words rho} =
      some {s with
        pc := pcAfter pc template1
        stack := outputStack1 words rho
        memory := memory1 s.memory words} := by
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
    [hpc, add_literals, template1, stack1, outputStack1, memory1, writes1, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk1

def template2 : List Instr := [
  .op (.Dup ⟨13, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 90),
  .op .MSTORE,
  .op (.Dup ⟨7, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 72),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 54),
  .op .MSTORE,
  .op (.Dup ⟨5, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 504),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1080),
  .op .MSTORE,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 486),
  .op .MSTORE ]
def stack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 0, words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def writes2 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (90, words 12),
  (72, words 4),
  (54, words 0),
  (504, words 1),
  (1080, words 5),
  (486, words 5) ]
def memory2 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes2 words)
theorem run_chunk2 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 682) :
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
  have hactiveNat (address : Nat) (haddress : address ≤ 1088) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template2, stack2, outputStack2, memory2, writes2, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk2

def template3 : List Instr := [
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1062),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 972),
  .op .MSTORE,
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 216),
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
def stack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 3, words 8, words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def writes3 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (1062, words 13),
  (972, words 3),
  (216, words 10),
  (648, words 15),
  (630, words 10),
  (612, words 15),
  (738, words 8),
  (288, words 7) ]
def memory3 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes3 words)
theorem run_chunk3 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 708) :
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
  have hactiveNat (address : Nat) (haddress : address ≤ 1088) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template3, stack3, outputStack3, memory3, writes3, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3

def template4 : List Instr := [
  .push ⟨22, by decide⟩ poolMask,
  .op .AND,
  .push ⟨2, by decide⟩ (UInt256.ofNat 594),
  .op .MSTORE,
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 1044),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 720),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 270),
  .op .MSTORE,
  .op (.Dup ⟨1, by decide⟩),
  .push ⟨2, by decide⟩ (UInt256.ofNat 396),
  .op .MSTORE,
  .op (.Dup ⟨0, by decide⟩),
  .op .PC,
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 468),
  .op .MSTORE ]
def stack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 11, words 5, words 15, words 1, words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def writes4 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (594, UInt256.land poolMask (words 11)),
  (1044, words 6),
  (720, words 5),
  (270, words 15),
  (396, words 4),
  (792, words 1),
  (468, words 1) ]
def memory4 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes4 words)
theorem run_chunk4 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 745) :
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
  have hactiveNat (address : Nat) (haddress : address ≤ 1088) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template4, stack4, outputStack4, memory4, writes4, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk4

def template5 : List Instr := [
  .push ⟨1, by decide⟩ (UInt256.ofNat 18),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 360),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 198),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 324),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 252),
  .op .MSTORE,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .MSTORE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 450),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 162),
  .op .MSTORE ]
def stack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14] ++ rho
def outputStack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 := [] ++ rho
def writes5 (words : Nat → UInt256) : List (Nat × UInt256) := [
  (18, words 4),
  (360, words 2),
  (198, words 13),
  (324, words 10),
  (252, words 7),
  (0, words 6),
  (450, words 12),
  (162, words 14) ]
def memory5 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes5 words)
theorem run_chunk5 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 798) :
    runInstrSeq template5 {s with pc := pc, stack := stack5 words rho} =
      some {s with
        pc := pcAfter pc template5
        stack := outputStack5 words rho
        memory := memory5 s.memory words} := by
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
    [hpc, add_literals, template5, stack5, outputStack5, memory5, writes5, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk5

theorem run_chunk0_of_small (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 607) :
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
  have hactiveNat (address : Nat) (haddress : address ≤ 1056) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template0, stack0, outputStack0, memory0, writes0, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_chunk0_of_small

theorem run_chunk1_of_small (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 636) :
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
  have hactiveNat (address : Nat) (haddress : address ≤ 1056) :
      MachineState.activeWordsAfter s.activeWords.toNat address 32 % UInt256.size = s.activeWords.toNat :=
    congrArg UInt256.toNat (hactiveAt address haddress)
  norm_num [UInt256.size] at hactiveNat
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template1, stack1, outputStack1, memory1, writes1, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactiveNat, hactiveAt]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_chunk1_of_small

theorem run_chunk2_grow (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) (hpc : pc = UInt256.ofNat 682) :
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
    [hpc, add_literals, template2, stack2, outputStack2, memory2, writes2, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactive, MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactive, MachineState.activeWordsAfter]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_chunk2_grow

def writerTemplate : List Instr := template0 ++ template1 ++ template2 ++ template3 ++ template4 ++ template5
def rawWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  writes0 words ++ writes1 words ++ writes2 words ++ writes3 words ++ writes4 words ++ writes5 words

def maskedG (words : Nat → UInt256) (x : Nat × Nat) : Nat × UInt256 :=
  (x.1, HoistedInherited.FusedTerminalMemory.storedWord words x)
@[simp] theorem maskedG_fst (words : Nat → UInt256) (x : Nat × Nat) :
    (maskedG words x).1 = x.1 := rfl

theorem ins_map_masked (words : Nat → UInt256) (x : Nat × Nat) (l : List (Nat × Nat)) :
    HoistedInherited.Pair13WriterRaw.ins (maskedG words x) (l.map (maskedG words)) =
      (HoistedInherited.Pair13WriterRaw.insP x l).map (maskedG words) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y.1 < x.1
    · simp only [List.map_cons, HoistedInherited.Pair13WriterRaw.ins, HoistedInherited.Pair13WriterRaw.insP, maskedG_fst, if_pos h]
    · simp only [List.map_cons, HoistedInherited.Pair13WriterRaw.ins, HoistedInherited.Pair13WriterRaw.insP, maskedG_fst, if_neg h, ih]

theorem isort_map_masked (words : Nat → UInt256) (l : List (Nat × Nat)) :
    HoistedInherited.Pair13WriterRaw.isort (l.map (maskedG words)) =
      (HoistedInherited.Pair13WriterRaw.isortP l).map (maskedG words) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, HoistedInherited.Pair13WriterRaw.isort, HoistedInherited.Pair13WriterRaw.isortP, ih, ins_map_masked]

def rawKeys : List (Nat × Nat) := [(900,9), (1008,15), (882,3), (126,11), (864,11), (846,3), (828,9), (936,8), (558,8), (540,1), (108,5), (684,6), (666,14), (414,6), (756,9), (522,0), (90,12), (72,4), (54,0), (504,1), (1080,5), (486,5), (1062,13), (972,3), (216,10), (648,15), (630,10), (612,15), (738,8), (288,7), (594,11), (1044,6), (720,5), (270,15), (396,4), (792,1), (468,1), (18,4), (360,2), (198,13), (324,10), (252,7), (0,6), (450,12), (162,14)]
theorem rawWrites_eq_masked (words : Nat → UInt256) :
    rawWrites words = rawKeys.map (maskedG words) := by rfl

theorem sorted_keys : HoistedInherited.Pair13WriterRaw.isortP rawKeys =
    HoistedInherited.Pair13WriterRaw.isortP HoistedInherited.PoolShape.writes := by decide

theorem memory_eq (memory : ByteArray) (words : Nat → UInt256) :
    writeChain memory (rawWrites words) = HoistedInherited.FusedTerminalMemory.writerMemory memory words := by
  have hnew : HoistedInherited.Pair13WriterRaw.isortOKN ((rawWrites words).map Prod.fst) = true := by
    change HoistedInherited.Pair13WriterRaw.isortOKN [900, 1008, 882, 126, 864, 846, 828, 936, 558, 540, 108, 684, 666, 414, 756, 522, 90, 72, 54, 504, 1080, 486, 1062, 972, 216, 648, 630, 612, 738, 288, 594, 1044, 720, 270, 396, 792, 468, 18, 360, 198, 324, 252, 0, 450, 162] = true
    decide
  have hold : HoistedInherited.Pair13WriterRaw.isortOKN ((HoistedInherited.PoolShape.writes.map (maskedG words)).map Prod.fst) = true := by
    change HoistedInherited.Pair13WriterRaw.isortOKN [126, 900, 216, 882, 864, 846, 828, 558, 684, 936, 108, 792, 540, 756, 522, 90, 72, 54, 666, 504, 1080, 1062, 486, 972, 648, 1008, 630, 612, 738, 288, 594, 1044, 414, 720, 270, 396, 468, 18, 360, 198, 324, 252, 0, 450, 162] = true
    decide
  change writeChain memory (rawWrites words) = writeChain memory (HoistedInherited.PoolShape.writes.map (maskedG words))
  rw [HoistedInherited.Pair13WriterRaw.chain_isort memory _ hnew, rawWrites_eq_masked,
      isort_map_masked, sorted_keys, ← isort_map_masked,
      ← HoistedInherited.Pair13WriterRaw.chain_isort memory _ hold]

theorem run_writer (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 607) :
    runInstrSeq writerTemplate {s with
      pc := pc
      stack := HoistedInherited.Pair13PoolRaw.poolStack words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := HoistedInherited.FusedTerminalMemory.writerMemory s.memory words} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0 s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by exact hpc)
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1 s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2 s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc2, pc1, pc0, hpc]; decide)
  let s3 : State := {s2 with memory := memory2 s2.memory words}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
  let s4 : State := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  let s5 : State := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc5, pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem : memory5 (memory4 (memory3 (memory2 (memory1
      (memory0 s.memory words) words) words) words) words) words =
      HoistedInherited.FusedTerminalMemory.writerMemory s.memory words := by
    rw [← memory_eq]
    simp only [memory0, memory1, memory2, memory3, memory4, memory5, rawWrites,
      writes0, writes1, writes2, writes3, writes4, writes5, writeChain,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, HoistedInherited.Pair13PoolRaw.poolStack, outputStack0, outputStack1, outputStack2,
    outputStack3, outputStack4, outputStack5, List.nil_append, hmem] using h05
#print axioms run_writer

theorem run_writer_grow (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) (hpc : pc = UInt256.ofNat 607) :
    runInstrSeq writerTemplate {s with
      pc := pc
      stack := HoistedInherited.Pair13PoolRaw.poolStack words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := HoistedInherited.FusedTerminalMemory.writerMemory s.memory words
        activeWords := UInt256.ofNat 35} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  have ha : 34 ≤ s.activeWords.toNat := by rw [hactive]; decide
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0_of_small s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
    (by exact hpc)
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1_of_small s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
    (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2_grow s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
    (by simp only [pc2, pc1, pc0, hpc]; decide)
  let s3 : State := {s2 with memory := memory2 s2.memory words, activeWords := UInt256.ofNat 35}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
  let s4 : State := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  let s5 : State := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun (by change 35 ≤ (UInt256.ofNat 35).toNat; decide)
    (by simp only [pc5, pc4, pc3, pc2, pc1, pc0, hpc]; decide)
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem : memory5 (memory4 (memory3 (memory2 (memory1
      (memory0 s.memory words) words) words) words) words) words =
      HoistedInherited.FusedTerminalMemory.writerMemory s.memory words := by
    rw [← memory_eq]
    simp only [memory0, memory1, memory2, memory3, memory4, memory5, rawWrites,
      writes0, writes1, writes2, writes3, writes4, writes5, writeChain,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, HoistedInherited.Pair13PoolRaw.poolStack, outputStack0, outputStack1, outputStack2,
    outputStack3, outputStack4, outputStack5, List.nil_append, hmem] using h05
#print axioms run_writer_grow

theorem exact_bytes : PcEncoding.assembleBytes writerTemplate = [128,97,3,132,82,134,97,3,240,82,130,97,3,114,82,132,96,126,82,132,97,3,96,82,130,97,3,78,82,128,97,3,60,82,131,97,3,168,82,131,97,2,46,82,135,97,2,28,82,133,96,108,82,141,97,2,172,82,143,88,82,141,97,1,158,82,97,2,244,82,128,97,2,10,82,141,96,90,82,135,96,72,82,96,54,82,133,97,1,248,82,131,97,4,56,82,131,97,1,230,82,136,97,4,38,82,97,3,204,82,136,97,0,216,82,131,97,2,136,82,136,97,2,118,82,131,98,0,2,100,82,88,82,136,97,1,32,82,117,255,255,255,255,0,0,0,0,0,0,0,0,0,0,0,0,0,0,255,255,255,255,22,97,2,82,82,136,97,4,20,82,97,2,208,82,97,1,14,82,129,97,1,140,82,128,88,82,97,1,212,82,96,18,82,97,1,104,82,96,198,82,97,1,68,82,96,252,82,95,82,97,1,194,82,96,162,82] := by decide
theorem end_pc : pcAfter (UInt256.ofNat 607) writerTemplate = UInt256.ofNat 824 := by decide
#print axioms memory_eq
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Pc792Writer
