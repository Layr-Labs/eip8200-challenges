import Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalWriter
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory Pair13PoolRaw
open PoolRawWriter (template0 template1 template2 template5 memory0 memory1 memory2 memory5 writes0 writes1 writes2 writes5 stack0 stack4 outputStack4 outputStack5 run_chunk0 run_chunk1 run_chunk2 run_chunk5 run_chunk0_of_small run_chunk1_of_small run_chunk2_grow)
open Pair13WriterRaw (writeChain)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
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
    .push ⟨3, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .op .PC,
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
  have hactivePC : MachineState.activeWordsAfter s.activeWords.toNat 738 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 738 (by decide))
  norm_num [UInt256.size] at hactivePC
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template3, stack3, outputStack3, memory3, writes3, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactivePC, hactiveAt]
  all_goals try (rw [hactivePC]; exact hactiveAt 288 (by decide))
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3


def template4 : List Instr :=
  [ .push ⟨22, by decide⟩ poolMask,
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 594),
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

def writes4 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (594, UInt256.land poolMask (words 11)),
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
    runInstrSeq template4 {s with pc := pc, stack := PoolRawWriter.stack4 words rho} =
      some {s with
        pc := pcAfter pc template4
        stack := PoolRawWriter.outputStack4 words rho
        memory := memory4 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template4, PoolRawWriter.stack4, PoolRawWriter.outputStack4, memory4, writes4, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk4


def writerTemplate : List Instr := template0 ++ template1 ++ template2 ++ template3 ++ template4 ++ template5
theorem run_writer (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 606) :
    runInstrSeq writerTemplate
        {s with
          pc := pc
          stack := Pair13PoolRaw.poolStack (words) (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := FusedTerminalMemory.writerMemory s.memory words} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0 s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1 s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2 s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s3 : State := {s2 with memory := memory2 s2.memory words}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
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
      = FusedTerminalMemory.writerMemory s.memory words := by
    simp only [memory0, memory1, memory2, memory3, memory4, memory5,
      writes0, writes1, writes2, writes3, writes4, writes5,
      writeChain, List.foldl_cons, List.foldl_nil]
    simp only [FusedTerminalMemory.writerMemory, PoolShape.writes, FusedTerminalMemory.storedWord, writeChain, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    norm_num only
    simp only [if_false, if_true]
    rw [Pair13WriterRaw.writeWord_comm _ 666 540 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 756 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 522 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 90 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 72 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 54 _ _ (by decide)]
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, Pair13PoolRaw.poolStack, outputStack5, hmem] using h05
theorem run_writer_grow (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34) (hpc : pc = UInt256.ofNat 606) :
    runInstrSeq writerTemplate
        {s with
          pc := pc
          stack := Pair13PoolRaw.poolStack (words) (ret :: UInt256.ofNat 4294967295 :: rest)} =
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
  have h0 := run_chunk0_of_small s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1_of_small s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun ha (by simp only [pc1, pc0, hpc]; decide)
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2_grow s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s3 : State := {s2 with memory := memory2 s2.memory words, activeWords := UInt256.ofNat 35}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun
    (by change 35 ≤ (UInt256.ofNat 35).toNat; decide) (by simp only [pc3, pc2, pc1, pc0, hpc]; decide)
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
      = FusedTerminalMemory.writerMemory s.memory words := by
    simp only [memory0, memory1, memory2, memory3, memory4, memory5,
      writes0, writes1, writes2, writes3, writes4, writes5,
      writeChain, List.foldl_cons, List.foldl_nil]
    simp only [FusedTerminalMemory.writerMemory, PoolShape.writes, FusedTerminalMemory.storedWord, writeChain, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    norm_num only
    simp only [if_false, if_true]
    rw [Pair13WriterRaw.writeWord_comm _ 666 540 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 756 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 522 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 90 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 72 _ _ (by decide),
      Pair13WriterRaw.writeWord_comm _ 666 54 _ _ (by decide)]
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, Pair13PoolRaw.poolStack, outputStack5, hmem] using h05


#print axioms run_writer
#print axioms run_writer_grow
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalWriter
