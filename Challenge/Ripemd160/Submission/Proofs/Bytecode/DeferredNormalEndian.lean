import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZeroEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PairTableMemory PairTableActive Table80ScratchZero
def upperReverse : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .AND,
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op .AND,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op .MUL,
    .op .XOR ]
def lowerReverse : List Instr :=
  [ .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op .MUL,
    .op .XOR,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .AND,
    .op .MUL,
    .op .XOR ]
def template : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .AND,
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op .AND,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op .MUL,
    .op .XOR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op .MUL,
    .op .XOR,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .AND,
    .op .MUL,
    .op .XOR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .MSTORE,
    .op .POP,
    .op .POP,
    .op (.Dup ⟨1, by decide⟩) ]
private def reversedValue (v : UInt256) : UInt256 :=
  multipliedStage (multipliedStage v 8 mask8) 16 mask16
private theorem reversedValue_eq (v : UInt256) : reversedValue v = PairedScheduleData.reversedWord v := by
  simp only [reversedValue, DenseEndianMultiply.multipliedStage8_eq_packedStage,
    DenseEndianMultiply.multipliedStage16_eq_packedStage]
  exact PairedScheduleContract.packedWord_eq_reversedWord v
private def upperValue (high : UInt256) : UInt256 := (UInt256.xor (UInt256.mul (UInt256.ofNat 65537) (UInt256.land (UInt256.xor (UInt256.xor (UInt256.mul (UInt256.land (UInt256.xor high (UInt256.shiftRight high (UInt256.ofNat 8))) mask8) (UInt256.ofNat 257)) high) (UInt256.shiftRight (UInt256.xor (UInt256.mul (UInt256.land (UInt256.xor high (UInt256.shiftRight high (UInt256.ofNat 8))) mask8) (UInt256.ofNat 257)) high) (UInt256.ofNat 16))) mask16)) (UInt256.xor (UInt256.mul (UInt256.land (UInt256.xor high (UInt256.shiftRight high (UInt256.ofNat 8))) mask8) (UInt256.ofNat 257)) high))
private theorem upperValue_eq (high : UInt256) : upperValue high = reversedValue high := by
  norm_num only [upperValue, reversedValue, multipliedStage, endianDelta, endianFactor]
  simp only [RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
private theorem run_upper (s : State) (pc high low returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq upperReverse {s with pc := pc, stack := high :: low :: mask8 :: mask16 :: returnPC :: maskWord :: rest} =
      some {s with pc := pcAfter pc upperReverse, stack := PairedScheduleData.reversedWord high :: low :: mask8 :: mask16 :: returnPC :: maskWord :: rest} := by
  rw [← reversedValue_eq, ← upperValue_eq]
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [upperReverse, upperValue,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_upper
private def lowerValue (low : UInt256) : UInt256 := (UInt256.xor (UInt256.mul (UInt256.land (UInt256.xor (UInt256.xor (UInt256.mul (UInt256.ofNat 257) (UInt256.land (UInt256.xor low (UInt256.shiftRight low (UInt256.ofNat 8))) mask8)) low) (UInt256.shiftRight (UInt256.xor (UInt256.mul (UInt256.ofNat 257) (UInt256.land (UInt256.xor low (UInt256.shiftRight low (UInt256.ofNat 8))) mask8)) low) (UInt256.ofNat 16))) mask16) (UInt256.ofNat 65537)) (UInt256.xor (UInt256.mul (UInt256.ofNat 257) (UInt256.land (UInt256.xor low (UInt256.shiftRight low (UInt256.ofNat 8))) mask8)) low))
private theorem lowerValue_eq (low : UInt256) : lowerValue low = reversedValue low := by
  norm_num only [lowerValue, reversedValue, multipliedStage, endianDelta, endianFactor]
  simp only [RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
private theorem run_lower (s : State) (pc low returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq lowerReverse {s with pc := pc, stack := low :: mask8 :: mask16 :: returnPC :: maskWord :: rest} =
      some {s with pc := pcAfter pc lowerReverse, stack := PairedScheduleData.reversedWord low :: mask8 :: mask16 :: returnPC :: maskWord :: rest} := by
  rw [← reversedValue_eq, ← lowerValue_eq]
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [lowerReverse, lowerValue,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_lower
def cleanupTemplate : List Instr :=
  [.op .POP, .op .POP, .op (.Dup ⟨1, by decide⟩)]
private theorem run_cleanup (s : State) (pc m8 m16 returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq cleanupTemplate
      {s with pc := pc, stack := m8 :: m16 :: returnPC :: maskWord :: rest} =
      some {s with
        pc := pcAfter pc cleanupTemplate
        stack := maskWord :: returnPC :: maskWord :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  simp [cleanupTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero]
  rfl

theorem template_eq : template =
    (((upperReverse ++ upperStore) ++ lowerReverse) ++ lowerStore) ++ cleanupTemplate := by rfl
theorem run_endian (s : State) (pc low high returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := high :: low :: mask8 :: mask16 :: returnPC :: maskWord :: rest} =
      some {s with pc := pcAfter pc template, stack := maskWord :: returnPC :: maskWord :: rest, memory := Table80ScratchZero.scratchMemory s.memory (PairedScheduleData.reversedWord low) (PairedScheduleData.reversedWord high)} := by
  have h1 := run_upper s pc high low returnPC rest hstack hrun
  change runInstrSeq upperReverse _ = some _ at h1
  have h2 := PairedSchedulePrimitives.run_storeTemplate s (pcAfter pc upperReverse)
    (PairedScheduleData.reversedWord high) 60
    (low :: mask8 :: mask16 :: returnPC :: maskWord :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h2
  change runInstrSeq upperStore _ = some _ at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_lower {s with memory := writeWord s.memory 60 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter pc upperReverse) upperStore) low returnPC rest hstack hrun
  change runInstrSeq lowerReverse _ = some _ at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := PairedSchedulePrimitives.run_storeTemplate
    {s with memory := writeWord s.memory 60 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse)
    (PairedScheduleData.reversedWord low) 28 (mask8 :: mask16 :: returnPC :: maskWord :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h4
  change runInstrSeq lowerStore _ = some _ at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_cleanup {s with memory := Table80ScratchZero.scratchMemory s.memory (PairedScheduleData.reversedWord low) (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse) lowerStore)
    mask8 mask16 returnPC rest hstack hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  simpa only [template_eq, DenseScheduleTrace.pcAfter_append, Table80ScratchZero.scratchMemory] using h
#print axioms run_endian
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian
