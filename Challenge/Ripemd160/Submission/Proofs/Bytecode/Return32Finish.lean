import Challenge.Ripemd160.Submission.Proofs.Bytecode.FinishMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Return32Output
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianLiteralBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Return32Finish
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

@[simp] private theorem rawZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

/-! ## The two multiplication stages -/

/-- Halfword swap scaled by `2^16`, then byte swap scaled by `2^8`; no right shift is executed. -/
def stage16 (m16 v : UInt256) : UInt256 :=
  UInt256.add (UInt256.mul (UInt256.ofNat 4294967295) (UInt256.land m16 v)) v
def stage8 (m8 v : UInt256) : UInt256 :=
  UInt256.add (UInt256.mul (UInt256.ofNat 65535) (UInt256.land m8 v)) v
def finish (m8 m16 v : UInt256) : UInt256 := stage8 m8 (stage16 m16 v)

def stagesCode : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .AND,
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), .op .MUL, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 65535), .op .MUL, .op .ADD]

theorem run_stages (s : State) (pc value a b m8 m16 : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running) :
    runInstrSeq stagesCode {s with pc := pc, stack := value :: a :: b :: m8 :: m16 :: rest} =
      some {s with pc := pcAfter pc stagesCode, stack := finish m8 m16 value :: a :: b :: m8 :: m16 :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [stagesCode, finish, stage16, stage8, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

/-! ## The terminal store and return -/

/-- Store at byte offset three and return the first word of memory. -/
def terminalCode : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .MSTORE,
   .op .CALLDATASIZE, .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .RETURN]

def outputMemory (s : State) (value : UInt256) : ByteArray :=
  MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded value.toNat 32) 3

def terminalResult (s : State) (pc value : UInt256) (rho : List UInt256) : State :=
  {s with
    pc := pcAfter pc terminalCode.dropLast
    stack := rho
    memory := outputMemory s value
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      (s.activeWordsAfterUInt256 3 32).toNat 0 32)
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory s value) 0 32}

theorem run_terminal (s : State) (pc value : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hrun : s.halt = .Running)
    (h32 : s.executionEnv.calldata.size = 32) :
    runInstrSeq terminalCode {s with pc := pc, stack := value :: rho} =
      some (terminalResult s pc value rho) := by
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  have hs : rho.length < 1024 := by omega
  simp (discharger := omega) [terminalCode, terminalResult, outputMemory, runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap, hs, h32, Nat.add_assoc,
    State.activeWordsAfterUInt256, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

theorem terminal_advances : ∀ instruction ∈ terminalCode.dropLast, PadLift.Advances instruction := by
  apply PadLift.advancesAll_sound
  decide

theorem stages_advances : ∀ instruction ∈ stagesCode, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound stagesCode (by decide)

/-! ## The artifact sites -/

theorem stages_slice :
    (Artifact.submissionArtifact.instructions.drop 5421).take stagesCode.length = stagesCode := by rfl
def stagesSite : GenericRoundSite Artifact.submissionArtifact .Osaka stagesCode :=
  StackSiteBuilder.ofSlice stagesCode 5421 stages_slice
    (by change 5421 + stagesCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := stagesCode) (by decide)) (by decide)
theorem stages_pc : stagesSite.startPC = UInt256.ofNat 9691 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5421) = UInt256.ofNat 9691
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stages_end : stagesSite.endPC = UInt256.ofNat 9709 := by
  have h := endPC_eq_pcAfter_sites stagesSite.sites stagesSite.startPC stagesSite.endPC
    stagesSite.head_eq stagesSite.end_eq stagesSite.contiguous
  rw [stagesSite.instruction_eq, stages_pc] at h
  exact h.trans (by decide)

theorem terminal_slice :
    (Artifact.submissionArtifact.instructions.drop 5433).take terminalCode.length = terminalCode := by rfl
def terminalSite : GenericRoundSite Artifact.submissionArtifact .Osaka terminalCode :=
  StackSiteBuilder.ofSlice terminalCode 5433 terminal_slice
    (by change 5433 + terminalCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := terminalCode) (by decide)) (by decide)
theorem terminal_pc : terminalSite.startPC = UInt256.ofNat 9709 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5433) = UInt256.ofNat 9709
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_stages (s : State) (value a b m8 m16 : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1000)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 9691, stack := value :: a :: b :: m8 :: m16 :: rest}
      {s with pc := UInt256.ofNat 9709, stack := finish m8 m16 value :: a :: b :: m8 :: m16 :: rest} := by
  have hend : pcAfter (UInt256.ofNat 9691) stagesCode = UInt256.ofNat 9709 := by decide
  have hraw := run_stages s (UInt256.ofNat 9691) value a b m8 m16 rest hstack hrun
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw stagesSite
    {s with pc := UInt256.ofNat 9691, stack := value :: a :: b :: m8 :: m16 :: rest}
    {s with pc := UInt256.ofNat 9709, stack := finish m8 m16 value :: a :: b :: m8 :: m16 :: rest}
    hcode hfork hrun hnp stages_pc.symm stages_advances hraw

def gasSteps_terminal (s : State) (value : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps {s with pc := UInt256.ofNat 9709, stack := value :: rho}
      (terminalResult s (UInt256.ofNat 9709) value rho) :=
  PadLift.gasSteps_of_raw terminalSite _ _ hcode hfork hrun hnp terminal_pc.symm
    terminal_advances (run_terminal s (UInt256.ofNat 9709) value rho hstack hrun h32)

/-! ## Semantics: the stages produce the byte-swapped word scaled by `2^24` -/

section Math
open PairedLaneUInt256Bridge DenseScheduleTemplate

private theorem bits_mask8 : bits mask8 = FinishMath.M8 := rfl
private theorem bits_mask16 : bits mask16 = FinishMath.M16 := rfl

theorem bits_stage16 (v : UInt256) :
    bits (stage16 mask16 v) =
      bits v + (bits v &&& FinishMath.M16) * BitVec.ofNat 256 4294967295 := by
  simp only [stage16, bits_add, bits_mul, bits_land, bits_ofNat, bits_mask16]
  rw [BitVec.and_comm, BitVec.mul_comm, BitVec.add_comm]

theorem bits_stage8 (v : UInt256) :
    bits (stage8 mask8 v) =
      bits v + (bits v &&& FinishMath.M8) * BitVec.ofNat 256 65535 := by
  simp only [stage8, bits_add, bits_mul, bits_land, bits_ofNat, bits_mask8]
  rw [BitVec.and_comm, BitVec.mul_comm, BitVec.add_comm]

theorem bits_packedStage8 (v : UInt256) :
    bits (packedStage v 8 mask8) = FinishMath.P8 (bits v) := by
  simp only [packedStage, bits_lor, bits_land, bits_shl _ 8 (by norm_num : 8 < 256),
    bits_shr _ 8 (by norm_num : 8 < 256), bits_mask8, FinishMath.P8]

theorem bits_packedStage16 (v : UInt256) :
    bits (packedStage v 16 mask16) = FinishMath.P16 (bits v) := by
  simp only [packedStage, bits_lor, bits_land, bits_shl _ 16 (by norm_num : 16 < 256),
    bits_shr _ 16 (by norm_num : 16 < 256), bits_mask16, FinishMath.P16]

theorem bits_packedWord (v : UInt256) :
    bits (packedWord v) = FinishMath.P16 (FinishMath.P8 (bits v)) := by
  unfold packedWord
  rw [bits_packedStage16, bits_packedStage8]

theorem bits_finish (v : UInt256) :
    bits (finish mask8 mask16 v) = (FinishMath.P16 (FinishMath.P8 (bits v))) <<< 24 := by
  unfold finish
  rw [bits_stage8, bits_stage16]
  exact FinishMath.fast_all (bits v)

private theorem and_mod_of_lt (m y : Nat) (hy : y < 2 ^ 160) :
    (m % 2 ^ 160) &&& y = m &&& y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < 160
  · simp [hi]
  · have hyi : y.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, hyi]

theorem packedStage16_lt (value : UInt256) (hv : value.toNat < 2 ^ 160) :
    (packedStage value 16 mask16).toNat < 2 ^ 160 := by
  have hlow : (UInt256.land value mask16).toNat < 2 ^ 144 := by
    rw [Word.word_toNat_land, Nat.and_comm, ← and_mod_of_lt mask16.toNat value.toNat hv]
    apply Nat.lt_of_le_of_lt Nat.and_le_left
    decide
  have hleft : (UInt256.shiftLeft (UInt256.land value mask16) (UInt256.ofNat 16)).toNat < 2 ^ 160 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide), Word.word_toNat_ofNat]
    norm_num only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    exact Nat.shiftLeft_lt hlow (m := 16)
  have hright : (UInt256.land (UInt256.shiftRight value (UInt256.ofNat 16)) mask16).toNat < 2 ^ 160 := by
    rw [Word.word_toNat_land]
    apply Nat.lt_of_le_of_lt Nat.and_le_left
    rw [Word.shiftRight_toNat value (by norm_num)]
    exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hv
  unfold packedStage
  rw [Word.word_toNat_lor]
  exact Nat.or_lt_two_pow hleft hright

theorem packedWord_lt (v : UInt256) (hv : v.toNat < 2 ^ 160) :
    (packedWord v).toNat < 2 ^ 160 :=
  packedStage16_lt _ (ClosedEndianLiteralBounds.packedStage8_lt v hv)

theorem finish_toNat (v : UInt256) (hv : v.toNat < 2 ^ 160) :
    (finish mask8 mask16 v).toNat = (packedWord v).toNat * 2 ^ 24 := by
  have hW := packedWord_lt v hv
  rw [← bits_toNat, bits_finish, ← bits_packedWord, BitVec.toNat_shiftLeft, bits_toNat,
    Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have h24 : (2 : Nat) ^ 24 * 2 ^ 160 ≤ 2 ^ 256 := by norm_num
  calc (packedWord v).toNat * 2 ^ 24 < 2 ^ 160 * 2 ^ 24 :=
        Nat.mul_lt_mul_of_pos_right hW (by norm_num)
    _ ≤ 2 ^ 256 := by norm_num
end Math

/-! ## The returned bytes -/

theorem readPadded_finish (m : ByteArray) (W : Nat) (hW : W < 2 ^ 232)
    (hpre : ∀ i, i < 3 → m[i]?.getD 0 = 0) :
    MachineState.readPadded
      (MachineState.writeBytes m (Data.Bytes.natToBytesPadded (W * 2 ^ 24) 32) 3) 0 32 =
      Data.Bytes.natToBytesPadded W 32 := by
  apply ByteArray.ext_getElem
  · simp only [Memory.readPadded_size, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi hj
    have hil : i < 32 := by simpa only [Memory.readPadded_size] using hi
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
      Memory.readPadded_getElem?_getD, if_pos hil, Nat.zero_add,
      MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hil]
    by_cases h3 : 3 ≤ i
    · rw [if_pos ⟨h3, by omega⟩,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
      congr 2
      have he : 32 - 1 - (i - 3) = (32 - 1 - i) + 3 := by omega
      rw [he, Nat.pow_add, show (2 : Nat) ^ 24 = 256 ^ 3 by norm_num]
      exact Nat.mul_div_mul_right W _ (by norm_num)
    · rw [if_neg (by omega), hpre i (by omega)]
      have hlt : W < 256 ^ (32 - 1 - i) := by
        calc W < 2 ^ 232 := hW
          _ = 256 ^ 29 := by norm_num
          _ ≤ 256 ^ (32 - 1 - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt hlt]
      rfl

theorem prepared_prefix (s : State) (h : Compression.HashState) (i : Nat) (hi : i < 3) :
    (Return32Output.prepared s h).memory[i]?.getD 0 = 0 := by
  have hm : (Return32Output.prepared s h).memory = MemoryPackedOutput.memory s.memory h := rfl
  rw [hm]
  simp only [MemoryPackedOutput.memory, MemoryPackedOutput.store,
    MachineState.writeBytes_getElem?_getD, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_pos ⟨by omega, by omega⟩,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have h0 := h.h0.toNat_lt
  have hlt : h.h0.toNat < 256 ^ (32 - 1 - i) := by
    calc h.h0.toNat < 2 ^ 32 := h0
      _ ≤ 256 ^ (32 - 1 - i) := by
        calc (2 : Nat) ^ 32 ≤ 256 ^ 4 := by norm_num
          _ ≤ 256 ^ (32 - 1 - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.sub_zero, Nat.div_eq_of_lt hlt]
  rfl

theorem hReturn_eq (s : State) (h : Compression.HashState) (pc : UInt256) (rho : List UInt256) :
    (terminalResult (Return32Output.prepared s h) pc
      (finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
        (Return32Output.packedHash h)) rho).hReturn =
    Data.Bytes.natToBytesPadded
      (DenseScheduleTemplate.packedWord (Return32Output.packedHash h)).toNat 32 := by
  have hV := ClosedEndianTrunc16.packedHash_lt h
  have hfin := finish_toNat _ hV
  have hW := packedWord_lt _ hV
  show MachineState.readPadded
    (outputMemory (Return32Output.prepared s h) _) 0 32 = _
  unfold outputMemory
  rw [hfin]
  exact readPadded_finish _ _ (Nat.lt_of_lt_of_le hW (by norm_num)) (prepared_prefix s h)

#print axioms run_stages
#print axioms run_terminal
#print axioms gasSteps_stages
#print axioms gasSteps_terminal
#print axioms finish_toNat
#print axioms readPadded_finish
#print axioms prepared_prefix
#print axioms hReturn_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Return32Finish
