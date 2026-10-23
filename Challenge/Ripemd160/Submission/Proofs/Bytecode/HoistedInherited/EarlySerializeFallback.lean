import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTail
import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Erasing a speculative serialized answer on a scanner miss

The miss continuation clears the one speculative word before entering the
ordinary padding prefix.  The states do not coincide at PC 246: the cleared
word and its high-water mark are absorbed by the *nonempty* calldata copy.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.EarlySerializeFallback

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

/-- The entire speculative allocation, after the cleanup store. -/
def zero32 : ByteArray := ByteArray.mk (Array.replicate 32 0)

private theorem bytes_ext (a b : ByteArray) (hs : a.size = b.size)
    (hg : ∀ i : Nat, a[i]?.getD (0 : UInt8) = b[i]?.getD 0) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · exact hs
  · intro i ha hb
    have h := hg i
    rw [getElem?_pos _ i ha, getElem?_pos _ i hb] at h
    exact h

@[simp] theorem zero32_size : zero32.size = 32 := by rfl

@[simp] theorem zero32_getD (i : Nat) : zero32[i]?.getD 0 = 0 := by
  change (Array.replicate 32 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 32
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

/-- MSTORE(0,0) overwrites, rather than merely obscuring, all speculative bytes. -/
theorem clear_word (m : ByteArray) (hm : m.size = 32) :
    MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) 0 = zero32 := by
  have hz : Data.Bytes.natToBytesPadded 0 32 = zero32 := by
    apply bytes_ext
    · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size 0 32
    · intro i
      by_cases hi : i < 32
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
        simp
      · rw [Memory.getElem?_getD_eq_zero_of_size_le _ _ (by
          rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
        simp
  rw [hz]
  apply bytes_ext
  · simp [MachineState.writeBytes_size, hm]
  · intro i
    rw [MachineState.writeBytes_getElem?_getD]
    by_cases hi : i < 32
    · simp [hi]
    · have hm' : ¬ i < m.size := by omega
      simp [hi, getElem?_neg, hm']

/-- A nonempty write beyond the cleared word grows both memories to the same
size; zero padding makes their untouched bytes identical.  The nonempty
hypothesis matters because `writeBytes` treats an empty write as a no-op. -/
theorem writeBytes_absorb_zero32 (bytes : ByteArray) (start : Nat)
    (hstart : 32 ≤ start) (hne : 0 < bytes.size) :
    MachineState.writeBytes zero32 bytes start =
      MachineState.writeBytes ByteArray.empty bytes start := by
  apply bytes_ext
  · simp only [MachineState.writeBytes_size, zero32_size, ByteArray.size_empty,
      if_neg (by omega : bytes.size ≠ 0)]
    omega
  · intro i
    simp [MachineState.writeBytes_getElem?_getD]

/-- In particular, the generic calldata copy absorbs the cleared answer. -/
theorem calldata_absorb_zero32 (input : ByteArray) (hpos : 0 < input.size) :
    MachineState.writeBytes zero32 (MachineState.readPadded input 0 input.size) 1056 =
      MachineState.writeBytes ByteArray.empty
        (MachineState.readPadded input 0 input.size) 1056 := by
  apply writeBytes_absorb_zero32 _ _ (by decide)
  simpa only [Memory.readPadded_size] using hpos

private theorem activeWords_absorb (n : Nat) (hpos : 0 < n) :
    MachineState.activeWordsAfter 1 1056 n = MachineState.activeWordsAfter 0 1056 n := by
  simp only [MachineState.activeWordsAfter, if_neg (by omega : n ≠ 0)]
  have h : 1 ≤ (1056 + n - 1) / 32 + 1 := by omega
  change max 1 _ = max 0 _
  rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.zero_le _)]

@[simp] private theorem literalZeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) := Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := Word.ofNat_add_ofNat h

private def wfOp {op : Operation}
    (hcode : Decode.opcodeOf (PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op) (havail : op.availableInFork .Osaka = true) :
    DataStepper.WellFormed .Osaka (.op op) := ⟨hcode, hplain, havail⟩

/-- Include the destination JUMPDEST, so the result is precisely PC 246. -/
private def cleanupPath : List (DataStepper.Located HoistedInherited.Artifact.submissionArtifact .Osaka) :=
  [⟨3457, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3458, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3459, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3460, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3461, .push ⟨1, by decide⟩ (UInt256.ofNat 245), by rfl, by decide⟩,
   ⟨3462, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def cleared (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    memory := zero32, activeWords := UInt256.ofNat 1, pc := UInt256.ofNat 246 }

/-- Only the speculative memory, high-water mark, PC and lower stack differ
from the original initial state. -/
def incoming (input : ByteArray) (m : ByteArray) (rho : List UInt256) : State :=
  { initialState submissionBytecode input 0 with
    memory := m, activeWords := UInt256.ofNat 1,
    pc := UInt256.ofNat 4785, stack := rho }

private theorem cleanup_pcs :
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3457 = 4785 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3458 = 4786 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3459 = 4787 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3460 = 4788 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3461 = 4789 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 3462 = 4791 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 125 = 245 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem prefix_pcs :
    HoistedInherited.Artifact.submissionArtifact.instructionPC 126 = 246 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 127 = 277 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 128 = 309 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 129 = 310 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 130 = 311 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 131 = 314 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 132 = 315 ∧
    HoistedInherited.Artifact.submissionArtifact.instructionPC 133 = 316 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem jump245 : Decode.isValidJumpDest submissionBytecode 245 = true := by
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 125 (by rfl)
  have hp := cleanup_pcs.2.2.2.2.2.2
  change Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 245 = true
  simpa only [hp] using h

/-- Keep the large concrete code image out of the symbolic state reduction.
Only JUMP consults code, and its decoder premise is supplied separately. -/
private theorem run_cleanup_state (s : State) (m : ByteArray) (hm : m.size = 32)
    (hv : Decode.isValidJumpDest s.executionEnv.code 245 = true)
    (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock cleanupPath
      {s with
        memory := m, activeWords := UInt256.ofNat 1,
        pc := UInt256.ofNat 4785, stack := []} =
      some {s with
        memory := zero32, activeWords := UInt256.ofNat 1,
        pc := UInt256.ofNat 246, stack := []} := by
  obtain ⟨p0, p1, p2, p3, p4, p5, pd⟩ := cleanup_pcs
  simp [cleanupPath, DataStepper.runLocatedBlock, DataStepper.runLocated,
    DataStepper.runInstr, p0, p1, p2, p3, p4, p5, pd, hv, hrun,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, clear_word m hm]

private theorem run_cleanup (input : ByteArray) (m : ByteArray) (hm : m.size = 32) :
    DataStepper.runLocatedBlock cleanupPath (incoming input m []) =
      some (cleared input) := by
  exact run_cleanup_state (initialState submissionBytecode input 0) m hm jump245 rfl

def copyPrefix : List (DataStepper.Located HoistedInherited.Artifact.submissionArtifact .Osaka) :=
  HoistedInherited.Artifact.padEnterPath ++ HoistedInherited.Artifact.padCopyPath

theorem run_copyPrefix (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) :
    DataStepper.runLocatedBlock copyPrefix (cleared input) =
      some (HoistedInherited.PaddingTrace.padCopied input) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := prefix_pcs
  have hsize : input.size % 2 ^ 256 = input.size := Nat.mod_eq_of_lt
    (Nat.lt_trans hfit (by norm_num))
  have hsize' : input.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      input.size := hsize
  have hm8 : UInt256.ofNat
      450552876409790643671482431940419874915447411150352389258589821042463539455 =
      DenseScheduleTemplate.mask8 := by decide
  have hm16 : UInt256.ofNat
      1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide
  simp [copyPrefix, HoistedInherited.Artifact.padEnterPath, HoistedInherited.Artifact.padCopyPath,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    cleared, HoistedInherited.PaddingTrace.padCopied, HoistedInherited.PaddingTrace.padCopyDone,
    HoistedInherited.PaddingTrace.padLengthReady, HoistedInherited.PaddingTrace.padEntry, HoistedInherited.Main.initializedState,
    HoistedInherited.Execution.mainStart, HoistedInherited.Execution.atPC, initialState,
    p0, p1, p2, p3, p4, p5, p6, p7, hsize, hsize', hm8, hm16,
    Padding.messageOffset, State.activeWordsAfterUInt256,
    calldata_absorb_zero32 input hpos, activeWords_absorb input.size hpos]
  rfl

theorem run_copyPrefix_warmEmpty (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) :
    DataStepper.runLocatedBlock copyPrefix ({initialState submissionBytecode input 0 with
        pc := UInt256.ofNat 246, activeWords := UInt256.ofNat 1}) =
      some (HoistedInherited.PaddingTrace.padCopied input) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := prefix_pcs
  have hsize : input.size % 2 ^ 256 = input.size := Nat.mod_eq_of_lt
    (Nat.lt_trans hfit (by norm_num))
  have hsize' : input.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      input.size := hsize
  have hm8 : UInt256.ofNat
      450552876409790643671482431940419874915447411150352389258589821042463539455 =
      DenseScheduleTemplate.mask8 := by decide
  have hm16 : UInt256.ofNat
      1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide
  simp [copyPrefix, HoistedInherited.Artifact.padEnterPath, HoistedInherited.Artifact.padCopyPath,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    HoistedInherited.PaddingTrace.padCopied, HoistedInherited.PaddingTrace.padCopyDone,
    HoistedInherited.PaddingTrace.padLengthReady, HoistedInherited.PaddingTrace.padEntry, HoistedInherited.Main.initializedState,
    HoistedInherited.Execution.mainStart, HoistedInherited.Execution.atPC, initialState,
    p0, p1, p2, p3, p4, p5, p6, p7, hsize, hsize', hm8, hm16,
    Padding.messageOffset, State.activeWordsAfterUInt256,
    activeWords_absorb input.size hpos]
  rfl

theorem run_copyPrefix_coldEmpty (input : ByteArray) (hfit : CalldataFits input)
    (_hpos : 0 < input.size) :
    DataStepper.runLocatedBlock copyPrefix ({initialState submissionBytecode input 0 with
        pc := UInt256.ofNat 246, activeWords := UInt256.ofNat 0}) =
      some (HoistedInherited.PaddingTrace.padCopied input) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := prefix_pcs
  have hsize : input.size % 2 ^ 256 = input.size := Nat.mod_eq_of_lt
    (Nat.lt_trans hfit (by norm_num))
  have hsize' : input.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      input.size := hsize
  have hm8 : UInt256.ofNat
      450552876409790643671482431940419874915447411150352389258589821042463539455 =
      DenseScheduleTemplate.mask8 := by decide
  have hm16 : UInt256.ofNat
      1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide
  simp [copyPrefix, HoistedInherited.Artifact.padEnterPath, HoistedInherited.Artifact.padCopyPath,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    HoistedInherited.PaddingTrace.padCopied, HoistedInherited.PaddingTrace.padCopyDone,
    HoistedInherited.PaddingTrace.padLengthReady, HoistedInherited.PaddingTrace.padEntry, HoistedInherited.Main.initializedState,
    HoistedInherited.Execution.mainStart, HoistedInherited.Execution.atPC, initialState,
    p0, p1, p2, p3, p4, p5, p6, p7, hsize, hsize', hm8, hm16,
    Padding.messageOffset, State.activeWordsAfterUInt256]
  rfl

/-- Scanner misses with a nonempty input rejoin the ordinary framed padding
state, preserving any lower stack of at most twenty words. -/
def gasSteps (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (m : ByteArray) (hm : m.size = 32) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (incoming input m rho)
      (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho) := by
  have gc := StackTail.gasSteps cleanupPath rho
    (by change 0 + rho.length + 7 < 1024; omega)
    (run_cleanup input m hm) rfl rfl rfl deployAddress_not_precompile
  have gp := StackTail.gasSteps copyPrefix rho
    (by change 0 + rho.length + 8 < 1024; omega)
    (run_copyPrefix input hfit hpos) rfl rfl rfl deployAddress_not_precompile
  exact GasSteps.cast
    (gc.trans (gp.trans (HoistedInherited.PaddingTail.gasSteps_push input rho hcap))) (by rfl) rfl

/-- Convenient form for a scanner theorem that names its incoming state. -/
def gasSteps_of_eq (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) (s : State) (m : ByteArray) (hm : m.size = 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (hs : s = { initialState submissionBytecode input 0 with
      memory := m, activeWords := UInt256.ofNat 1,
      pc := UInt256.ofNat 4785, stack := rho }) :
    GasSteps s (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho) := by
  subst s
  exact gasSteps input hfit hpos m hm rho hcap

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.EarlySerializeFallback
