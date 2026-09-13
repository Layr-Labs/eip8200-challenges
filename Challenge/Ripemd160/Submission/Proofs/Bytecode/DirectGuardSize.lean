import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size gate: `(size >> 2) * (size ^ 1000) != 0` jumps to the generic arm. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4872

/-- `UInt256.eq` is `if a.toNat = b.toNat then 1 else 0`, and both operands are
below `2 ^ 256`, so the test reduces to the underlying `Nat` comparison. -/
theorem size_eq_zero (input : ByteArray) (k : Nat)
    (hlt : input.size < 2 ^ 256) (hk : k < 2 ^ 256) (hne : input.size ≠ k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hne]

theorem size_eq_one (input : ByteArray) (k : Nat)
    (heq : input.size = k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 1 := by
  rw [heq]
  unfold UInt256.eq
  simp

def gatePath : List Located := gatePrefix ++ [opAt 16 .JUMPI]

private theorem stepS_calldatasize (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

private theorem pc_g8 : Artifact.submissionArtifact.instructionPC 8 = 11 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g9 : Artifact.submissionArtifact.instructionPC 9 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g10 : Artifact.submissionArtifact.instructionPC 10 = 15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g11 : Artifact.submissionArtifact.instructionPC 11 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g12 : Artifact.submissionArtifact.instructionPC 12 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g13 : Artifact.submissionArtifact.instructionPC 13 = 19 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g14 : Artifact.submissionArtifact.instructionPC 14 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g15 : Artifact.submissionArtifact.instructionPC 15 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g16 : Artifact.submissionArtifact.instructionPC 16 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 354 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 242 = 354 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 242 (by rfl)
  rwa [hpc] at h

theorem run_gate_prefix (input : ByteArray) :
    run gatePrefix (PatternedScan.stS input 11 []) =
      some (PatternedScan.stS input 24 [354, EntryGateLogic.gateWord input.size]) := by
  simp (config := { maxSteps := 400000 })
    [run, gatePrefix, opAt, pushAt, wfOp, PatternedScan.stS, initialState,
     EntryGateLogic.gateWord, pc_g8, pc_g9, pc_g10, pc_g11, pc_g12, pc_g13, pc_g14, pc_g15,
     DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
     RawExpressionAC.xor_comm, RawExpressionAC.mul_comm]
  exact RawExpressionAC.mul_comm _ _

theorem run_gate_taken (input : ByteArray) (hfit : CalldataFits input)
    (h4 : 4 ≤ input.size) (h1000 : input.size ≠ 1000) :
    run gatePath (PatternedScan.stS input 11 []) = some (PatternedScan.stS input 354 []) := by
  have hj : run [opAt 16 .JUMPI]
      (PatternedScan.stS input 24 [354, EntryGateLogic.gateWord input.size]) =
      some (PatternedScan.stS input 354 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 16 24 _ (by norm_num) pc_g16)
      (PatternedScan.stepS_jumpi_taken input 24 354 354 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (EntryGateLogic.gateWord_true input.size hfit h4 h1000) generic_dest)
  exact DataStepper.runLocatedBlock_append gatePrefix [opAt 16 .JUMPI] _ _ _
    (run_gate_prefix input) rfl hj

theorem run_gate_fall (input : ByteArray) (hfit : CalldataFits input)
    (hsmall : input.size < 4 ∨ input.size = 1000) :
    run gatePath (PatternedScan.stS input 11 []) = some (PatternedScan.stS input 25 []) := by
  have hj : run [opAt 16 .JUMPI]
      (PatternedScan.stS input 24 [354, EntryGateLogic.gateWord input.size]) =
      some (PatternedScan.stS input 25 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 16 24 _ (by norm_num) pc_g16)
      (PatternedScan.stepS_jumpi_fall input 24 354 _ []
        (by simp) (by norm_num) (EntryGateLogic.gateWord_false input.size hfit hsmall))
  exact DataStepper.runLocatedBlock_append gatePrefix [opAt 16 .JUMPI] _ _ _
    (run_gate_prefix input) rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
