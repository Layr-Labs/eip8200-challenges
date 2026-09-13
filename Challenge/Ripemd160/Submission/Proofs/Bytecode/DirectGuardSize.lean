import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryGateLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size gate: `(size >> 2) * (size ^ 1000) != 0` jumps to the generic arm. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4870

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

private theorem pc_g8 : Artifact.submissionArtifact.instructionPC 8 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g9 : Artifact.submissionArtifact.instructionPC 9 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g10 : Artifact.submissionArtifact.instructionPC 10 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g11 : Artifact.submissionArtifact.instructionPC 11 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g12 : Artifact.submissionArtifact.instructionPC 12 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g13 : Artifact.submissionArtifact.instructionPC 13 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g14 : Artifact.submissionArtifact.instructionPC 14 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g15 : Artifact.submissionArtifact.instructionPC 15 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_g16 : Artifact.submissionArtifact.instructionPC 16 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 358 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 244 = 358 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 244 (by rfl)
  rwa [hpc] at h

theorem run_gate_prefix (input : ByteArray) :
    run gatePrefix (PatternedScan.stS input 12 []) =
      some (PatternedScan.stS input 26 [358, EntryGateLogic.gateWord input.size]) := by
  let n := UInt256.ofNat input.size
  let s := UInt256.shiftRight n 2
  let x := UInt256.xor 1000 n
  let l0 : Located := opAt 8 .CALLDATASIZE
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 8 12 [] (by norm_num) pc_g8)
    (stepS_calldatasize input 12 [] (by simp) (by norm_num))
  let l1 : Located := pushAt 9 2 2
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 9 13 [n] (by norm_num) pc_g9)
    (PatternedScan.stepS_push input 13 2 2 [n] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 10 .SHR
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 10 16 [2, n] (by norm_num) pc_g10)
    (PatternedScan.stepS_shr input 16 2 n [] (by simp) (by norm_num))
  let l3 : Located := opAt 11 .CALLDATASIZE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 11 17 [s] (by norm_num) pc_g11)
    (stepS_calldatasize input 17 [s] (by simp) (by norm_num))
  let l4 : Located := pushAt 12 2 1000
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 12 18 [n, s] (by norm_num) pc_g12)
    (PatternedScan.stepS_push input 18 2 1000 [n, s] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := opAt 13 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 13 21 [1000, n, s] (by norm_num) pc_g13)
    (PatternedScan.stepS_xor input 21 1000 n [s] (by simp) (by norm_num))
  let l6 : Located := opAt 14 .MUL
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 14 22 [x, s] (by norm_num) pc_g14)
    (PatternedScan.stepS_mul input 22 x s [] (by simp) (by norm_num))
  let l7 : Located := pushAt 15 2 358
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 15 23 [x * s] (by norm_num) pc_g15)
    (PatternedScan.stepS_push input 23 2 358 [x * s] (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  have hseq7 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ hseq6 rfl h7
  have hv : x * s = EntryGateLogic.gateWord input.size := by
    simp only [x, s, n, EntryGateLogic.gateWord, Word.literal_eq_ofNat]
  rw [hv] at hseq7
  exact hseq7

theorem run_gate_taken (input : ByteArray) (hfit : CalldataFits input)
    (h4 : 4 ≤ input.size) (h1000 : input.size ≠ 1000) :
    run gatePath (PatternedScan.stS input 12 []) = some (PatternedScan.stS input 358 []) := by
  have hj : run [opAt 16 .JUMPI]
      (PatternedScan.stS input 26 [358, EntryGateLogic.gateWord input.size]) =
      some (PatternedScan.stS input 358 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 16 26 _ (by norm_num) pc_g16)
      (PatternedScan.stepS_jumpi_taken input 26 358 358 _ []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (EntryGateLogic.gateWord_true input.size hfit h4 h1000) generic_dest)
  exact DataStepper.runLocatedBlock_append gatePrefix [opAt 16 .JUMPI] _ _ _
    (run_gate_prefix input) rfl hj

theorem run_gate_fall (input : ByteArray) (hfit : CalldataFits input)
    (hsmall : input.size < 4 ∨ input.size = 1000) :
    run gatePath (PatternedScan.stS input 12 []) = some (PatternedScan.stS input 27 []) := by
  have hj : run [opAt 16 .JUMPI]
      (PatternedScan.stS input 26 [358, EntryGateLogic.gateWord input.size]) =
      some (PatternedScan.stS input 27 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 16 26 _ (by norm_num) pc_g16)
      (PatternedScan.stepS_jumpi_fall input 26 358 _ []
        (by simp) (by norm_num) (EntryGateLogic.gateWord_false input.size hfit hsmall))
  exact DataStepper.runLocatedBlock_append gatePrefix [opAt 16 .JUMPI] _ _ _
    (run_gate_prefix input) rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
