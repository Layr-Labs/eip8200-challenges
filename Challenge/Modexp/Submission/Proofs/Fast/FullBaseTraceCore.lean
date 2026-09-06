import Challenge.Modexp.Submission.Proofs.Fast.FullBaseStates
import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

/-- Symbolic instruction execution; actual byte locations and gas are separate obligations. -/
def runInstructions : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← Challenge.EvmProof.Stepper.runInstr instruction state
      runInstructions rest next

def copyAddProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 96),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024), .op .CALLDATACOPY,
   .push ⟨2, by decide⟩ (UInt256.ofNat 3644),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .push ⟨2, by decide⟩ (UInt256.ofNat 3072),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .push ⟨2, by decide⟩ (UInt256.ofNat 3695), .op .JUMP]

def dispatchProgram : List Instr :=
  [.op .JUMPDEST,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024), .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255), .op .SHR, .op .ISZERO,
   .push ⟨2, by decide⟩ (UInt256.ofNat 3712), .op .JUMPI,
   .push ⟨2, by decide⟩ (UInt256.ofNat 2467), .op .JUMP]


def afterAddProgram : List Instr :=
  [.op .JUMPDEST,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1755),
   .push ⟨2, by decide⟩ (UInt256.ofNat 2048),
   .push ⟨2, by decide⟩ (UInt256.ofNat 6144),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1939), .op .JUMP]

theorem run_afterAdd (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 1939 = true) :
    runInstructions afterAddProgram (afterAddState s memory n bsize esize msize) =
      some (monproCallState s memory n bsize esize msize) := by
  simp [afterAddProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    afterAddState, monproCallState, outer, hjump,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_copyAdd (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3695 = true) :
    runInstructions copyAddProgram (copyState s memory n bsize esize msize) =
      some (dispatchState s memory input n bsize esize msize) := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by decide)
  have haw := copyBase_activeWords s n hn32 hactive
  simp only [State.activeWordsAfterUInt256] at haw
  simp [copyAddProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    copyState, dispatchState, copyBaseMem, outer, hjump, hdata, hsize,
    State.activeWordsAfterUInt256, haw,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch_hit (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat)
    (htop : BaseTopBitSet (copyBaseMem memory input n))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2467 = true) :
    runInstructions dispatchProgram
      (dispatchState s memory input n bsize esize msize) =
      some (addCallState s memory input n bsize esize msize) := by
  have hword : 2 ^ 255 ≤
      (MachineState.readWord (copyBaseMem memory input n) 1024).toNat := htop
  have hshift :
      (UInt256.shiftRight
        (MachineState.readWord (copyBaseMem memory input n) 1024)
        (UInt256.ofNat 255)).toNat ≠ 0 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide)]
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.ne_of_gt (Nat.div_pos (by omega) (by norm_num))
  have hzero : UInt256.isZero
      (UInt256.shiftRight
        (MachineState.readWord (copyBaseMem memory input n) 1024)
        (UInt256.ofNat 255)) = UInt256.ofNat 0 := by
    rw [UInt256.isZero]
    simp [hshift]
  simp [dispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    dispatchState, addCallState, copyBaseMem, outer, hzero, hjump,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def dispatchSkipProgram : List Instr :=
  [.op .JUMPDEST,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024), .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255), .op .SHR, .op .ISZERO,
   .push ⟨2, by decide⟩ (UInt256.ofNat 3712), .op .JUMPI,
   .op .JUMPDEST, .op .POP, .op .POP, .op .POP, .op .POP,
   .push ⟨2, by decide⟩ (UInt256.ofNat 3644), .op .JUMP]

theorem run_dispatch_skip (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat)
    (htop : ¬ BaseTopBitSet (copyBaseMem memory input n))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3644 = true) :
    runInstructions dispatchSkipProgram
      (dispatchState s memory input n bsize esize msize) =
      some (afterAddState s (copyBaseMem memory input n)
        n bsize esize msize) := by
  have hword : (MachineState.readWord
      (copyBaseMem memory input n) 1024).toNat < 2 ^ 255 := by
    exact Nat.lt_of_not_ge (by simpa [BaseTopBitSet] using htop)
  have hshift :
      (UInt256.shiftRight
        (MachineState.readWord (copyBaseMem memory input n) 1024)
        (UInt256.ofNat 255)).toNat = 0 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide)]
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hword
  have hzero : UInt256.isZero
      (UInt256.shiftRight
        (MachineState.readWord (copyBaseMem memory input n) 1024)
        (UInt256.ofNat 255)) = UInt256.ofNat 1 := by
    rw [UInt256.isZero]
    simp [hshift]
  simp [dispatchSkipProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, dispatchState, afterAddState,
    copyBaseMem, outer, hzero, hjump,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.FullBase

