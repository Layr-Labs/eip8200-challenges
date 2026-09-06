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
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2467 = true) :
    runInstructions copyAddProgram (copyState s memory n bsize esize msize) =
      some (addCallState s memory input n bsize esize msize) := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by decide)
  have haw := copyBase_activeWords s n hn32 hactive
  simp only [State.activeWordsAfterUInt256] at haw
  simp [copyAddProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    copyState, addCallState, copyBaseMem, outer, hjump, hdata, hsize,
    State.activeWordsAfterUInt256, haw,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.FullBase

