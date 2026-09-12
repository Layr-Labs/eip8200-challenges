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
   .push ⟨2, by decide⟩ (UInt256.ofNat 256), .op .CALLDATACOPY,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1469),
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1536),
   .push ⟨2, by decide⟩ (UInt256.ofNat 3912), .op .JUMP]

theorem run_copyAdd (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 170 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3912 = true) :
    runInstructions copyAddProgram (copyState s memory n bsize esize msize) =
      some (addCallState s memory input n bsize esize msize) := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 256 by omega) (by decide)
  have haw := copyBase_activeWords s n hn32 hactive
  simp only [State.activeWordsAfterUInt256] at haw
  simp [copyAddProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    copyState, addCallState, copyBaseMem, outer, hjump, hdata, hsize,
    State.activeWordsAfterUInt256, haw,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.FullBase
