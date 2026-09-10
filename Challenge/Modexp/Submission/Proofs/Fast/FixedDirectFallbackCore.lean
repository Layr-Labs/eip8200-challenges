import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Artifact-independent fixed-exponent fallback

This isolates the semantic reduction of the short `MCOPY` fallback from its
concrete instruction locations.  The bytecode proof only has to identify the
located block with `fallbackProgram`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectFallbackCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates

def runInstructions : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← Challenge.EvmProof.Stepper.runInstr instruction state
      runInstructions rest next

def fallbackProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 4096),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .op .MCOPY,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1703),
   .op .JUMP]

set_option linter.unusedSimpArgs false in
theorem run_fallbackProgram (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 1703 = true)
    (hrun : s.halt = .Running) :
    runInstructions fallbackProgram
      (fallback s memory n bsize esize msize) =
      some (missState s memory n bsize esize msize) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n :=
    Exp.mod_word_self
      (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n))
      4096 (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 1024 (32 * n) 4096 (32 * n)
      (by omega) (by omega) (by omega) (by omega) hactive
  simp (config := { maxSteps := 600000 })
    [fallbackProgram, runInstructions,
      Challenge.EvmProof.Stepper.runInstr,
      fallback, missState, Exp.ebHead, Exp.mcopyMem, Exp.outer,
      hrun, hmod, hfix, Exp.push0_word, hjump,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectFallbackCore
