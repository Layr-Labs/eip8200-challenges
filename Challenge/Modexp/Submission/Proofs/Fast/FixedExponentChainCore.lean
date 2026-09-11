import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Artifact-independent fixed-exponent chain blocks

The two fixed-chain blocks which write memory are reduced here without any
concrete program-counter data.  Located-code modules subsequently prove only
that the submitted instruction slices denote these short programs.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates

def runInstructions : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← Challenge.EvmProof.Stepper.runInstr instruction state
      runInstructions rest next

def startProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 2048),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .op .MCOPY]

def decodeProgram : List Instr :=
  [.op .JUMPDEST,
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 3040),
   .op .ADD,
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 3833),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .push ⟨2, by decide⟩ (UInt256.ofNat 3072),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1024),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1930),
   .op .JUMP]

set_option linter.unusedSimpArgs false in
theorem run_startProgram (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    runInstructions startProgram (special s memory n bsize esize msize count) =
      some (square s (initialSquareMem memory n)
        n bsize esize msize count) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n :=
    Exp.mod_word_self
      (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n))
      2048 (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 1024 (32 * n) 2048 (32 * n)
      (by omega) (by omega) (by omega) (by omega) hactive
  simp (config := { maxSteps := 600000 })
    [startProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      special, square, initialSquareMem, Exp.mcopyMem, Exp.outer,
      hrun, hmod, hfix,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_decodeProgram (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 1930 = true)
    (hrun : s.halt = .Running) :
    runInstructions decodeProgram (decode s memory n bsize esize msize) =
      some (Exp.mpCall s
        (Exp.storeWord memory (3040 + 32 * n) (UInt256.ofNat 1))
        1024 3072 1024 (UInt256.ofNat 3833)
        (Exp.outer n bsize esize msize)) := by
  have haddr : (3040 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      3040 + 32 * n :=
    Exp.mod_word_self
      (Nat.lt_of_le_of_lt (show 3040 + 32 * n ≤ 3973 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (3040 + 32 * n) 32) = s.activeWords :=
    Exp.activeWords_fix s (3040 + 32 * n) 32 (by omega) (by omega) hactive
  simp (config := { maxSteps := 600000 })
    [decodeProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      decode, Exp.mpCall, Exp.storeWord, Exp.outer,
      hrun, haddr, hfix, hjump,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCore
