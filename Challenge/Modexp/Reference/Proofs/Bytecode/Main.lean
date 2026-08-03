import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# MODEXP bytecode entry and header validation

This is the first execution certificate for the frozen artifact.  It follows
the compiler's function-declaration trampolines, reads the three EIP-198
header words, proves the EIP-7823 checks take their successful edge, and
stops at the operand dispatcher.  The same `GasSteps` witness is used by the
functional proof and by the exact gas schedule.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def loc (index : Nat) (hindex : index < 961 := by omega) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  Challenge.EvmProof.Stepper.Located.ofIndex Artifact.allWellFormed
    ⟨index, by
      change index < Artifact.referenceInstructions.length
      rw [Artifact.referenceInstructions_count]
      exact hindex⟩

/-- Reachable instruction indices from byte zero through the successful
EIP-7823 header check.  The non-contiguous prefix consists solely of the
compiler's jumps over internal function bodies. -/
def headerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [loc 0, loc 1,
   loc 12, loc 13, loc 14,
   loc 43, loc 44, loc 45,
   loc 80, loc 81, loc 82,
   loc 262, loc 263, loc 264,
   loc 350, loc 351, loc 352,
   loc 412, loc 413, loc 414,
   loc 560, loc 561, loc 562,
   loc 899, loc 900, loc 901, loc 902, loc 903, loc 904, loc 905,
   loc 906, loc 907, loc 908, loc 909, loc 910, loc 911, loc 912,
   loc 913, loc 914, loc 915, loc 916, loc 917, loc 918, loc 919]

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState referenceBytecode input 0 with
    pc := UInt256.ofNat 1228
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

private theorem headerWord (input : ByteArray) (offset : Nat) :
    MachineState.readWord input offset =
      UInt256.ofNat (Precompile.bytesToNatPadded input offset 32) := rfl

private theorem size_lt_word {n : Nat} (h : n ≤ 1024) : n < 2 ^ 256 := by
  omega

@[simp] private theorem jump14 :
    Decode.isValidJumpDest referenceBytecode 14 = true :=
  Artifact.isValidJumpDest_index 12 (by rfl)

@[simp] private theorem jump53 :
    Decode.isValidJumpDest referenceBytecode 53 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

@[simp] private theorem jump99 :
    Decode.isValidJumpDest referenceBytecode 99 = true :=
  Artifact.isValidJumpDest_index 80 (by rfl)

@[simp] private theorem jump305 :
    Decode.isValidJumpDest referenceBytecode 305 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

@[simp] private theorem jump434 :
    Decode.isValidJumpDest referenceBytecode 434 = true :=
  Artifact.isValidJumpDest_index 350 (by rfl)

@[simp] private theorem jump512 :
    Decode.isValidJumpDest referenceBytecode 512 = true :=
  Artifact.isValidJumpDest_index 412 (by rfl)

@[simp] private theorem jump699 :
    Decode.isValidJumpDest referenceBytecode 699 = true :=
  Artifact.isValidJumpDest_index 560 (by rfl)

@[simp] private theorem jump1196 :
    Decode.isValidJumpDest referenceBytecode 1196 = true :=
  Artifact.isValidJumpDest_index 899 (by rfl)

@[simp] private theorem jump1228 :
    Decode.isValidJumpDest referenceBytecode 1228 = true :=
  Artifact.isValidJumpDest_index 921 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerPath
      (initialState referenceBytecode input 0) = some (headerState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb' := size_lt_word hb
  have he' := size_lt_word he
  have hm' := size_lt_word hm
  simp (config := { maxSteps := 1000000 })
    [headerPath, loc, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerState, initialState, headerWord, baseSize, exponentSize, modulusSize,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hb, he, hm, hb', he', hm']

/-- Header parsing as a gas-parametric relational trace. -/
def gasSteps_header (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (headerState input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka headerPath
  · rfl
  · rfl
  · exact run_header input hvalid
  · rfl
  · exact deployAddress_not_precompile

/-- Exact, input-independent gas used by the compiler trampolines and the
three successful EIP-7823 size checks. -/
theorem gasSteps_header_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_header input hvalid).cost = 162 := by
  rfl

end Challenge.Modexp.Reference.Proofs.Bytecode.Main
