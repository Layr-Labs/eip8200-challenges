import Challenge.Sha256.RouteB
import EvmSemantics.EVM.StepDeterminism
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Direct execution proof for the frozen SHA-256 reference bytecode

This module starts the concrete proof of `referenceDirectGoal`. Unlike the
Route A proof, every transition here is a transition of the frozen bytes under
`EvmSemantics.EVM.stepF`; no Yul syntax or compiler theorem is in scope.
-/

namespace Challenge.Sha256.RouteB.Reference

open EvmSemantics
open EvmSemantics.EVM

/-- The SHA program body starts after the compiler-generated function
trampolines. -/
def mainPC : Nat := 0x03e5

/-- The compiler-generated entry chain. Every element is a `JUMPDEST`; all
but the last immediately push and jump to the next element. -/
def entryTargets : List Nat :=
  [0x001b, 0x0044, 0x006d, 0x009e, 0x00cf,
   0x00e4, 0x00fc, 0x0112, 0x0126, 0x0139,
   0x014d, 0x0160, 0x01b9, 0x025f, mainPC]

theorem reference_decode_entry_push :
    Decode.decodeAt referenceBytecode 0 =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat 0x001b, 2)) := by
  norm_num [Decode.decodeAt, Decode.opcodeOf,
    UInt8.toNat_ofNat]

theorem reference_decode_entry_jump :
    Decode.decodeAt referenceBytecode 3 = some (.JUMP, none) := by
  decide

/-- One compact certificate validates every destination in the entry chain
against the pinned EVM jump-destination scan. -/
theorem reference_entryTargets_valid :
    Challenge.RouteB.Bytecode.JumpDestCertificate
      referenceBytecode entryTargets := by
  change entryTargets.all (Decode.isValidJumpDest referenceBytecode) = true
  decide

/-- Membership in the certified list yields the exact side condition used by
`JUMP` and `JUMPI`. -/
theorem reference_entryTarget_isValid {pc : Nat} (hpc : pc ∈ entryTargets) :
    Decode.isValidJumpDest referenceBytecode pc = true := by
  exact Challenge.RouteB.Bytecode.JumpDestCertificate.valid
    reference_entryTargets_valid hpc

theorem reference_first_target_is_jumpdest :
    Decode.isValidJumpDest referenceBytecode 0x001b = true := by
  apply reference_entryTarget_isValid
  simp [entryTargets]

theorem frame_decoded_entry_push (calldata : ByteArray) (gas : Nat) :
    (frame referenceBytecode calldata gas).decoded =
      some (.Push ⟨2, by decide⟩, some (UInt256.ofNat 0x001b, 2)) := by
  unfold State.decoded
  rw [show (frame referenceBytecode calldata gas).executionEnv.code =
    referenceBytecode by rfl]
  rw [show (frame referenceBytecode calldata gas).pc.toNat = 0 by rfl]
  rw [reference_decode_entry_push]
  rfl

theorem pushed_decoded_entry_jump (calldata : ByteArray) (gas : Nat) :
    ({ frame referenceBytecode calldata gas with
      pc := UInt256.ofNat 3
      stack := [UInt256.ofNat 0x001b]
      gasAvailable := gas - 3 } : State).decodedOp = some .JUMP := by
  unfold State.decodedOp State.decoded
  rw [show ({ frame referenceBytecode calldata gas with
    pc := UInt256.ofNat 3
    stack := [UInt256.ofNat 0x001b]
    gasAvailable := gas - 3 } : State).executionEnv.code = referenceBytecode by rfl]
  rw [show (UInt256.ofNat 3).toNat = 3 by decide]
  rw [reference_decode_entry_jump]
  rfl

theorem step_entry_push (calldata : ByteArray) (gas : Nat) (hgas : 3 ≤ gas) :
    Step (frame referenceBytecode calldata gas)
      { frame referenceBytecode calldata gas with
          pc := UInt256.ofNat 3
          stack := [UInt256.ofNat 0x001b]
          gasAvailable := gas - 3 } := by
  have hpc : (0 : UInt256) + UInt256.ofNat 3 = UInt256.ofNat 3 := by decide
  apply Step.running rfl deployAddress_not_precompile
  simpa [frame, State.fork, Gas.baseCost, hpc] using
    StepRunning.pushN (s := frame referenceBytecode calldata gas)
      (k := ⟨2, by decide⟩) (data := UInt256.ofNat 0x001b) (immWidth := 2)
      (by decide) (frame_decoded_entry_push calldata gas)
      (by change 3 ≤ gas; exact hgas) (by simp [frame])

theorem stepF_entry_push (calldata : ByteArray) (gas : Nat) (hgas : 3 ≤ gas) :
    stepF (frame referenceBytecode calldata gas) =
      { frame referenceBytecode calldata gas with
          pc := UInt256.ofNat 3
          stack := [UInt256.ofNat 0x001b]
          gasAvailable := gas - 3 } := by
  exact step_complete (step_entry_push calldata gas hgas)

theorem step_entry_jump (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Step { frame referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 }
      { frame referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  have hjump : 8 ≤ gas - 3 := by omega
  have hsub : gas - 3 - 8 = gas - 11 := by omega
  apply Step.running rfl deployAddress_not_precompile
  simpa [frame, State.fork, Gas.baseCost, hsub] using
    StepRunning.jump
      (s := { frame referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 })
      (dest := UInt256.ofNat 0x001b) (rest := [])
      (pushed_decoded_entry_jump calldata gas)
      (by change 8 ≤ gas - 3; exact hjump) (by simp) (by
        change Decode.isValidJumpDest referenceBytecode 0x001b = true
        exact reference_first_target_is_jumpdest) (by
          norm_num [Operation.pushArity, Operation.popArity])

theorem stepF_entry_jump (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    stepF { frame referenceBytecode calldata gas with
        pc := UInt256.ofNat 3
        stack := [UInt256.ofNat 0x001b]
        gasAvailable := gas - 3 } =
      { frame referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  exact step_complete (step_entry_jump calldata gas hgas)

/-- The first executable Route B block consumes the initial `PUSH2; JUMP` and
lands on the first certified trampoline target. -/
theorem execN_to_firstTarget (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Challenge.RouteB.execN 2 (frame referenceBytecode calldata gas) =
      { frame referenceBytecode calldata gas with
          pc := UInt256.ofNat 0x001b
          gasAvailable := gas - 11 } := by
  have hpush : 3 ≤ gas := by omega
  simp [Challenge.RouteB.execN, stepF_entry_push calldata gas hpush,
    stepF_entry_jump calldata gas hgas]

/-- Relational form of the first reference-bytecode block. Later block and
loop proofs compose this theorem with `Reaches.trans`. -/
theorem reaches_firstTarget (calldata : ByteArray) (gas : Nat) (hgas : 11 ≤ gas) :
    Challenge.RouteB.Reaches
      (fun s => s = frame referenceBytecode calldata gas)
      (fun s => s = { frame referenceBytecode calldata gas with
        pc := UInt256.ofNat 0x001b
        gasAvailable := gas - 11 }) := by
  intro s hs
  subst s
  have hpush : 3 ≤ gas := by omega
  exact ⟨_, .trans (step_entry_push calldata gas hpush)
    (.trans (step_entry_jump calldata gas hgas) (.refl _)), rfl⟩

end Challenge.Sha256.RouteB.Reference
