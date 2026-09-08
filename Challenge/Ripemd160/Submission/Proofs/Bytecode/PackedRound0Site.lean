import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# The first packed round in the final artifact

This module binds `PackedEmit.emitRound Phase.even 0` to the exact frozen
artifact slice at instruction index 501, byte PC 891.  It does not assume a
decoded path: `StackSiteBuilder.ofSlice` derives every located instruction and
PC boundary from `Artifact.submissionArtifact`.

The resulting `StraightLineLocated` certificate is deliberately one round,
not the complete eighty-round program.  Its later stack-cap premise is the
small per-round bound (`19 + 47 < 1024`); the eighty rounds must be composed at
their frame boundaries rather than charged against one coarse 4,000-op bound.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0Site

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

private def instrOp (operation : Operation) : Instr := .op operation
private def instrPush0 : Instr := .push ⟨0, by decide⟩ 0
private def instrPush1 (value : Nat) : Instr :=
  .push ⟨1, by decide⟩ (UInt256.ofNat value)
private def instrDup (index : Fin 16) : Instr := .op (.Dup ⟨index⟩)
private def instrSwap (index : Fin 16) : Instr := .op (.Swap ⟨index⟩)

private theorem encodesInstrDup (index : Fin 16) :
    EncodesShape (.dup (index.val + 1)) (instrDup index) := by
  simpa [instrDup] using EncodesShape.dup index

private theorem encodesInstrSwap (index : Fin 16) :
    EncodesShape (.swap (index.val + 1)) (instrSwap index) := by
  simpa [instrSwap] using EncodesShape.swap index

/-- Exact instruction encoding of `emitRound Phase.even 0`.  DUP/SWAP
arguments here are their zero-based EVM instruction indices. -/
def round0Template : List Instr :=
  [instrPush0, instrOp .MLOAD, instrPush1 88, instrOp .MLOAD, instrOp .OR,
   instrDup 2, instrDup 4, instrOp .XOR, instrDup 9, instrOp .XOR,
   instrDup 4, instrDup 10, instrOp .AND, instrDup 6, instrOp .OR,
   instrOp .XOR, instrOp .ADD, instrOp .ADD, instrDup 15, instrOp .ADD,
   instrDup 5, instrOp .AND, instrDup 8, instrOp .MUL, instrDup 0,
   instrDup 14, instrOp .SHR, instrDup 7, instrOp .AND, instrSwap 0,
   instrPush1 24, instrOp .SHR, instrDup 8, instrOp .AND, instrOp .OR,
   instrDup 4, instrOp .ADD, instrSwap 1, instrDup 5, instrOp .AND,
   instrDup 8, instrOp .MUL, instrDup 14, instrOp .SHR, instrDup 5,
   instrOp .AND, instrSwap 3]

@[simp] theorem round0Template_length : round0Template.length = 47 := rfl

/-- The table-driven emitter specializes definitionally to the independently
transcribed round-0 operation model. -/
theorem emitRound_even_zero : emitRound Phase.even 0 = step0Ops := by
  rfl

private theorem step0_encoding :
    EncodesSequence step0Ops round0Template := by
  repeat' first
    | exact EncodesSequence.nil
    | apply EncodesSequence.cons
    | apply EncodesShape.push0
    | apply EncodesShape.push
    | apply EncodesShape.mload
    | exact encodesInstrDup (0 : Fin 16)
    | exact encodesInstrDup (2 : Fin 16)
    | exact encodesInstrDup (4 : Fin 16)
    | exact encodesInstrDup (5 : Fin 16)
    | exact encodesInstrDup (6 : Fin 16)
    | exact encodesInstrDup (7 : Fin 16)
    | exact encodesInstrDup (8 : Fin 16)
    | exact encodesInstrDup (9 : Fin 16)
    | exact encodesInstrDup (10 : Fin 16)
    | exact encodesInstrDup (14 : Fin 16)
    | exact encodesInstrDup (15 : Fin 16)
    | exact encodesInstrSwap (0 : Fin 16)
    | exact encodesInstrSwap (1 : Fin 16)
    | exact encodesInstrSwap (3 : Fin 16)
    | apply EncodesShape.pop
    | apply EncodesShape.land
    | apply EncodesShape.lor
    | apply EncodesShape.xor
    | apply EncodesShape.add
    | apply EncodesShape.mul
    | apply EncodesShape.shr
    | decide

theorem emitRound_even_zero_encoding :
    EncodesSequence (emitRound Phase.even 0) round0Template := by
  rw [emitRound_even_zero]
  exact step0_encoding

private theorem round0_slice :
    (Artifact.submissionArtifact.instructions.drop 501).take
      round0Template.length = round0Template := by
  rfl

private theorem round0_fits :
    501 + round0Template.length ≤
      Artifact.submissionArtifact.instructions.length := by
  change 501 + round0Template.length ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  decide

private theorem round0_wellFormed :
    ∀ instruction ∈ round0Template,
      Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

/-- Exact final-artifact location of packed round 0. -/
def round0Site : GenericRoundSite Artifact.submissionArtifact .Osaka
    round0Template :=
  StackSiteBuilder.ofSlice round0Template 501 round0_slice round0_fits
    StackRoundData.artifact_code_bound round0_wellFormed (by decide)

@[simp] theorem round0Site_startPC :
    round0Site.startPC = UInt256.ofNat 891 := by
  rfl

@[simp] theorem round0Site_endPC :
    round0Site.endPC = UInt256.ofNat 940 := by
  rfl

/-- The emitter's first round and the exact final artifact slice form the
located straight-line path required by `roundsCertificate`. -/
theorem round0_straightLine :
    StraightLineLocated (emitRound Phase.even 0) round0Site.path := by
  exact straightLineLocated_of_genericRoundSite round0Site
    emitRound_even_zero_encoding

#print axioms round0_straightLine

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0Site
