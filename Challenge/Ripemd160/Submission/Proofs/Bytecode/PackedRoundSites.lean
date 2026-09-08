import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0Site

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact final-artifact sites for all eighty packed rounds

Every packed operation occupies one decoded instruction.  The five RIPEMD
groups have round lengths 47/53/43/53/47, and the three-instruction constant
swap after each of rounds 15, 31, 47 and 63 is reflected in the five closed
group bases below.  Thus a round site can be selected without charging a
single coarse stack budget for all eighty rounds.

This module deliberately stops at one `StraightLineLocated` certificate per
round.  A whole-compression gas proof must apply `roundsCertificate` with the
nineteen-word frame bound at each round, execute the four boundary swaps, and
compose the resulting `GasSteps`; it must not use `19 + emitRounds.length` as
a stack-cap premise.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

/-- Physical register phase at the entry of round `i`. -/
def phaseAt (i : Nat) : Phase :=
  if i % 2 = 0 then .even else .odd

/-- Exact decoded-instruction index of round `i` in the final 5363-byte
artifact.  The bases include all preceding three-op constant swaps. -/
def roundStartIndex (i : Nat) : Nat :=
  match i / 16 with
  | 0 => 501 + 47 * (i % 16)
  | 1 => 1256 + 53 * (i % 16)
  | 2 => 2107 + 43 * (i % 16)
  | 3 => 2798 + 53 * (i % 16)
  | _ => 3649 + 47 * (i % 16)

private def depthIndex (depth : Nat) : Fin 16 :=
  ⟨(depth - 1) % 16, Nat.mod_lt _ (by decide)⟩

/-- Instruction selected by the packed round emitter.  Round-local literal
pushes are all one byte; the wider `packedK` pushes live between round sites
and are intentionally outside this encoder. -/
def encodeRoundOp : Op → Instr
  | .push0 => .push ⟨0, by decide⟩ 0
  | .push value => .push ⟨1, by decide⟩ value
  | .mload => .op .MLOAD
  | .dup depth => .op (.Dup ⟨depthIndex depth⟩)
  | .swap depth => .op (.Swap ⟨depthIndex depth⟩)
  | .pop => .op .POP
  | .and => .op .AND
  | .or => .op .OR
  | .xor => .op .XOR
  | .add => .op .ADD
  | .mul => .op .MUL
  | .shr => .op .SHR

/-- The only nontrivial encodability condition in the round opcode subset:
EVM DUP/SWAP depths are one-based and range from one through sixteen. -/
def Encodable : Op → Prop
  | .dup depth | .swap depth => 1 ≤ depth ∧ depth ≤ 16
  | _ => True

private instance encodableDecidable (op : Op) : Decidable (Encodable op) := by
  cases op <;> unfold Encodable <;> infer_instance

/-- Finite-index form of encodability.  This avoids asking typeclass search to
decide an unbounded `∀ op : Op` merely because membership appears as a guard. -/
private def OpsEncodable (ops : List Op) : Prop :=
  ∀ i : Fin ops.length, Encodable ops[i]

private instance opsEncodableDecidable (ops : List Op) :
    Decidable (OpsEncodable ops) :=
  inferInstanceAs (Decidable (∀ i : Fin ops.length, Encodable ops[i]))

private theorem encodable_mem_of_opsEncodable {ops : List Op}
    (h : OpsEncodable ops) : ∀ op ∈ ops, Encodable op := by
  intro op hmem
  obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  exact h ⟨index, hi⟩

private theorem encodesShape_encodeRoundOp (op : Op) (h : Encodable op) :
    EncodesShape op (encodeRoundOp op) := by
  cases op with
  | push0 => exact EncodesShape.push0
  | push value =>
      exact EncodesShape.push (⟨1, by decide⟩ : Fin 33) value (by decide)
  | mload => exact EncodesShape.mload
  | dup depth =>
      rcases h with ⟨hpos, hupper⟩
      have hlt : depth - 1 < 16 := by
        omega
      have hmod : (depth - 1) % 16 = depth - 1 := Nat.mod_eq_of_lt hlt
      have hdepth : depth - 1 + 1 = depth := by
        omega
      simpa [encodeRoundOp, depthIndex, hmod, hdepth] using
        (EncodesShape.dup (⟨depth - 1, hlt⟩ : Fin 16))
  | swap depth =>
      rcases h with ⟨hpos, hupper⟩
      have hlt : depth - 1 < 16 := by
        omega
      have hmod : (depth - 1) % 16 = depth - 1 := Nat.mod_eq_of_lt hlt
      have hdepth : depth - 1 + 1 = depth := by
        omega
      simpa [encodeRoundOp, depthIndex, hmod, hdepth] using
        (EncodesShape.swap (⟨depth - 1, hlt⟩ : Fin 16))
  | pop => exact EncodesShape.pop
  | and => exact EncodesShape.land
  | or => exact EncodesShape.lor
  | xor => exact EncodesShape.xor
  | add => exact EncodesShape.add
  | mul => exact EncodesShape.mul
  | shr => exact EncodesShape.shr

private theorem encodesSequence_map (ops : List Op)
    (h : ∀ op ∈ ops, Encodable op) :
    EncodesSequence ops (ops.map encodeRoundOp) := by
  induction ops with
  | nil => exact EncodesSequence.nil
  | cons op ops ih =>
      exact EncodesSequence.cons
        (encodesShape_encodeRoundOp op (h op List.mem_cons_self))
        (ih (by
          intro tailOp hmem
          exact h tailOp (List.mem_cons_of_mem op hmem)))

/-- The exact instruction template emitted for round `i`. -/
def roundTemplate (i : Fin 80) : List Instr :=
  (emitRound (phaseAt i.val) i.val).map encodeRoundOp

private theorem roundOps_encodable (i : Fin 80) :
    ∀ op ∈ emitRound (phaseAt i.val) i.val, Encodable op := by
  apply encodable_mem_of_opsEncodable
  fin_cases i <;> decide

theorem round_encoding (i : Fin 80) :
    EncodesSequence (emitRound (phaseAt i.val) i.val) (roundTemplate i) := by
  exact encodesSequence_map _ (roundOps_encodable i)

/-- Finite exact-byte binding for every one of the eighty final-artifact round
slices.  This is an instruction-list equality, not a decoded-path premise. -/
private theorem round_slice (i : Fin 80) :
    (Artifact.submissionArtifact.instructions.drop (roundStartIndex i.val)).take
      (roundTemplate i).length = roundTemplate i := by
  fin_cases i <;> rfl

private theorem round_fits (i : Fin 80) :
    roundStartIndex i.val + (roundTemplate i).length ≤
      Artifact.submissionArtifact.instructions.length := by
  change roundStartIndex i.val + (roundTemplate i).length ≤
    Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  fin_cases i <;> decide

private theorem round_wellFormed (i : Fin 80) :
    ∀ instruction ∈ roundTemplate i,
      Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by
    fin_cases i <;> decide)

private theorem round_nonempty (i : Fin 80) : roundTemplate i ≠ [] := by
  fin_cases i <;> decide

/-- Exact final-artifact located site for any packed round. -/
def roundSite (i : Fin 80) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (roundTemplate i) :=
  StackSiteBuilder.ofSlice (roundTemplate i) (roundStartIndex i.val)
    (round_slice i) (round_fits i) StackRoundData.artifact_code_bound
    (round_wellFormed i) (round_nonempty i)

/-- One small located certificate per round.  This is the reusable input to a
per-round `roundsCertificate`; it is not a whole-compression execution claim. -/
theorem round_straightLine (i : Fin 80) :
    StraightLineLocated (emitRound (phaseAt i.val) i.val) (roundSite i).path := by
  exact straightLineLocated_of_genericRoundSite (roundSite i) (round_encoding i)

#print axioms round_straightLine

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSites
