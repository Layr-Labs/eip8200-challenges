import Challenge.Sha256.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Stepper

namespace Challenge.Sha256.Submission.Proofs.Bytecode.LocatedRange

open EvmSemantics
open EvmSemantics.EVM

private theorem allWellFormed :
    Challenge.EvmProof.Stepper.AllWellFormed Artifact.referenceArtifact .Osaka := by
  unfold Challenge.EvmProof.Stepper.AllWellFormed
  native_decide

def located (index : Fin 810) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  Challenge.EvmProof.Stepper.Located.ofIndex allWellFormed
    ⟨index.val, by
      change index.val < Artifact.referenceInstructions.length
      rw [Artifact.referenceInstructions_count]
      exact index.isLt⟩

def range (start count : Nat) (hbound : start + count ≤ 810) :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  List.ofFn fun index : Fin count =>
    located ⟨start + index.val, by omega⟩

open Lean in
syntax "locatedRange% " num num : term

open Lean in
macro_rules
  | `(locatedRange% $start:num $count:num) => do
      let some startValue := start.raw.isNatLit?
        | Macro.throwErrorAt start "expected a natural-number literal"
      let some countValue := count.raw.isNatLit?
        | Macro.throwErrorAt count "expected a natural-number literal"
      let mut terms : Array (TSyntax `term) := #[]
      for offset in List.range countValue do
        let literal := Syntax.mkNumLit (toString (startValue + offset))
        terms := terms.push (← `(Challenge.Sha256.Submission.Proofs.Bytecode.LocatedRange.located
          $(⟨literal⟩)))
      `([$terms,*])

end Challenge.Sha256.Submission.Proofs.Bytecode.LocatedRange
