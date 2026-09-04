import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate

def template (j : Nat) (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  match j with
  | 0 => f0Template xAddress rotation
  | 1 => f1Template xAddress rotation constant
  | 2 => f2Template xAddress rotation constant
  | 3 => f3Template xAddress rotation constant
  | _ => f4Template xAddress rotation constant

def leftStartIndex (i : Nat) : Nat :=
  996 + 42 * min i 16 + 46 * min (i - 16) 16 + 47 * min (i - 32) 16 +
    46 * min (i - 48) 16 + 47 * min (i - 64) 16

def rightStartIndex (i : Nat) : Nat :=
  4654 + 47 * min i 16 + 46 * min (i - 16) 16 + 47 * min (i - 32) 16 +
    46 * min (i - 48) 16 + 42 * min (i - 64) 16

def leftAddress (i : Nat) : UInt256 :=
  UInt256.ofNat (672 + 32 * Crypto.Ripemd160.r[i]!)

def rightAddress (i : Nat) : UInt256 :=
  UInt256.ofNat (672 + 32 * Crypto.Ripemd160.rP[i]!)

def leftRotation (i : Nat) : Nat := Crypto.Ripemd160.s[i]!
def rightRotation (i : Nat) : Nat := Crypto.Ripemd160.sP[i]!

def leftConstant (i : Nat) : UInt256 :=
  Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[i / 16]!)

def rightConstant (i : Nat) : UInt256 :=
  Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[i / 16]!)

def leftTemplate (i : Nat) : List Instr :=
  template (i / 16) (leftAddress i) (leftRotation i) (leftConstant i)

def rightTemplate (i : Nat) : List Instr :=
  template (4 - i / 16) (rightAddress i) (rightRotation i) (rightConstant i)

def TemplateWellFormed (instructions : List Instr) : Prop :=
  ∀ i : Fin instructions.length,
    Challenge.EvmProof.Stepper.WellFormed .Osaka instructions[i]

private def plainDecidable (operation : Operation) : Decidable (plainOp operation) := by
  cases operation <;> dsimp only [plainOp] <;> infer_instance

/-- A transparent decision procedure avoids casts in the general Stepper instance. -/
private def instructionWellFormedDecidable (instruction : Instr) :
    Decidable (Challenge.EvmProof.Stepper.WellFormed .Osaka instruction) :=
  match instruction with
  | .push width value => inferInstanceAs (Decidable
      (value.toNat < 256 ^ width.val ∧
        (Operation.Push ⟨width⟩).availableInFork .Osaka = true))
  | .op operation =>
    letI := plainDecidable operation
    inferInstanceAs (Decidable (Decode.opcodeOf (Instr.opByte operation) = some operation ∧
      plainOp operation ∧ operation.availableInFork .Osaka = true))

instance (instructions : List Instr) : Decidable (TemplateWellFormed instructions) :=
  letI := instructionWellFormedDecidable
  inferInstanceAs (Decidable (∀ i : Fin instructions.length,
    Challenge.EvmProof.Stepper.WellFormed .Osaka instructions[i]))

theorem templateWellFormed_mem {instructions : List Instr}
    (h : TemplateWellFormed instructions) :
    ∀ instruction ∈ instructions, Challenge.EvmProof.Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  exact h ⟨i, hi⟩

theorem artifact_code_bound : Artifact.submissionArtifact.code.size < 2 ^ 256 := by
  change submissionBytecode.size < 2 ^ 256
  rw [referenceBytecode_size]
  norm_num

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
