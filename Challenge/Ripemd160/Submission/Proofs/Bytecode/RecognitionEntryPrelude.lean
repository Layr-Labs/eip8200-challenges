import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.EvmProof.Word
import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := DataStepper.Located Artifact.submissionArtifact .Osaka

/-- The scanner's segment end `min size 251`, in the shape the scanner frame uses (`J2Raw.clamp`). -/
def segEnd (n : Nat) : UInt256 :=
  UInt256.add (UInt256.ofNat n)
    (UInt256.mul (UInt256.lt (UInt256.ofNat 251) (UInt256.ofNat n)) (UInt256.sub (UInt256.ofNat 251) (UInt256.ofNat n)))

/-- Dispatch retains the length on short routes. Long routes need no saved word. -/
def entryRho (n : Nat) : List UInt256 :=
  if n ≤ 128 then [UInt256.ofNat n] else []

@[simp] theorem entryRho_length (n : Nat) : (entryRho n).length ≤ 1 := by
  unfold entryRho
  split <;> simp

/-- The private recognizer entry with its actual dispatch-defined saved tail. -/
def patternedEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 4786, stack := entryRho input.size }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
