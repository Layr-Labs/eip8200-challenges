import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.EvmProof.Word
import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PatternedScan
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := DataStepper.Located HoistedInherited.Artifact.submissionArtifact .Osaka

/-- The scanner's segment end `min size 251`, in the shape the scanner frame uses (`J2Raw.clamp`). -/
def segEnd (n : Nat) : UInt256 :=
  UInt256.add (UInt256.ofNat n)
    (UInt256.mul (UInt256.lt (UInt256.ofNat 251) (UInt256.ofNat n)) (UInt256.sub (UInt256.ofNat 251) (UInt256.ofNat n)))

/-- The private scanners need no lower saved stack words on any route. -/
def entryRho (_n : Nat) : List UInt256 := []

@[simp] theorem entryRho_length (n : Nat) : (entryRho n).length ≤ 1 := by
  simp [entryRho]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PatternedScan
