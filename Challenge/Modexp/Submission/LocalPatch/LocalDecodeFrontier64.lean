import Challenge.Modexp.Submission.LocalPatch.LocalDecode
import Challenge.Modexp.Submission.Bytecode

set_option warningAsError true

/-!
# frontier64 local-decode binding and controls
-/

namespace Challenge.Modexp.Submission.LocalPatch.LocalDecodeFrontier64

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.LocalPatch.LocalDecode

def checkCandidateAt (candidate : ByteArray) (pc : Nat) : Bool :=
  LocalDecode.checkAt Challenge.Modexp.submissionBytecode candidate pc

def checkCandidateWindows (candidate : ByteArray) (pcs : List Nat) : Bool :=
  LocalDecode.checkMany Challenge.Modexp.submissionBytecode candidate pcs

/-- Candidate-local finite certificate for all listed untouched PCs. -/
structure Certificate (candidate : ByteArray) (pcs : List Nat) : Prop where
  checked : checkCandidateWindows candidate pcs = true

namespace Certificate

theorem decodeAt_eq {candidate : ByteArray} {pcs : List Nat}
    (cert : Certificate candidate pcs) {pc : Nat} (hpc : pc ∈ pcs) :
    Decode.decodeAt Challenge.Modexp.submissionBytecode pc =
      Decode.decodeAt candidate pc :=
  LocalDecode.decodeAt_eq_of_checkMany cert.checked hpc

end Certificate

/-- Identity control for the exact frozen frontier64 byte provider. -/
theorem frontier64SelfCheck (pcs : List Nat) :
    checkCandidateWindows Challenge.Modexp.submissionBytecode pcs = true :=
  LocalDecode.checkMany_refl _ _

/-! ## Small nonidentical controls

The arrays differ at PC 0. Their untouched windows demonstrate an ordinary
PUSH, EIP-8024 immediate decoding, a truncated final PUSH, and out-of-range
implicit STOP.
-/

def smallBaseline : ByteArray :=
  ByteArray.mk #[0x00, 0x60, 0x2a, 0xe6, 0x05, 0x61, 0xaa]

def smallCandidate : ByteArray :=
  ByteArray.mk #[0x01, 0x60, 0x2a, 0xe6, 0x05, 0x61, 0xaa]

def smallPCs : List Nat := [1, 3, 5, 100]

example : smallBaseline ≠ smallCandidate := by decide

example : windowLength smallBaseline 1 = 2 := by decide
example : windowLength smallBaseline 3 = 2 := by decide
example : windowLength smallBaseline 5 = 3 := by decide
example : windowLength smallBaseline 100 = 0 := by decide

theorem smallCheck :
    LocalDecode.checkMany smallBaseline smallCandidate smallPCs = true := by
  decide

theorem smallDecodeAt (pc : Nat) (hpc : pc ∈ smallPCs) :
    Decode.decodeAt smallBaseline pc =
      Decode.decodeAt smallCandidate pc :=
  LocalDecode.decodeAt_eq_of_checkMany smallCheck hpc

end Challenge.Modexp.Submission.LocalPatch.LocalDecodeFrontier64
