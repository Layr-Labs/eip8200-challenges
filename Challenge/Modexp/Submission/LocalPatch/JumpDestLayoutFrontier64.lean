import Challenge.Modexp.Submission.LocalPatch.JumpDestLayout
import Challenge.Modexp.Submission.Bytecode

set_option warningAsError true

/-!
# frontier64 binding and executable controls

The baseline byte provider remains the frozen
`Challenge.Modexp.submissionBytecode`. A future generated candidate discharges
one Boolean certificate, then obtains the pinned semantics' complete
`isValidJumpDest` equality for arbitrary destinations.
-/

namespace Challenge.Modexp.Submission.LocalPatch.JumpDestLayoutFrontier64

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.LocalPatch.JumpDestLayout

/-- Candidate-local finite check against the exact frozen frontier64 baseline. -/
def checkCandidate (candidate : ByteArray) : Bool :=
  JumpDestLayout.check Challenge.Modexp.submissionBytecode candidate

/-- Small proof object carried by a candidate-specific transport module. -/
structure Certificate (candidate : ByteArray) : Prop where
  checked : checkCandidate candidate = true

namespace Certificate

/-- Complete target equality, including out-of-range and PUSH-payload bytes. -/
theorem isValidJumpDest_eq {candidate : ByteArray}
    (cert : Certificate candidate) (target : Nat) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode target =
      Decode.isValidJumpDest candidate target :=
  JumpDestLayout.isValidJumpDest_eq_of_check cert.checked target

/-- Rewrite a successful baseline JUMP/JUMPI side condition. -/
theorem valid {candidate : ByteArray}
    (cert : Certificate candidate) {target : Nat}
    (hvalid : Decode.isValidJumpDest
      Challenge.Modexp.submissionBytecode target = true) :
    Decode.isValidJumpDest candidate target = true :=
  JumpDestLayout.valid_of_check cert.checked hvalid

/-- Rewrite a baseline bad-jump side condition. -/
theorem invalid {candidate : ByteArray}
    (cert : Certificate candidate) {target : Nat}
    (hinvalid : Decode.isValidJumpDest
      Challenge.Modexp.submissionBytecode target = false) :
    Decode.isValidJumpDest candidate target = false :=
  JumpDestLayout.invalid_of_check cert.checked hinvalid

end Certificate

/-- Exact frontier64 identity binding. This uses the generic proof, not reduction of
the 5,439-byte literal. -/
theorem frontier64SelfCheck :
    checkCandidate Challenge.Modexp.submissionBytecode = true := by
  exact JumpDestLayout.check_refl _

/-! ## Small nonidentical control

Both arrays have boundaries 0, 2, 3, 6 and the sole JUMPDEST at 2. The left
array deliberately contains `0x5b` inside both PUSH payloads, while the right
array changes those payload bytes. A bytewise same-0x5b-position checker would
reject this valid same-layout rewrite; the boundary scanner accepts it.
-/

def smallBaseline : ByteArray :=
  ByteArray.mk #[0x60, 0x5b, 0x5b, 0x61, 0x5b, 0x60, 0x00]

def smallCandidate : ByteArray :=
  ByteArray.mk #[0x60, 0xaa, 0x5b, 0x61, 0x7f, 0xbb, 0x00]

example : smallBaseline ≠ smallCandidate := by decide

theorem smallControlCheck :
    JumpDestLayout.check smallBaseline smallCandidate = true := by
  decide

theorem smallControlAllTargets (target : Nat) :
    Decode.isValidJumpDest smallBaseline target =
      Decode.isValidJumpDest smallCandidate target :=
  JumpDestLayout.isValidJumpDest_eq_of_check smallControlCheck target

example : Decode.isValidJumpDest smallBaseline 2 = true := by decide
example : Decode.isValidJumpDest smallCandidate 2 = true := by decide

example : Decode.isValidJumpDest smallBaseline 1 = false := by decide
example : Decode.isValidJumpDest smallBaseline 4 = false := by decide
example : Decode.isValidJumpDest smallCandidate 1 = false := by decide
example : Decode.isValidJumpDest smallCandidate 4 = false := by decide

example : Decode.isValidJumpDest smallBaseline 100 = false := by decide
example : Decode.isValidJumpDest smallCandidate 100 = false := by decide

end Challenge.Modexp.Submission.LocalPatch.JumpDestLayoutFrontier64
