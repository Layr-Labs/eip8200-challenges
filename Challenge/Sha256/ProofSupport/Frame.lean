import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Canonical-frame proof facts

Small projections and side conditions used by submission proofs. They are facts
about the frame defined in `Spec.lean`, not part of the statement an auditor
must accept.
-/

namespace Challenge.Sha256

open EvmSemantics
open EvmSemantics.EVM

theorem frame_pc (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).pc = UInt256.ofNat 0 := rfl

theorem frame_stack (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).stack = [] := rfl

theorem frame_gas (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).gasAvailable = gas := rfl

theorem frame_calldata (code calldata : ByteArray) (gas : Nat) :
    (frame code calldata gas).executionEnv.calldata = calldata := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompile .Osaka deployAddress = false := by
  decide

end Challenge.Sha256
