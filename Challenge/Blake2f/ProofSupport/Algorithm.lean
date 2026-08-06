import Challenge.Blake2f.ProofSupport.Word
set_option warningAsError true

/-!
# Reusable pure model of BLAKE2f rounds

This module names the eight-quarter-round transition and iteration used by the
pinned crypto specification. Candidate proofs can maintain this model without
depending on the bundled reference's memory layout or control flow.
-/

namespace Challenge.Blake2f.ProofSupport.Algorithm

open EvmSemantics

/-- One complete BLAKE2b mixing round, including columns then diagonals. -/
def roundStep (message : Array UInt64) (v : Array UInt64) (round : Nat) :
    Array UInt64 :=
  let sigma := Crypto.Blake2f.SIGMA[round % 10]!
  let v := Crypto.Blake2f.mixG v 0 4 8 12 message[sigma[0]!]! message[sigma[1]!]!
  let v := Crypto.Blake2f.mixG v 1 5 9 13 message[sigma[2]!]! message[sigma[3]!]!
  let v := Crypto.Blake2f.mixG v 2 6 10 14 message[sigma[4]!]! message[sigma[5]!]!
  let v := Crypto.Blake2f.mixG v 3 7 11 15 message[sigma[6]!]! message[sigma[7]!]!
  let v := Crypto.Blake2f.mixG v 0 5 10 15 message[sigma[8]!]! message[sigma[9]!]!
  let v := Crypto.Blake2f.mixG v 1 6 11 12 message[sigma[10]!]! message[sigma[11]!]!
  let v := Crypto.Blake2f.mixG v 2 7 8 13 message[sigma[12]!]! message[sigma[13]!]!
  Crypto.Blake2f.mixG v 3 4 9 14 message[sigma[14]!]! message[sigma[15]!]!

/-- Iterate the mathematical round transition in execution order. -/
def rounds (message : Array UInt64) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | count + 1, v => roundStep message (rounds message count v) count

@[simp] theorem rounds_zero (message v) : rounds message 0 v = v := rfl

theorem rounds_succ (message v) (count : Nat) :
    rounds message (count + 1) v =
      roundStep message (rounds message count v) count := rfl

end Challenge.Blake2f.ProofSupport.Algorithm
