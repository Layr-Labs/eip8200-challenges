import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.SeededInverse

open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-- Four correct seed bits suffice for six Newton steps. -/
theorem seed_mod_sixteen (m : Nat) (hodd : m % 2 = 1) :
    m * ((3 * m) ^^^ 2) % 16 = 1 := by
  have hseed : ((3 * m) ^^^ 2) % 16 = ((3 * (m % 16)) % 16) ^^^ 2 := by
    change ((3 * m) ^^^ 2) % 2^4 = _
    rw [Nat.xor_mod_two_pow, Nat.mul_mod]
  have hm : (m % 16) % 2 = 1 := by
    simpa only [Nat.mod_mod_of_dvd m (by decide : 2 ∣ 16)] using hodd
  have hlt : m % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [Nat.mul_mod, hseed]
  generalize m % 16 = q at hm hlt ⊢
  interval_cases q <;> omega

def seededIter (m : Nat) : Nat → Nat
  | 0 => (3 * m) ^^^ 2
  | j + 1 => Model.newtonStep m (seededIter m j)

/-- Generic modular inverse certificate. The diagnostic bytecode still needs
its own exact instruction trace and final Comparator check. -/
theorem seeded_inverse_six (m : Nat) (hodd : m % 2 = 1) :
    m * seededIter m 6 % Limbs.radix = 1 := by
  have h0 : m * seededIter m 0 % 2^4 = 1 % 2^4 := by
    change m * ((3 * m) ^^^ 2) % 16 = 1
    exact seed_mod_sixteen m hodd
  have h1 := Model.newton_step_nat (k := 4) (by decide) h0
    (Model.newtonStep_modEq m (seededIter m 0))
  have h2 := Model.newton_step_nat (k := 8) (by decide) h1
    (Model.newtonStep_modEq m (seededIter m 1))
  have h3 := Model.newton_step_nat (k := 16) (by decide) h2
    (Model.newtonStep_modEq m (seededIter m 2))
  have h4 := Model.newton_step_nat (k := 32) (by decide) h3
    (Model.newtonStep_modEq m (seededIter m 3))
  have h5 := Model.newton_step_nat (k := 64) (by decide) h4
    (Model.newtonStep_modEq m (seededIter m 4))
  have h6 := Model.newton_step_nat (k := 128) (by decide) h5
    (Model.newtonStep_modEq m (seededIter m 5))
  exact h6

theorem seed_word (m : Nat) :
    UInt256.xor (UInt256.ofNat 2) (UInt256.ofNat 3 * UInt256.ofNat m) =
      UInt256.ofNat ((3 * m) ^^^ 2) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((2 % 2^256) ^^^ ((3 % 2^256) * (m % 2^256) % 2^256)) % 2^256 =
    ((3 * m) ^^^ 2) % 2^256
  rw [← Nat.mul_mod, ← Nat.xor_mod_two_pow, Nat.mod_mod, Nat.xor_comm]

#print axioms seed_mod_sixteen
#print axioms seeded_inverse_six

#print axioms seed_word

end Challenge.Modexp.Submission.Proofs.Fast.SeededInverse
