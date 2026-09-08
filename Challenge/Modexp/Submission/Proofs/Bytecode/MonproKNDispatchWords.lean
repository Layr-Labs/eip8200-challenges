import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNResidue

set_option warningAsError true

/-! The two concrete eight-copy address calculations, without an Artifact. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatchWords

open EvmSemantics
open MonproKNResidue

theorem ofNat_mul (left right : Nat) :
    UInt256.ofNat left * UInt256.ofNat right = UInt256.ofNat (left * right) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((left % (2 ^ 256)) * (right % (2 ^ 256))) % (2 ^ 256) =
    (left * right) % (2 ^ 256)
  exact (Nat.mul_mod left right (2 ^ 256)).symm

theorem address_value (base stride slot : Nat) :
    UInt256.ofNat base + UInt256.ofNat stride * UInt256.ofNat slot =
      UInt256.ofNat (base + stride * slot) := by
  rw [ofNat_mul, Challenge.EvmProof.Word.ofNat_add_mod]

def l1PC (slot : Nat) : Nat := 4089 + 38 * slot
def l2PC (slot : Nat) : Nat := 2098 + 41 * slot

theorem l1PCs : (List.range 8).map l1PC =
    [4089, 4127, 4165, 4203, 4241, 4279, 4317, 4355] := by decide

theorem l2PCs : (List.range 8).map l2PC =
    [2098, 2139, 2180, 2221, 2262, 2303, 2344, 2385] := by decide

theorem l1_selector (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 9472) (hn : n ≤ 32) (hj : j < n) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight
        (UInt256.ofNat (pa - 32) - UInt256.ofNat (pa + 32 * (n - 1 - j)))
        (UInt256.ofNat 5)) = UInt256.ofNat (residue (n - j)) := by
  exact dispatch_value (pa - 32) (pa + 32 * (n - 1 - j)) (n - j)
    (by omega) (by omega) (by omega) (by omega) (by omega)

theorem l2_selector (n k : Nat) (hn : n ≤ 32) (hk : k + 1 < n) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight
        (UInt256.ofNat 8224 - UInt256.ofNat (8256 + 32 * (n - 2 - k)))
        (UInt256.ofNat 5)) = UInt256.ofNat (residue (n - 1 - k)) := by
  exact dispatch_value 8224 (8256 + 32 * (n - 2 - k)) (n - 1 - k)
    (by omega) (by omega) (by norm_num) (by omega) (by omega)

/-- Width two starts at the final L2 copy: exactly one multiply-accumulate. -/
theorem l2_n2_entry : l2PC (residue (2 - 1 - 0)) = 2385 := by decide

theorem l1PC_next (slot : Nat) : l1PC slot + 38 = l1PC (slot + 1) := by
  simp only [l1PC]
  omega

theorem l2PC_next (slot : Nat) : l2PC slot + 41 = l2PC (slot + 1) := by
  simp only [l2PC]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatchWords
