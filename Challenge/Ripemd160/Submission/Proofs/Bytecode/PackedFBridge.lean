import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedF
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Packed Boolean-function bridge

This module connects the two proved packed `Nat` lanes to the actual UInt256
opcode expression and to the pinned RIPEMD-160 Boolean function.  Rotation and
round-state refinement are intentionally outside this boundary.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant

private theorem bnot32_toNat (x : UInt32) :
    (Crypto.Ripemd160.bnot32 x).toNat = maskLN ^^^ x.toNat := by
  unfold Crypto.Ripemd160.bnot32 maskLN
  rw [UInt32.toNat_xor]
  change x.toNat ^^^ (2 ^ 32 - 1) = (2 ^ 32 - 1) ^^^ x.toNat
  exact Nat.xor_comm _ _

/-- `PackedF.natF` is exactly the pinned RIPEMD Boolean function on UInt32
inputs. -/
theorem natF_toNat (j : Nat) (x y z : UInt32) (hj : j < 5) :
    PackedF.natF j x.toNat y.toNat z.toNat =
      (Crypto.Ripemd160.f j x y z).toNat := by
  interval_cases j <;>
    simp [PackedF.natF, Crypto.Ripemd160.f, UInt32.toNat_and,
      UInt32.toNat_or, UInt32.toNat_xor, bnot32_toNat]

/-- Bounded-`Nat` form used directly by lane projection. -/
theorem natF_eq_ripemdF (j x y z : Nat) (hj : j < 5)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) :
    PackedF.natF j x y z =
      (Crypto.Ripemd160.f j (UInt32.ofNat x) (UInt32.ofNat y)
        (UInt32.ofNat z)).toNat := by
  have h := natF_toNat j (UInt32.ofNat x) (UInt32.ofNat y)
    (UInt32.ofNat z) hj
  simp only [UInt32.toNat_ofNat'] at h
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hz] at h
  exact h

private theorem word_toNat_lxor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.toNat ^^^ b.toNat) % UInt256.size = _
  rw [show UInt256.size = 2 ^ 256 from rfl]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.val.isLt b.val.isLt)

/-- The exact UInt256 Boolean expression used by a packed round group. -/
def packedFWord (r : Nat) (x y z : UInt256) : UInt256 :=
  match r with
  | 0 => UInt256.xor (UInt256.xor (UInt256.xor x y) maskR)
      (UInt256.lor (UInt256.land y maskR) z)
  | 1 => UInt256.xor
      (UInt256.xor (UInt256.land (UInt256.xor y z) x) z)
      (UInt256.land
        (UInt256.xor (UInt256.land x y) (UInt256.lor y z)) maskR)
  | 2 => UInt256.xor (UInt256.lor (UInt256.xor y maskLR) x) z
  | 3 => UInt256.xor
      (UInt256.xor (UInt256.land (UInt256.xor x y) z) y)
      (UInt256.land
        (UInt256.xor (UInt256.land x y) (UInt256.lor y z)) maskR)
  | _ => UInt256.xor (UInt256.xor (UInt256.xor x y) maskL)
      (UInt256.lor (UInt256.land y maskL) z)

/-- Transport the actual UInt256 opcode expression to the proved packed-`Nat`
expression without imposing lane invariants. -/
theorem packedFWord_toNat (r : Nat) (x y z : UInt256) (hr : r < 5) :
    (packedFWord r x y z).toNat =
      PackedF.natPackedF r x.toNat y.toNat z.toNat := by
  interval_cases r <;>
    simp [packedFWord, PackedF.natPackedF, word_toNat_lxor,
      Challenge.EvmProof.Word.word_toNat_land,
      Challenge.EvmProof.Word.word_toNat_lor, maskL_toNat, maskR_toNat,
      maskLR_toNat]

theorem packedFWord_lane0_ripemdF (r : Nat) (x y z : UInt256)
    (hr : r < 5) :
    lane0N (packedFWord r x y z).toNat =
      (Crypto.Ripemd160.f r (UInt32.ofNat (lane0N x.toNat))
        (UInt32.ofNat (lane0N y.toNat))
        (UInt32.ofNat (lane0N z.toNat))).toNat := by
  rw [packedFWord_toNat r x y z hr, PackedF.packedF_lane0 r _ _ _ hr]
  exact natF_eq_ripemdF r _ _ _ hr (windowN_lt _ _) (windowN_lt _ _)
    (windowN_lt _ _)

theorem packedFWord_lane1_ripemdF (r : Nat) (x y z : UInt256)
    (hr : r < 5) :
    lane1N (packedFWord r x y z).toNat =
      (Crypto.Ripemd160.f (4 - r) (UInt32.ofNat (lane1N x.toNat))
        (UInt32.ofNat (lane1N y.toNat))
        (UInt32.ofNat (lane1N z.toNat))).toNat := by
  rw [packedFWord_toNat r x y z hr, PackedF.packedF_lane1 r _ _ _ hr]
  exact natF_eq_ripemdF (4 - r) _ _ _ (by omega) (windowN_lt _ _)
    (windowN_lt _ _) (windowN_lt _ _)

/-- UInt32 projection form analogous to `ScratchLow.stackF_project`. -/
theorem packedFWord_lane0_project (r : Nat) (x y z : UInt256)
    (hr : r < 5) :
    UInt32.ofNat (lane0N (packedFWord r x y z).toNat) =
      Crypto.Ripemd160.f r (UInt32.ofNat (lane0N x.toNat))
        (UInt32.ofNat (lane0N y.toNat))
        (UInt32.ofNat (lane0N z.toNat)) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', lane0N,
    Nat.mod_eq_of_lt (windowN_lt (packedFWord r x y z).toNat 0)]
  exact packedFWord_lane0_ripemdF r x y z hr

theorem packedFWord_lane1_project (r : Nat) (x y z : UInt256)
    (hr : r < 5) :
    UInt32.ofNat (lane1N (packedFWord r x y z).toNat) =
      Crypto.Ripemd160.f (4 - r) (UInt32.ofNat (lane1N x.toNat))
        (UInt32.ofNat (lane1N y.toNat))
        (UInt32.ofNat (lane1N z.toNat)) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', lane1N,
    Nat.mod_eq_of_lt (windowN_lt (packedFWord r x y z).toNat 64)]
  exact packedFWord_lane1_ripemdF r x y z hr

#print axioms natF_eq_ripemdF
#print axioms packedFWord_toNat
#print axioms packedFWord_lane0_project
#print axioms packedFWord_lane1_project

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFBridge
