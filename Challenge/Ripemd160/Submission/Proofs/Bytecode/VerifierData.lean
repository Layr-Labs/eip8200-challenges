import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# Straight-line patterned-input verifier data

The verifier replaces the affine scan loop with literal `PUSH32` word
comparisons.  Each verifier block folds `lor (xor expected (readWord input
off))` over a fixed list of offsets into one accumulator; the accumulator is
zero exactly when the calldata equals the patterned prefix of that length.

`expectedWordAtOffset off` generalises `expectedWordAt j` to arbitrary byte
offsets so the unaligned tail compare (`off = size - 32`) can reuse the same
machinery.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierData

open EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedWordData PatternedWordLogic
open KnownInputLogic

/-- Word starting at byte offset `off`, most significant byte first. -/
def patternedWordNatAt (off : Nat) : Nat :=
  (List.range 32).foldl (fun acc k => acc * 256 + (paddedByte (off + k)).toNat) 0

def expectedWordAtOffset (off : Nat) : UInt256 := UInt256.ofNat (patternedWordNatAt off)

theorem expectedWordAtOffset_aligned (j : Nat) :
    expectedWordAtOffset (32 * j) = expectedWordAt j := rfl

/-- `CALLDATALOAD` on the patterned vector at an arbitrary offset. -/
theorem readWord_patterned_offset (off : Nat) :
    MachineState.readWord patternedInput off = expectedWordAtOffset off := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  unfold expectedWordAtOffset patternedWordNatAt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : ∀ k, (paddedByte (off + k)).toNat < 256 := fun k => (paddedByte (off + k)).toNat_lt
  have gen : ∀ (l : List Nat) (a : Nat),
      l.foldl (fun acc k => acc * 256 + (paddedByte (off + k)).toNat) a
        < 256 ^ l.length * 256 + a := by
    intro l a
    induction l generalizing a with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.length_cons]
        have hx := hb x
        have h := ih (a * 256 + (paddedByte (off + x)).toNat)
        omega
  have h := gen (List.range 32) 0
  simpa using h

/-- The compare offsets for a verifier of `size` bytes: aligned words plus the
unaligned tail word when `size` is not a multiple of 32. -/
def compareOffsets (size : Nat) : List Nat :=
  (List.range (size / 32)).map (fun j => 32 * j) ++
    (if size % 32 = 0 then [] else [size - 32])

/-- Expected word for a `< 32`-byte verifier: `n` `0x61` bytes then zeros,
matching `readWord`'s zero-padding of a short input. -/
def expectedShortNat (n : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc k => acc * 256 + (if k < n then (paddedByte k).toNat else 0)) 0

def expectedShort (n : Nat) : UInt256 := UInt256.ofNat (expectedShortNat n)

/-- The compare pairs for a verifier of `size` bytes.  For `size < 32` a
single word compare against `expectedShort` suffices; for `size ≥ 32` the
aligned words plus the unaligned tail. -/
def comparePairs (size : Nat) : List (Nat × UInt256) :=
  if size < 32 then [(0, expectedShort size)]
  else (compareOffsets size).map (fun off => (off, expectedWordAtOffset off))

/-- The verifier accumulator, in the exact operand order `runInstr` produces:
each compare pushes `xor (readWord input off) expected` then `or diff acc`. -/
def verifyAccRaw (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      verifyAccRaw input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

/-- The verifier accumulator. -/
def verifyAcc (input : ByteArray) (size : Nat) : UInt256 :=
  verifyAccRaw input (comparePairs size) 0

theorem verifyAccRaw_eq_scanDiff (input : ByteArray)
    (xs : List (Nat × UInt256)) (acc : UInt256) :
    verifyAccRaw input xs acc = scanDiff input xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons p ps ih =>
      rw [verifyAccRaw, scanDiff, ih, UInt256.xor_comm]

theorem verifyAcc_zero_iff (input : ByteArray) (size : Nat) :
    verifyAcc input size = 0 ↔
      ∀ p, p ∈ comparePairs size →
        MachineState.readWord input p.1 = p.2 := by
  rw [verifyAcc, verifyAccRaw_eq_scanDiff, scanDiff_eq_zero_iff]
  simp

/-- For `size ≥ 32`, `verifyAcc = 0` iff every compare-offset word matches. -/
theorem verifyAcc_zero_iff_offsets (input : ByteArray) (size : Nat)
    (hn32 : 32 ≤ size) :
    verifyAcc input size = 0 ↔
      ∀ off, off ∈ compareOffsets size →
        MachineState.readWord input off = expectedWordAtOffset off := by
  rw [verifyAcc, verifyAccRaw_eq_scanDiff, scanDiff_eq_zero_iff]
  simp only [comparePairs, if_neg (by omega : ¬ size < 32),
    List.mem_map, forall_exists_index, and_imp,
    Prod.forall, Prod.mk.injEq]
  constructor
  · intro h off hoff
    exact h off (expectedWordAtOffset off) hoff rfl
  · intro h off w hoff hw
    rw [← hw]; exact h off hoff


end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierData
