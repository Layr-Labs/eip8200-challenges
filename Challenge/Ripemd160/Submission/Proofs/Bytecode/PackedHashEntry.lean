import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSpreadSchedule

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry

open EvmSemantics
open PackedLaneMask PackedLaneInvariant PackedStepCorrected PackedCompression

def packPair (left right : UInt32) : UInt256 :=
  UInt256.ofNat (left.toNat + right.toNat * 2 ^ 64)

theorem packPair_nat (left right : UInt32) :
    (packPair left right).toNat = left.toNat + right.toNat * 2 ^ 64 := by
  rw [packPair, Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hl := left.toNat_lt
  have hr := right.toNat_lt
  norm_num only [Nat.reducePow] at *
  omega

theorem packPair_clean (left right : UInt32) : Clean (packPair left right) := by
  have hl := left.toNat_lt
  have hr := right.toNat_lt
  constructor <;> rw [packPair_nat] <;> norm_num only [Nat.reducePow] at * <;> omega

theorem packPair_represents (left right : UInt32) :
    Represents (packPair left right) left right := by
  have hl := left.toNat_lt
  have hr := right.toNat_lt
  have h0 : lane0N (packPair left right).toNat = left.toNat := by
    rw [packPair_nat]
    simp only [lane0N, windowN, Nat.shiftRight_zero]
    norm_num only [Nat.reducePow] at *
    omega
  have h1 : lane1N (packPair left right).toNat = right.toNat := by
    rw [packPair_nat]
    simp only [lane1N, windowN, Nat.shiftRight_eq_div_pow]
    norm_num only [Nat.reducePow] at *
    omega
  exact ⟨by rw [h0, UInt32.ofNat_toNat], by rw [h1, UInt32.ofNat_toNat]⟩

def initialRegs (h : Compression.HashState) : Regs :=
  ⟨packPair h.h0 h.h0, packPair h.h1 h.h1, packPair h.h2 h.h2,
    packPair h.h3 h.h3, packPair h.h4 h.h4⟩

theorem initialRegs_ok (h : Compression.HashState) : RegsOk (initialRegs h) :=
  ⟨packPair_clean _ _, (packPair_clean _ _).toInv, (packPair_clean _ _).toInv,
    packPair_clean _ _, packPair_clean _ _⟩

theorem initialRegs_represents (h : Compression.HashState) :
    RegsRepresents (initialRegs h) (CompressionCorrect.workingOfHash h)
      (CompressionCorrect.workingOfHash h) :=
  ⟨packPair_represents _ _, packPair_represents _ _, packPair_represents _ _,
    packPair_represents _ _, packPair_represents _ _⟩

/-- Complete arithmetic result from a concrete spread and arbitrary chaining
state. Only preprocessing's initial gap and stored message-word identities
remain as premises; the located bytecode execution is a separate obligation. -/
theorem compress_model (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) :
    PackedCombine.packedCombine (Compression.embedHash h)
      (packedRounds (PackedSpreadSchedule.messageWords memory words)
        (fun i => PackedSpreadSchedule.groupConstant (i / 16)) 80 (initialRegs h))
      = Compression.embedHash (CompressionCorrect.compressModel values h) :=
  PackedSpreadSchedule.compress_from_spread memory words values hgap hv h
    (initialRegs h) (initialRegs_represents h) (initialRegs_ok h)

#print axioms compress_model
#print axioms packPair_nat
#print axioms packPair_clean
#print axioms packPair_represents
#print axioms initialRegs_ok
#print axioms initialRegs_represents

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry
