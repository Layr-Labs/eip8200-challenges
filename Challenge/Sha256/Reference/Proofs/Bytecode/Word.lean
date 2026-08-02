import Challenge.EvmProof.Word
set_option warningAsError true
/-!
# SHA-256 operations as EVM word expressions

These definitions mirror the arithmetic/bitwise expressions implemented by
the reference bytecode.  The theorems identify them with the corresponding
operations in `EvmSemantics.Crypto.Sha256`; later symbolic-execution proofs
can therefore rewrite an opcode block to the high-level specification in one
step.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.Word

open EvmSemantics
open Challenge.EvmProof.Word

abbrev EWord := EvmSemantics.UInt256

def evmRotr32 (x : EWord) (n : Nat) : EWord :=
  mask32 (UInt256.shiftRight x (UInt256.ofNat n) |||
    UInt256.shiftLeft x (UInt256.ofNat (32 - n)))

def evmCh (x y z : EWord) : EWord :=
  (x &&& y) ^^^ (~~~x &&& z)

def evmMaj (x y z : EWord) : EWord :=
  ((x &&& y) ^^^ (x &&& z)) ^^^ (y &&& z)

def evmSmallSigma0 (x : EWord) : EWord :=
  (evmRotr32 x 7 ^^^ evmRotr32 x 18) ^^^
    UInt256.shiftRight x (UInt256.ofNat 3)

def evmSmallSigma1 (x : EWord) : EWord :=
  (evmRotr32 x 17 ^^^ evmRotr32 x 19) ^^^
    UInt256.shiftRight x (UInt256.ofNat 10)

def evmBigSigma0 (x : EWord) : EWord :=
  (evmRotr32 x 2 ^^^ evmRotr32 x 13) ^^^ evmRotr32 x 22

def evmBigSigma1 (x : EWord) : EWord :=
  (evmRotr32 x 6 ^^^ evmRotr32 x 11) ^^^ evmRotr32 x 25

@[simp] theorem evmRotr32_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    evmRotr32 (ofUInt32 x) n =
      ofUInt32 (Crypto.Sha256.rotr32 x n) := by
  exact Challenge.EvmProof.Word.evm_rotr32 x n hn0 hn

@[simp] theorem evmCh_ofUInt32 (x y z : UInt32) :
    evmCh (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Sha256.Ch x y z) := by
  have hnot :
      (~~~ofUInt32 x) &&& ofUInt32 z =
        ofUInt32 ((x ^^^ 0xffffffff) &&& z) := by
    rw [and_ofUInt32, toUInt32_not_ofUInt32]
  unfold evmCh Crypto.Sha256.Ch
  rw [← ofUInt32_and, hnot, ← ofUInt32_xor]

@[simp] theorem evmMaj_ofUInt32 (x y z : UInt32) :
    evmMaj (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Sha256.Maj x y z) := by
  unfold evmMaj Crypto.Sha256.Maj
  rw [← ofUInt32_and, ← ofUInt32_and, ← ofUInt32_and,
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmSmallSigma0_ofUInt32 (x : UInt32) :
    evmSmallSigma0 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.smallSigma0 x) := by
  unfold evmSmallSigma0 Crypto.Sha256.smallSigma0 Crypto.Sha256.shr32
  rw [evmRotr32_ofUInt32 x 7 (by decide) (by decide),
    evmRotr32_ofUInt32 x 18 (by decide) (by decide),
    shiftRight_ofUInt32 x 3 (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmSmallSigma1_ofUInt32 (x : UInt32) :
    evmSmallSigma1 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.smallSigma1 x) := by
  unfold evmSmallSigma1 Crypto.Sha256.smallSigma1 Crypto.Sha256.shr32
  rw [evmRotr32_ofUInt32 x 17 (by decide) (by decide),
    evmRotr32_ofUInt32 x 19 (by decide) (by decide),
    shiftRight_ofUInt32 x 10 (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmBigSigma0_ofUInt32 (x : UInt32) :
    evmBigSigma0 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.bigSigma0 x) := by
  unfold evmBigSigma0 Crypto.Sha256.bigSigma0
  rw [evmRotr32_ofUInt32 x 2 (by decide) (by decide),
    evmRotr32_ofUInt32 x 13 (by decide) (by decide),
    evmRotr32_ofUInt32 x 22 (by decide) (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmBigSigma1_ofUInt32 (x : UInt32) :
    evmBigSigma1 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.bigSigma1 x) := by
  unfold evmBigSigma1 Crypto.Sha256.bigSigma1
  rw [evmRotr32_ofUInt32 x 6 (by decide) (by decide),
    evmRotr32_ofUInt32 x 11 (by decide) (by decide),
    evmRotr32_ofUInt32 x 25 (by decide) (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

end Challenge.Sha256.Reference.Proofs.Bytecode.Word
