import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80RoundSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80CryptoBridge

open Paired80Core Paired80RoundSemantic

abbrev CryptoLane := PairedLaneCryptoBridge.CryptoLane
abbrev bits := PairedLaneCryptoBridge.bits
abbrev cryptoStep := PairedLaneCryptoBridge.cryptoStep

theorem cryptoStep_bits (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt32) (q : CryptoLane) :
    bits (cryptoStep j r message k q) =
      scalarStep j r message.toBitVec k.toBitVec (bits q) := by
  exact PairedLaneCryptoBridge.cryptoStep_bits j r hr0 (by omega) message k q

theorem pairedStep_of_crypto (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 17) (hs0 : 0 < s) (hs : s < 17)
    (wl wr kl kr : UInt32) (l q : CryptoLane) :
    pairedStep j r s (pack wl.toBitVec wr.toBitVec) (pack kl.toBitVec kr.toBitVec)
        (packLane (bits l) (bits q)) =
      packLane (bits (cryptoStep j r wl kl l)) (bits (cryptoStep (4 - j) s wr kr q)) := by
  rw [pairedStep_pack j r s hr0 hr hs0 hs,
    cryptoStep_bits j r hr0 hr, cryptoStep_bits (4 - j) s hs0 hs]

#print axioms cryptoStep_bits
#print axioms pairedStep_of_crypto

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80CryptoBridge
