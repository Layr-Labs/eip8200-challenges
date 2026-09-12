import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
open EvmSemantics EvmSemantics.EVM Paired80WordRound Paired80Compression
open Paired80CryptoBridge (CryptoLane cryptoStep)
open Paired80Algorithm (leftFold rightFold)
open StaggerCoreModel StaggerRepresentation
open StaggerScalarWord (embed)

theorem prologue_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    prologue memory (embed q) = embed (rightFold words 3 q) := by
  have hm0 : low32 (MachineState.readWord memory 50) = words 5 := hm.scalar 5 (by decide)
  have hm1 : low32 (MachineState.readWord memory 310) = words 14 := hm.scalar 31 (by decide)
  have hm2 : low32 (MachineState.readWord memory 350) = words 7 := hm.scalar 35 (by decide)
  unfold prologue right0 right1 right2
  rw [clean_step_of_crypto 4 8 (by decide) (by decide),
    clean_step_of_crypto 4 9 (by decide) (by decide),
    clean_step_of_crypto 4 9 (by decide) (by decide), hm0, hm1, hm2]
  rfl

theorem paired_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    paired memory (embed q) = packCrypto (leftFold words 77 q) (rightFold words 80 q) := by
  rw [paired, prologue_crypto memory words q hm, pair_embed]
  exact StaggerAlgorithm.fold_crypto (message memory) words 77 (by decide) q q hm.paired

def leftFinish (words : Nat → UInt32) (q : CryptoLane) : CryptoLane :=
  cryptoStep 4 6 (words 13) Crypto.Ripemd160.K[4]!
    (cryptoStep 4 5 (words 15) Crypto.Ripemd160.K[4]!
      (cryptoStep 4 8 (words 6) Crypto.Ripemd160.K[4]! q))

theorem leftFinish_fold (words : Nat → UInt32) (q : CryptoLane) :
    leftFinish words (leftFold words 77 q) = leftFold words 80 q := by rfl

theorem epilogue_crypto_general (memory : ByteArray) (words : Nat → UInt32) (q : WordLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory q) = leftFinish words (unpackLeft q) := by
  have hm0 : low32 (MachineState.readWord memory 0) = words 6 := hm.scalar 0 (by decide)
  have hm1 : low32 (MachineState.readWord memory 80) = words 15 := hm.scalar 8 (by decide)
  have hm2 : low32 (MachineState.readWord memory 140) = words 13 := hm.scalar 14 (by decide)
  have h0 := left_c_clean q
  have h1 : StaggerScalarWord.mask (left77 memory (left q)).c = (left77 memory (left q)).c :=
    left_b_clean q
  have h2 : StaggerScalarWord.mask (left78 memory (left77 memory (left q))).c =
      (left78 memory (left77 memory (left q))).c :=
    StaggerScalarWord.step_b_clean false 4 8 (MachineState.readWord memory 0)
      (UInt256.ofNat 2840853838) (left q)
  have p0 := StaggerScalarWord.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 0) (UInt256.ofNat 2840853838) (left q) h0
  have p1 := StaggerScalarWord.project_step false false 4 5 (by decide) (by decide)
    (MachineState.readWord memory 80) (UInt256.ofNat 2840853838) (left77 memory (left q)) h1
  have p2 := StaggerScalarWord.project_step false false 4 6 (by decide) (by decide)
    (MachineState.readWord memory 140) (UInt256.ofNat 2840853838) (left78 memory (left77 memory (left q))) h2
  unfold epilogue
  change unpackLeft (StaggerScalarWord.step false false 4 6 _ _ _) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step false false 4 5 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2, unpackLeft_left]
  rfl

theorem epilogue_crypto (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory (packCrypto l r)) = leftFinish words l := by
  rw [epilogue_crypto_general memory words _ hm, unpackLeft_packCrypto]

#print axioms prologue_crypto
#print axioms paired_crypto
#print axioms epilogue_crypto_general
#print axioms epilogue_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
