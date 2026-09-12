import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarLow54
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
open EvmSemantics EvmSemantics.EVM
open Paired144WordRound (packCrypto)
open Paired80Compression (low32 unpackLeft)
open Paired80CryptoBridge (CryptoLane cryptoStep)
open Paired80Algorithm (leftFold rightFold)
open StaggerCoreModel StaggerRepresentation
open StaggerScalarWord (embed unpackLeft_packCrypto)

theorem prologue_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    prologue memory (embed q) = embed (rightFold words 3 q) := by
  have hm0 : low32 (MachineState.readWord memory 90) = words 5 := hm.scalar 5 (by decide)
  have hm1 : low32 (MachineState.readWord memory 558) = words 14 := hm.scalar 31 (by decide)
  have hm2 : low32 (MachineState.readWord memory 630) = words 7 := hm.scalar 35 (by decide)
  unfold prologue right0 right1 right2
  rw [clean_step_of_crypto 4 8 (by decide) (by decide),
    clean_step_of_crypto 4 9 (by decide) (by decide),
    clean_step_of_crypto 4 9 (by decide) (by decide), hm0, hm1, hm2]
  rfl

theorem paired_left (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (paired memory (embed q)) = leftFold words 77 q := by
  rw [paired, prologue_crypto memory words q hm, pair_embed]
  rw [StaggerAlgorithm.fold_crypto (message memory) words 76 (by decide) q q
    (fun i hi => hm.paired i (by omega)),
    StaggerAlgorithm.stepFinal_left_of_crypto words 76 (by decide) _ _ _
    (hm.paired 76 (by decide))]
  rfl

theorem paired_right (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    StaggerWord.unpackRightLane (paired memory (embed q)) = rightFold words 80 q := by
  rw [paired, prologue_crypto memory words q hm, pair_embed]
  rw [StaggerAlgorithm.fold_crypto (message memory) words 76 (by decide) q q
    (fun i hi => hm.paired i (by omega)),
    StaggerAlgorithm.stepFinal_right_of_crypto words 76 (by decide) _ _ _
    (hm.paired 76 (by decide))]
  rfl

def leftFinish (words : Nat → UInt32) (q : CryptoLane) : CryptoLane :=
  cryptoStep 4 6 (words 13) Crypto.Ripemd160.K[4]!
    (cryptoStep 4 5 (words 15) Crypto.Ripemd160.K[4]!
      (cryptoStep 4 8 (words 6) Crypto.Ripemd160.K[4]! q))

theorem leftFinish_fold (words : Nat → UInt32) (q : CryptoLane) :
    leftFinish words (leftFold words 77 q) = leftFold words 80 q := by rfl

theorem epilogue_crypto (memory : ByteArray) (words : Nat → UInt32) (q : WordLane)
    (hc0 : StaggerScalarLow54.Low54 (PairedLaneUInt256Bridge.bits q.c))
    (hc1 : StaggerScalarLow54.Low54 (PairedLaneUInt256Bridge.bits q.b))
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory q) = leftFinish words (unpackLeft q) := by
  have hm0 : low32 (MachineState.readWord memory 0) = words 6 := hm.scalar 0 (by decide)
  have hm1 : low32 (MachineState.readWord memory 144) = words 15 := hm.scalar 8 (by decide)
  have hm2 : low32 (MachineState.readWord memory 252) = words 13 := hm.scalar 14 (by decide)
  have h1 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left77 memory q).c) := hc1
  have h2 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left78 memory (left77 memory q)).c) :=
    StaggerScalarLow54.clean_low54 _
      (StaggerScalarWord.step_b_clean false 4 8 (MachineState.readWord memory 0)
        (UInt256.ofNat 2840853838) q)
  have p0 := StaggerScalarLow54.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 0) (UInt256.ofNat 2840853838) q hc0
  have p1 := StaggerScalarLow54.project_step false false 4 5 (by decide) (by decide)
    (MachineState.readWord memory 144) (UInt256.ofNat 2840853838) (left77 memory q) h1
  have p2 := StaggerScalarLow54.project_step false false 4 6 (by decide) (by decide)
    (MachineState.readWord memory 252) (UInt256.ofNat 2840853838)
      (left78 memory (left77 memory q)) h2
  unfold epilogue
  change unpackLeft (StaggerScalarWord.step false false 4 6 _ _ _) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step false false 4 5 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2]
  rfl

#print axioms prologue_crypto
#print axioms paired_crypto
#print axioms epilogue_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
