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

theorem paired_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    ∃ d : UInt256,
      paired memory (embed q) =
        {packCrypto (leftFold words 77 q) (rightFold words 80 q) with e:=d} ∧
      UInt256.land d Paired144WordRound.pairWord =
        (packCrypto (leftFold words 77 q) (rightFold words 80 q)).e := by
  rw [paired, prologue_crypto memory words q hm, pair_embed]
  exact StaggerTerminal75.final_shape (message memory) words q q hm.paired

def leftFinish (words : Nat → UInt32) (q : CryptoLane) : CryptoLane :=
  cryptoStep 4 6 (words 13) Crypto.Ripemd160.K[4]!
    (cryptoStep 4 5 (words 15) Crypto.Ripemd160.K[4]!
      (cryptoStep 4 8 (words 6) Crypto.Ripemd160.K[4]! q))

theorem leftFinish_fold (words : Nat → UInt32) (q : CryptoLane) :
    leftFinish words (leftFold words 77 q) = leftFold words 80 q := by rfl

theorem epilogue_project (memory : ByteArray) (words : Nat → UInt32) (q : Paired144WordRound.WordLane)
    (hm : StaggerMessage.Ready memory words)
    (hb : StaggerScalarLow54.Low54 (PairedLaneUInt256Bridge.bits q.b))
    (hc : StaggerScalarLow54.Low54 (PairedLaneUInt256Bridge.bits q.c)) :
    unpackLeft (epilogue memory q) = leftFinish words (unpackLeft q) := by
  have hm0 : low32 (MachineState.readWord memory 0) = words 6 := hm.scalar 0 (by decide)
  have hm1 : low32 (MachineState.readWord memory 144) = words 15 := hm.scalar 8 (by decide)
  have hm2 : low32 (MachineState.readWord memory 252) = words 13 := hm.scalar 14 (by decide)
  have h1 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left77 memory q).c) := hb
  have h2 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left78 memory (left77 memory q)).c) :=
    StaggerScalarLow54.clean_low54 _
      (StaggerScalarWord.step_b_clean false 4 8 (MachineState.readWord memory 0)
        (UInt256.ofNat 2840853838) q)
  have p0 := StaggerScalarLow54.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 0) (UInt256.ofNat 2840853838) q hc
  have p1 := StaggerScalarLow54.project_step false false 4 5 (by decide) (by decide)
    (MachineState.readWord memory 144) (UInt256.ofNat 2840853838) (left77 memory q) h1
  have p2 := StaggerScalarLow54.project_step false false 4 6 (by decide) (by decide)
    (MachineState.readWord memory 252) (UInt256.ofNat 2840853838)
      (left78 memory (left77 memory q)) h2
  change unpackLeft (StaggerScalarWord.step false false 4 6
    (MachineState.readWord memory 252) (UInt256.ofNat 2840853838)
    (left78 memory (left77 memory q))) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step false false 4 5 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2]
  rfl

theorem low32_pairMask (x : UInt256) :
    low32 (UInt256.land x Paired144WordRound.pairWord) = low32 x := by
  apply UInt32.eq_of_toBitVec_eq
  change (PairedLaneUInt256Bridge.bits (UInt256.land x Paired144WordRound.pairWord)).setWidth 32 =
    (PairedLaneUInt256Bridge.bits x).setWidth 32
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 32≤256),
    BitVec.setWidth_eq_extractLsb' (by decide : 32≤256)]
  rw [PairedLaneUInt256Bridge.bits_land,Paired144WordRound.pairWord,
    PairedLaneUInt256Bridge.bits_word,←Paired144Core.normalize_eq_and]
  exact Paired144Core.low_pack _ _

theorem unpackLeft_dirtyE (l r : CryptoLane) (d : UInt256)
    (he : UInt256.land d Paired144WordRound.pairWord = (packCrypto l r).e) :
    unpackLeft {packCrypto l r with e:=d} = l := by
  have hlow : low32 d = low32 (packCrypto l r).e :=
    (low32_pairMask d).symm.trans (congrArg low32 he)
  have h : unpackLeft {packCrypto l r with e:=d} = unpackLeft (packCrypto l r) := by
    exact congrArg (fun e : UInt32 =>
      (⟨low32 (packCrypto l r).a,low32 (packCrypto l r).b,low32 (packCrypto l r).c,
        low32 (packCrypto l r).d,e⟩ : CryptoLane)) hlow
  exact h.trans (unpackLeft_packCrypto l r)

theorem epilogue_crypto (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory (packCrypto l r)) = leftFinish words l := by
  have hp:=StaggerScalarLow54.packCrypto_low54 l r
  rw [epilogue_project memory words (packCrypto l r) hm hp.2.1 hp.2.2.1,
    unpackLeft_packCrypto]

theorem epilogue_dirtyE (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) (d : UInt256)
    (he : UInt256.land d Paired144WordRound.pairWord = (packCrypto l r).e) :
    unpackLeft (epilogue memory {packCrypto l r with e:=d}) = leftFinish words l := by
  have hp:=StaggerScalarLow54.packCrypto_low54 l r
  rw [epilogue_project memory words {packCrypto l r with e:=d} hm hp.2.1 hp.2.2.1,
    unpackLeft_dirtyE l r d he]

#print axioms prologue_crypto
#print axioms paired_crypto
#print axioms epilogue_crypto
#print axioms epilogue_dirtyE
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
