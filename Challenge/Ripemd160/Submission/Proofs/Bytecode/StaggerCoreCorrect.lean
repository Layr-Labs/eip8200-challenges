import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarLow54
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrologueNear
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

open PairedLaneUInt256Bridge (bits word bits_injective)
open StaggerPrologueNear (Near LaneNear)

theorem prologue_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (prologue memory (embed q)) = rightFold words 3 q := by
  have hm0 : low32 (MachineState.readWord memory 90) = words 5 := hm.scalar 5 (by decide)
  have hm1 : low32 (MachineState.readWord memory 558) = words 14 := hm.scalar 31 (by decide)
  have hm2 : low32 (MachineState.readWord memory 630) = words 7 := hm.scalar 35 (by decide)
  have hi := StaggerScalarLow54.packCrypto_low54 q ⟨0,0,0,0,0⟩
  have h1 : StaggerScalarLow54.Low54 (bits (right0 memory (embed q)).c) := hi.2.1
  have h2 : StaggerScalarLow54.Low54 (bits (right1 memory (right0 memory (embed q))).c) :=
    StaggerScalarLow54.clean_low54 _
      (StaggerScalarWord.step_b_clean false 4 8 _ _ (embed q))
  have p0 := StaggerScalarLow54.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 90) (UInt256.ofNat 1352829926) (embed q) hi.2.2.1
  have p1 := StaggerScalarLow54.project_step true false 4 9 (by decide) (by decide)
    (MachineState.readWord memory 558) (UInt256.ofNat 1352829926) (right0 memory (embed q)) h1
  have p2 := StaggerScalarLow54.project_step true false 4 9 (by decide) (by decide)
    (MachineState.readWord memory 630) (UInt256.ofNat 1352829926)
      (right1 memory (right0 memory (embed q))) h2
  change unpackLeft (StaggerScalarWord.step true false 4 9 _ _ _) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 9 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2, show unpackLeft (embed q) = q from unpackLeft_packCrypto _ _]
  rfl

theorem clean_word_eq (x : UInt256) (hx : StaggerScalarWord.mask x=x) :
    x = word (Paired144Core.pack (low32 x).toBitVec 0#32) := by
  exact hx.symm.trans (StaggerScalarWord.mask_eq x)

theorem prologue_bc (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    (prologue memory (embed q)).b = (embed (rightFold words 3 q)).b ∧
    (prologue memory (embed q)).c = (embed (rightFold words 3 q)).c := by
  have hp := prologue_crypto memory words q hm
  have hb := congrArg (fun z : CryptoLane => z.b) hp
  have hc := congrArg (fun z : CryptoLane => z.c) hp
  have hcb : StaggerScalarWord.mask (prologue memory (embed q)).b = (prologue memory (embed q)).b :=
    StaggerScalarWord.step_b_clean false 4 9 _ _ _
  have hcc : StaggerScalarWord.mask (prologue memory (embed q)).c = (prologue memory (embed q)).c :=
    StaggerScalarWord.step_b_clean false 4 9 _ _ _
  constructor
  · rw [clean_word_eq _ hcb]
    exact congrArg (fun x : UInt32 => word (Paired144Core.pack x.toBitVec 0#32)) hb
  · rw [clean_word_eq _ hcc]
    exact congrArg (fun x : UInt32 => word (Paired144Core.pack x.toBitVec 0#32)) hc

theorem pairWord_near (l r r' : UInt256) (h : low32 r=low32 r') :
    Near (StaggerCoreModel.pairWord l r) (StaggerCoreModel.pairWord l r') := by
  have hh := congrArg UInt32.toBitVec h
  change (bits r).setWidth 32 = (bits r').setWidth 32 at hh
  unfold Near StaggerCoreModel.pairWord
  rw [PairedLaneUInt256Bridge.bits_lor,PairedLaneUInt256Bridge.bits_lor,
    PairedLaneUInt256Bridge.bits_shl _ 144 (by decide),
    PairedLaneUInt256Bridge.bits_shl _ 144 (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := congrArg (fun z : BitVec 32 => z.getLsbD (i-144)) hh
  have hi256 : i<256 := by omega
  by_cases h144 : i<144
  · simp only [BitVec.getLsbD_setWidth,hi,hi256,decide_true,Bool.true_and,
      BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,h144,Bool.not_true,Bool.false_and]
  · have hsmall : i-144<32 := by omega
    simp only [BitVec.getLsbD_setWidth,hsmall,decide_true,Bool.true_and] at hbit
    simp only [BitVec.getLsbD_setWidth,hi,hi256,decide_true,Bool.true_and,
      BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,h144,decide_false,Bool.not_false,hbit]

theorem pair_near (l r r' : Paired144WordRound.WordLane) (h : unpackLeft r=unpackLeft r') :
    LaneNear (pair l r) (pair l r') := by
  exact ⟨pairWord_near _ _ _ (congrArg (fun z : CryptoLane => z.a) h),
    pairWord_near _ _ _ (congrArg (fun z : CryptoLane => z.b) h),
    pairWord_near _ _ _ (congrArg (fun z : CryptoLane => z.c) h),
    pairWord_near _ _ _ (congrArg (fun z : CryptoLane => z.d) h),
    pairWord_near _ _ _ (congrArg (fun z : CryptoLane => z.e) h)⟩

theorem paired_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    ∃ dd de : UInt256,
      paired memory (embed q) =
        {packCrypto (leftFold words 77 q) (rightFold words 80 q) with d:=dd, e:=de} ∧
      UInt256.land dd Paired144WordRound.pairWord =
        (packCrypto (leftFold words 77 q) (rightFold words 80 q)).d ∧
      UInt256.land de Paired144WordRound.pairWord =
        (packCrypto (leftFold words 77 q) (rightFold words 80 q)).e := by
  have hp : unpackLeft (prologue memory (embed q)) = unpackLeft (embed (rightFold words 3 q)) :=
    (prologue_crypto memory words q hm).trans (unpackLeft_packCrypto _ _).symm
  have hbc := prologue_bc memory words q hm
  have hb : (pair (embed q) (prologue memory (embed q))).b =
      (pair (embed q) (embed (rightFold words 3 q))).b :=
    congrArg (StaggerCoreModel.pairWord (embed q).b) hbc.1
  have hc : (pair (embed q) (prologue memory (embed q))).c =
      (pair (embed q) (embed (rightFold words 3 q))).c :=
    congrArg (StaggerCoreModel.pairWord (embed q).c) hbc.2
  rw [paired, StaggerPrologueNear.fold_eq (message memory) 77 (by decide)
    _ _ (pair_near _ _ _ hp) hb hc, pair_embed]
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

theorem unpackLeft_dirtyDE (l r : CryptoLane) (dd de : UInt256)
    (hd : UInt256.land dd Paired144WordRound.pairWord = (packCrypto l r).d)
    (he : UInt256.land de Paired144WordRound.pairWord = (packCrypto l r).e) :
    unpackLeft {packCrypto l r with d:=dd, e:=de} = l := by
  have hlowd : low32 dd = low32 (packCrypto l r).d :=
    (low32_pairMask dd).symm.trans (congrArg low32 hd)
  have hlowe : low32 de = low32 (packCrypto l r).e :=
    (low32_pairMask de).symm.trans (congrArg low32 he)
  change (⟨low32 (packCrypto l r).a, low32 (packCrypto l r).b, low32 (packCrypto l r).c,
    low32 dd, low32 de⟩ : CryptoLane) = l
  rw [hlowd, hlowe]
  exact unpackLeft_packCrypto l r

theorem epilogue_crypto (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory (packCrypto l r)) = leftFinish words l := by
  have hp:=StaggerScalarLow54.packCrypto_low54 l r
  rw [epilogue_project memory words (packCrypto l r) hm hp.2.1 hp.2.2.1,
    unpackLeft_packCrypto]

theorem epilogue_dirtyDE (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) (dd de : UInt256)
    (hd : UInt256.land dd Paired144WordRound.pairWord = (packCrypto l r).d)
    (he : UInt256.land de Paired144WordRound.pairWord = (packCrypto l r).e) :
    unpackLeft (epilogue memory {packCrypto l r with d:=dd, e:=de}) = leftFinish words l := by
  have hp:=StaggerScalarLow54.packCrypto_low54 l r
  rw [epilogue_project memory words {packCrypto l r with d:=dd, e:=de} hm hp.2.1 hp.2.2.1,
    unpackLeft_dirtyDE l r dd de hd he]

#print axioms prologue_crypto
#print axioms paired_crypto
#print axioms epilogue_crypto
#print axioms epilogue_dirtyDE
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
