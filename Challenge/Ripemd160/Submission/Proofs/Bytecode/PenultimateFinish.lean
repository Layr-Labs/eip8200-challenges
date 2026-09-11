import Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateRound

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000
set_option maxRecDepth 50000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateFinish
open EvmSemantics
open PairedHelperBooleanTrace (Frame CoreFrame inlineSum inline4Boolean scaledRotation scaledT
  inline4Boolean_eq scaledT_of_boolean_high rawC10 rawC10_eq)
open PenultimateRound

private abbrev pair := _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord
private abbrev lower := _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.lowerWord

theorem modifiedT_maskBD (memory : ByteArray) (q : Frame)
    (hp : q.pair = pair) (hl : q.lower = lower)
    (ha : Normal q.a) (hm : Normal (PairedAllInlineCoreTrace.inline79Frame memory q).message0)
    (hk : Normal q.k) (hb : (PairedLaneUInt256Bridge.bits q.b).getLsbD 64 = false)
    (hc : (PairedLaneUInt256Bridge.bits q.c).getLsbD 64 = false)
    (hd : (PairedLaneUInt256Bridge.bits q.d).getLsbD 64 = false) :
    TerminalRound.modifiedT (PairedAllInlineCoreTrace.inline79Frame memory q) (inline4Boolean q) =
      TerminalRound.modifiedT (PairedAllInlineCoreTrace.inline79Frame memory (maskBD q))
        (inline4Boolean (maskBD q)) := by
  have h := inlineSum_maskBD (PairedAllInlineCoreTrace.inline79Frame memory q)
    hp hl ha hm hk hb hc hd
  change inlineSum (PairedAllInlineCoreTrace.inline79Frame memory q) (inline4Boolean q) =
    inlineSum (PairedAllInlineCoreTrace.inline79Frame memory (maskBD q))
      (inline4Boolean (maskBD q)) at h
  unfold TerminalRound.modifiedT scaledRotation
  rw [h]
  rfl

theorem resultMemory_mask_ce (memory : ByteArray) (q : PairedTailTrace.Frame)
    (hlower : q.lower = lower) :
    PairedTailTrace.resultMemory memory
      {q with c := UInt256.land pair q.c, e := UInt256.land pair q.e} =
      PairedTailTrace.resultMemory memory q := by
  simp only [PairedTailTrace.resultMemory, PairedTailTrace.result0, PairedTailTrace.result1,
    PairedTailTrace.result2, PairedTailTrace.result3, PairedTailTrace.result4, hlower,
    PairedTailTrace.tail_combine_normalized, TerminalMask.toUInt32_pair,
    TerminalMask.toUInt32_pair_shr]

theorem resultMemory_modified_maskBD (memory : ByteArray) (q : Frame)
    (hp : q.pair = pair) (hl : q.lower = lower)
    (ha : Normal q.a) (hm : Normal (PairedAllInlineCoreTrace.inline79Frame memory q).message0)
    (hk : Normal q.k) (hb : (PairedLaneUInt256Bridge.bits q.b).getLsbD 64 = false)
    (hc : (PairedLaneUInt256Bridge.bits q.c).getLsbD 64 = false)
    (hd : (PairedLaneUInt256Bridge.bits q.d).getLsbD 64 = false) :
    PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory (maskBD q)) =
      PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory q) := by
  have ht := modifiedT_maskBD memory q hp hl ha hm hk hb hc hd
  have hf : TerminalRound.modifiedFrame memory (maskBD q) =
      {TerminalRound.modifiedFrame memory q with
        c := UInt256.land pair q.b
        e := UInt256.land pair q.d} := by
    unfold TerminalRound.modifiedFrame
    rw [← ht]
    rfl
  rw [hf]
  exact resultMemory_mask_ce memory (TerminalRound.modifiedFrame memory q) hl

def dirty78Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with
    a := q.e
    b := rawT78 memory q
    c := q.b
    d := TerminalRound.modifiedC10 q
    e := q.d}

theorem maskBD_dirty78_eval (memory : ByteArray) (f : CoreFrame) :
    maskBD (dirty78Frame memory f.frame) =
      (PairedAllInlineCoreTrace.inline78Block.eval memory f).frame := by
  have ht : scaledT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 63) (UInt256.ofNat 27) (inline4Boolean f.frame) =
      PairedLaneWordRound.wordT 4 5 11 f.frame.a f.frame.b f.frame.c f.frame.d f.frame.e
        (PairedAllInlineCoreTrace.inline78Frame memory f.frame).message0 f.frame.k :=
    (congrArg (scaledT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 63) (UInt256.ofNat 27)) (inline4Boolean_eq f.frame rfl)).trans
      (scaledT_of_boolean_high (PairedAllInlineCoreTrace.inline78Frame memory f.frame) 4 5 11
        (UInt256.ofNat 63) (UInt256.ofNat 27) (by decide) rfl rfl rfl rfl rfl)
  have hb : UInt256.land pair (rawT78 memory f.frame) =
      PairedLaneWordRound.wordT 4 5 11 f.frame.a f.frame.b f.frame.c f.frame.d f.frame.e
        (PairedAllInlineCoreTrace.inline78Frame memory f.frame).message0 f.frame.k := ht
  have hd : UInt256.land pair (TerminalRound.modifiedC10 f.frame) =
      UInt256.land (PairedLaneWordRotate.wordShift f.frame.c 22) pair :=
    rawC10_eq f.frame rfl rfl
  simp only [maskBD, dirty78Frame]
  change {f.frame with
    a := f.frame.e
    b := UInt256.land pair (rawT78 memory f.frame)
    c := f.frame.b
    d := UInt256.land pair (TerminalRound.modifiedC10 f.frame)
    e := f.frame.d} = _
  rw [hb, hd]
  rfl

#print axioms modifiedT_maskBD
#print axioms resultMemory_mask_ce
#print axioms resultMemory_modified_maskBD
#print axioms maskBD_dirty78_eval

theorem packed_normals (l r : PairedLaneCryptoBridge.CryptoLane) :
    Normal (PairedLaneWordRound.packCrypto l r).b ∧
    Normal (PairedLaneWordRound.packCrypto l r).c ∧
    Normal (PairedLaneWordRound.packCrypto l r).e := by
  exact ⟨PairedLaneCore.normalize_pack _ _, PairedLaneCore.normalize_pack _ _,
    PairedLaneCore.normalize_pack _ _⟩

theorem message79_normal (memory : ByteArray) (q : Frame) (words : Nat → UInt32)
    (hready : PairedHelperBooleanTrace.NormalizedScheduleReady memory words) :
    Normal (PairedAllInlineCoreTrace.inline79Frame memory q).message0 := by
  change Normal (PairedHelperBooleanTrace.algorithmMessage memory 79)
  rw [PairedHelperBooleanTrace.algorithmMessage_of_normalized memory words hready 79 (by decide)]
  exact PairedLaneCore.normalize_pack _ _

theorem resultMemory_dirty78 (memory : ByteArray) (l r : PairedLaneCryptoBridge.CryptoLane)
    (words : Nat → UInt32) (k : UInt256) (hk : Normal k)
    (hready : PairedHelperBooleanTrace.NormalizedScheduleReady memory words) :
    let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto l r, k⟩
    PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory (dirty78Frame memory f.frame)) =
      PairedTailTrace.resultMemory memory
        (TerminalRound.canonicalFrame memory (PairedAllInlineCoreTrace.inline78Block.eval memory f).frame) := by
  dsimp only
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto l r, k⟩
  have hn := packed_normals l r
  have hb := rawT78_gap memory f.frame rfl rfl rfl hn.2.2
  have hc := normal_gap (PairedLaneWordRound.packCrypto l r).b hn.1
  have hd := rawC10_gap f.frame rfl hn.2.1
  have h := resultMemory_modified_maskBD memory (dirty78Frame memory f.frame)
    rfl rfl hn.2.2 (message79_normal memory _ words hready) hk hb hc hd
  rw [maskBD_dirty78_eval] at h
  exact h.symm.trans (TerminalRound.resultMemory_modified_eq_canonical memory _ rfl rfl)

#print axioms packed_normals
#print axioms message79_normal
#print axioms resultMemory_dirty78
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateFinish

