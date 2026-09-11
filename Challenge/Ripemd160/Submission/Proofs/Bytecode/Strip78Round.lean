import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Algebra

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedHelperBooleanTrace PairedAllInlineCoreTrace
open PairedLaneUInt256Bridge PairedLaneCore PairedLaneScaledRotate Strip78Algebra
open PairedStartupTrace (pairWord lowerWord upperWord)

def stripTemplate : List Instr := PairedAllInlineCoreTrace.inline78Template.take 35 ++ (PairedAllInlineCoreTrace.inline78Template.drop 37).take 5

def stripT (q : PairedHelperBooleanTrace.Frame) (value : UInt256) : UInt256 :=
  UInt256.add q.e (scaledRotation q q.upper (UInt256.ofNat 63) (UInt256.ofNat 27) value)

def stripOutput (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [TerminalRound.modifiedC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_stripTemplate (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq stripTemplate {s with pc := pc, stack := PairedAllInlineCoreTrace.inline78Entry q rho} =
      some {s with pc := pcAfter pc stripTemplate, stack := stripOutput q (stripT (PairedAllInlineCoreTrace.inline78Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [stripTemplate, PairedAllInlineCoreTrace.inline78Template, PairedAllInlineCoreTrace.inline78Entry, stripOutput,
    stripT, scaledRotation, inlineSum, PairedAllInlineCoreTrace.inline78Frame, TerminalRound.modifiedC10,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat]
  constructor
  · rfl
  constructor
  · rfl
  · change stripT (PairedAllInlineCoreTrace.inline78Frame s.memory q) (PairedSynthCoreTrace.fourRaw q) =
      stripT (PairedAllInlineCoreTrace.inline78Frame s.memory q) (inline4Boolean q)
    rw [PairedSynthCoreTrace.fourRaw_eq_inline4Boolean]

def dirtyFrame (memory : ByteArray) (f : CoreFrame) : PairedHelperBooleanTrace.Frame :=
  { (inline78Block.eval memory f).frame with
    b := stripT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) (inline4Boolean f.frame)
    d := TerminalRound.modifiedC10 f.frame }

theorem masked_dirtyFrame (memory : ByteArray) (f : CoreFrame) :
    maskedBD (dirtyFrame memory f) = (inline78Block.eval memory f).frame := by
  have ht : scaledT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 63) (UInt256.ofNat 27) (inline4Boolean f.frame) =
      PairedLaneWordRound.wordT 4 5 11 f.frame.a f.frame.b f.frame.c f.frame.d f.frame.e
        (PairedAllInlineCoreTrace.inline78Frame memory f.frame).message0 f.k :=
    (congrArg (scaledT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 63) (UInt256.ofNat 27)) (inline4Boolean_eq f.frame rfl)).trans
      (scaledT_of_boolean_high (PairedAllInlineCoreTrace.inline78Frame memory f.frame) 4 5 11
        (UInt256.ofNat 63) (UInt256.ofNat 27) (by decide) rfl rfl rfl rfl rfl)
  have hd : UInt256.land pairWord (TerminalRound.modifiedC10 f.frame) =
      UInt256.land (PairedLaneWordRotate.wordShift f.frame.c 22) pairWord := by
    apply bits_injective
    simp only [TerminalRound.modifiedC10, PairedLaneWordRotate.wordShift, bits_land,
      bits_shr _ 22 (by decide), bits_mul]
    change bits pairWord &&& ((bits PairedLaneWordRotate.factorWord * bits f.frame.c) >>> 22) =
      ((bits f.frame.c * bits PairedLaneWordRotate.factorWord) >>> 22) &&& bits pairWord
    rw [BitVec.mul_comm, BitVec.and_comm]
  change { (inline78Block.eval memory f).frame with
      b := UInt256.land pairWord (stripT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) (inline4Boolean f.frame)),
      d := UInt256.land pairWord (TerminalRound.modifiedC10 f.frame) } = _
  have hb : UInt256.land pairWord (stripT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) (inline4Boolean f.frame)) =
      (inline78Block.eval memory f).frame.b := ht
  rw [hb]
  change { (inline78Block.eval memory f).frame with
      b := (inline78Block.eval memory f).frame.b,
      d := UInt256.land pairWord (TerminalRound.modifiedC10 f.frame) } = _
  rw [hd]
  rfl

theorem output_dirtyFrame (memory : ByteArray) (f : CoreFrame) (rho : List UInt256) :
    stripOutput f.frame (stripT (PairedAllInlineCoreTrace.inline78Frame memory f.frame) (inline4Boolean f.frame)) rho =
      PairedAllInlineCoreTrace.inline79Entry (dirtyFrame memory f) rho := by
  rfl

theorem stripT_gap (q : PairedHelperBooleanTrace.Frame) (v : UInt256)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (he : normalize (bits q.e) = bits q.e) :
    (bits (stripT q v)).getLsbD 64 = false := by
  let sum := bits (inlineSum q v)
  have hsum : normalize sum = sum := by
    unfold sum inlineSum
    rw [hpair, bits_mask, normalize_idem]
  have hrot : bits (scaledRotation q q.upper (UInt256.ofNat 63) (UInt256.ofNat 27) v) =
      (scaleHigh sum 6 * PairedLaneProduct.factor) >>> 27 := by
    simp only [scaledRotation, hfactor, hupper, bits_shr _ 27 (by decide), bits_mul,
      bits_add, bits_land, bits_ofNat]
    change (PairedLaneProduct.factor * ((BitVec.ofNat 256 63 *
        (PairedLaneBoolean.upperMask &&& sum)) + sum)) >>> 27 = _
    rw [BitVec.mul_comm]
    rfl
  rw [stripT, bits_add, hrot, ← he, ← hsum]
  exact scaled78_add_gap _ _ _ _

theorem c10_gap (q : PairedHelperBooleanTrace.Frame)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hc : normalize (bits q.c) = bits q.c) :
    (bits (TerminalRound.modifiedC10 q)).getLsbD 64 = false := by
  simp only [TerminalRound.modifiedC10, hfactor, bits_shr _ 22 (by decide), bits_mul]
  change ((PairedLaneProduct.factor * bits q.c) >>> 22).getLsbD 64 = false
  rw [BitVec.mul_comm, ← hc]
  exact PairedLaneCarry.shifted_product_gap _ _ 10 (by decide) (by decide)

theorem clean_low (x : BitVec 256) (hx : normalize x = x) : x.toNat % 2 ^ 128 < 2 ^ 32 := by
  rw [← hx, normalize, pack_toNat]
  have h := (low x).isLt
  simp only [Nat.reducePow] at *
  omega

theorem clean_three_small (x y z : UInt256)
    (hx : normalize (bits x) = bits x) (hy : normalize (bits y) = bits y)
    (hz : normalize (bits z) = bits z) :
    (UInt256.add x (UInt256.add y z)).toNat % 2 ^ 128 < 2 ^ 63 := by
  have hx' := clean_low (bits x) hx
  have hy' := clean_low (bits y) hy
  have hz' := clean_low (bits z) hz
  change (bits (UInt256.add x (UInt256.add y z))).toNat % 2 ^ 128 < 2 ^ 63
  simp only [bits_add, BitVec.toNat_add, Nat.reducePow] at *
  omega

theorem resultMemory_strip_eq (memory : ByteArray) (f : CoreFrame)
    (hb : normalize (bits f.frame.b) = bits f.frame.b)
    (hc : normalize (bits f.frame.c) = bits f.frame.c)
    (he : normalize (bits f.frame.e) = bits f.frame.e)
    (hk : normalize (bits f.k) = bits f.k)
    (hm : normalize (bits (PairedAllInlineCoreTrace.inline79Frame memory f.frame).message0) =
      bits (PairedAllInlineCoreTrace.inline79Frame memory f.frame).message0) :
    PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory (dirtyFrame memory f)) =
      PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory (inline78Block.eval memory f).frame) := by
  have hbc : UInt256.land pairWord (dirtyFrame memory f).c = (dirtyFrame memory f).c := by
    apply bits_injective
    rw [bits_mask]
    exact hb
  have hbGap : (bits (dirtyFrame memory f).b).getLsbD 64 = false :=
    stripT_gap (PairedAllInlineCoreTrace.inline78Frame memory f.frame) _ rfl rfl rfl he
  have hdGap : (bits (dirtyFrame memory f).d).getLsbD 64 = false := c10_gap f.frame rfl hc
  have hsmall : (UInt256.add (dirtyFrame memory f).k
      (UInt256.add (PairedAllInlineCoreTrace.inline79Frame memory (dirtyFrame memory f)).message0
        (dirtyFrame memory f).a)).toNat % 2 ^ 128 < 2 ^ 63 :=
    clean_three_small f.k (PairedAllInlineCoreTrace.inline79Frame memory f.frame).message0 f.frame.e hk hm he
  have h := resultMemory_masked memory (dirtyFrame memory f) rfl rfl hbc hbGap hdGap hsmall
  rw [masked_dirtyFrame] at h
  exact h

#print axioms resultMemory_strip_eq
#print axioms stripT_gap
#print axioms c10_gap
#print axioms clean_three_small
#print axioms run_stripTemplate
#print axioms masked_dirtyFrame
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round
