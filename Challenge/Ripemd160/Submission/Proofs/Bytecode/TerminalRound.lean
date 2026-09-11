import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalMask

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRound
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open StackRoundTrace
open PairedAllInlineCoreTrace
open PairedHelperBooleanTrace (CoreFrame scaledT scaledRotation inlineSum inlineProduct
  rawC10 inline4Boolean inline4Boolean_eq scaledT_of_boolean_high rawC10_eq)
open PairedStartupTrace (pairWord upperWord lowerWord)

def modifiedTemplate : List Instr :=
  inline79Template.take 35 ++ (inline79Template.drop 37).take 5

theorem modifiedTemplate_length : modifiedTemplate.length = 40 := by
  decide

theorem modifiedTemplate_bytes : (modifiedTemplate.map Instr.size).sum = 47 := by
  decide

theorem modifiedTemplate_pc :
    pcAfter (UInt256.ofNat 4804) modifiedTemplate = UInt256.ofNat 4851 := by
  decide

def modifiedC10 (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  UInt256.shiftRight (UInt256.mul q.factor q.c) (UInt256.ofNat 22)

def modifiedT (q : PairedHelperBooleanTrace.Frame) (value : UInt256) : UInt256 :=
  UInt256.add q.e (scaledRotation q q.upper (UInt256.ofNat 31)
    (UInt256.ofNat 26) value)

def modifiedOutput (q : PairedHelperBooleanTrace.Frame) (value : UInt256)
    (rho : List UInt256) : List UInt256 :=
  [modifiedC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_modifiedTemplate_raw (s : State) (pc : UInt256)
    (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq modifiedTemplate {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc modifiedTemplate, stack := modifiedOutput q (modifiedT (inline79Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedHelperBooleanTrace.active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [modifiedTemplate, inline79Template, inline79Entry,
    modifiedOutput, modifiedC10, modifiedT, inline79Frame, scaledRotation,
    inlineSum, inlineProduct, rawC10, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt]
  constructor
  · rfl
  constructor
  · rfl
  · change modifiedT (inline79Frame s.memory q) (PairedSynthCoreTrace.fourRaw q) =
      modifiedT (inline79Frame s.memory q) (inline4Boolean q)
    rw [PairedSynthCoreTrace.fourRaw_eq_inline4Boolean]

def modifiedFrame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) :
    PairedTailTrace.Frame where
  a := q.e
  b := modifiedT (inline79Frame memory q) (inline4Boolean q)
  c := q.b
  d := modifiedC10 q
  e := q.d
  unused5 := q.factor
  unused6 := q.pair
  unused3 := q.upper
  lower := q.lower

def canonicalFrame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) :
    PairedTailTrace.Frame where
  a := q.e
  b := scaledT (inline79Frame memory q) q.upper (UInt256.ofNat 31)
    (UInt256.ofNat 26) (inline4Boolean q)
  c := q.b
  d := rawC10 q
  e := q.d
  unused5 := q.factor
  unused6 := q.pair
  unused3 := q.upper
  lower := q.lower

theorem resultMemory_modified_eq_canonical (memory : ByteArray)
    (q : PairedHelperBooleanTrace.Frame) (hpair : q.pair = pairWord)
    (hlower : q.lower = lowerWord) :
    PairedTailTrace.resultMemory memory (modifiedFrame memory q) =
      PairedTailTrace.resultMemory memory (canonicalFrame memory q) := by
  have h := TerminalMask.resultMemory_mask_bd memory (modifiedFrame memory q) hlower
  rw [← h]
  simp [modifiedFrame, canonicalFrame, modifiedC10, modifiedT, scaledT, rawC10, inline79Frame,
    hpair]

def evaluatedTailFrame (memory : ByteArray) (f : CoreFrame) : PairedTailTrace.Frame :=
  let w := (inline79Block.eval memory f).lane
  { a := w.a, b := w.b, c := w.c, d := w.d, e := w.e,
    unused5 := PairedLaneWordRotate.factorWord, unused6 := pairWord,
    unused3 := upperWord, lower := lowerWord }

theorem canonicalFrame_eval (memory : ByteArray) (f : CoreFrame) :
    canonicalFrame memory f.frame = evaluatedTailFrame memory f := by
  have ht : scaledT (inline79Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 31) (UInt256.ofNat 26) (inline4Boolean f.frame) =
      PairedLaneWordRound.wordT 4 6 11 f.frame.a f.frame.b f.frame.c f.frame.d f.frame.e
        (inline79Frame memory f.frame).message0 f.frame.k :=
    (congrArg (scaledT (inline79Frame memory f.frame) f.frame.upper
      (UInt256.ofNat 31) (UInt256.ofNat 26)) (inline4Boolean_eq f.frame rfl)).trans
      (scaledT_of_boolean_high (inline79Frame memory f.frame) 4 6 11
        (UInt256.ofNat 31) (UInt256.ofNat 26) (by decide) rfl rfl rfl rfl rfl)
  simp only [canonicalFrame, evaluatedTailFrame, inline79Block,
    PairedLaneWordRound.wordStep, ht, rawC10_eq f.frame rfl rfl]
  rfl

#print axioms run_modifiedTemplate_raw
#print axioms resultMemory_modified_eq_canonical
#print axioms canonicalFrame_eval
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRound
