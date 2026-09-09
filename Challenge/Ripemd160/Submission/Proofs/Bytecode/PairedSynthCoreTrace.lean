import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordGroupTwoHoist
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanSynthesis

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanFactoring

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSequentialShift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall26Inline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall20Inline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall22Inline

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist


def zeroRaw (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  PairedLaneBooleanFactoring.factoredWord q.b q.c q.d q.upper

def fourRaw (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  PairedLaneBooleanFactoring.factoredWord q.b q.c q.d q.lower

theorem zeroRaw_eq_inline0Boolean (q : PairedHelperBooleanTrace.Frame) :
    zeroRaw q = inline0Boolean q := by
  change PairedLaneBooleanFactoring.factoredWord q.b q.c q.d q.upper = _
  apply Eq.trans (PairedLaneBooleanFactoring.factored_word q.b q.c q.d q.upper).symm
  apply bits_injective
  simp only [inline0Boolean, bits_xor, bits_land, bits_lor, bits_lnot]
  ac_rfl

#print axioms zeroRaw_eq_inline0Boolean

theorem fourRaw_eq_inline4Boolean (q : PairedHelperBooleanTrace.Frame) :
    fourRaw q = inline4Boolean q := by
  change PairedLaneBooleanFactoring.factoredWord q.b q.c q.d q.lower = _
  apply Eq.trans (PairedLaneBooleanFactoring.factored_word q.b q.c q.d q.lower).symm
  apply bits_injective
  simp only [inline4Boolean, bits_xor, bits_land, bits_lor, bits_lnot]
  ac_rfl

#print axioms fourRaw_eq_inline4Boolean

def inline0Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 7),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline0Template_length : inline0Template.length = 44 := rfl

theorem run_inline0Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline0Template {s with pc := pc, stack := inline0Entry q rho} =
      some {s with pc := pcAfter pc inline0Template, stack := inline0Output q (scaledT (inline0Frame s.memory q) q.lower (UInt256.ofNat 7) (UInt256.ofNat 24) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline0Template, inline0Entry, inline0Output,
    scaledT, scaledRotation, inlineSum, inline0Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline0Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline0Template {s with pc := pc, stack := inline0Entry q rho} =
      some {s with pc := pcAfter pc inline0Template, stack := inline0Output q (scaledT (inline0Frame s.memory q) q.lower (UInt256.ofNat 7) (UInt256.ofNat 24) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline0Template_raw s pc q rho hstack hrun hactive

theorem run_inline0Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline0Template {s with pc := pc, stack := inline0Entry q rho} =
      some {s with pc := pcAfter pc inline0Template, stack := inline0WordStack q (PairedLaneWordRound.wordStep 0 11 8 (inline0Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline0Frame s.memory q) q.lower (UInt256.ofNat 7) (UInt256.ofNat 24) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 11 8 q.a q.b q.c q.d q.e
        (inline0Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline0Frame s.memory q) q.lower (UInt256.ofNat 7) (UInt256.ofNat 24)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline0Frame s.memory q) 0 11 8 (UInt256.ofNat 7) (UInt256.ofNat 24) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline0Output q (scaledT (inline0Frame s.memory q) q.lower (UInt256.ofNat 7) (UInt256.ofNat 24) (inline0Boolean q)) rho =
      inline0WordStack q
        (PairedLaneWordRound.wordStep 0 11 8 (inline0Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline0Output, inline0WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline0Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline0Template, stack := vs}) hout)

#print axioms inline0Template_length
#print axioms run_inline0Template_raw
#print axioms run_inline0Template
#print axioms run_inline0Template_word

def inline1Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 31),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline1Template_length : inline1Template.length = 44 := rfl

theorem run_inline1Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline1Template {s with pc := pc, stack := inline1Entry q rho} =
      some {s with pc := pcAfter pc inline1Template, stack := inline1Output q (scaledT (inline1Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 23) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline1Template, inline1Entry, inline1Output,
    scaledT, scaledRotation, inlineSum, inline1Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline1Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline1Template {s with pc := pc, stack := inline1Entry q rho} =
      some {s with pc := pcAfter pc inline1Template, stack := inline1Output q (scaledT (inline1Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 23) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline1Template_raw s pc q rho hstack hrun hactive

theorem run_inline1Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline1Template {s with pc := pc, stack := inline1Entry q rho} =
      some {s with pc := pcAfter pc inline1Template, stack := inline1WordStack q (PairedLaneWordRound.wordStep 0 14 9 (inline1Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline1Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 23) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 14 9 q.a q.b q.c q.d q.e
        (inline1Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline1Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 23)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline1Frame s.memory q) 0 14 9 (UInt256.ofNat 31) (UInt256.ofNat 23) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline1Output q (scaledT (inline1Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 23) (inline0Boolean q)) rho =
      inline1WordStack q
        (PairedLaneWordRound.wordStep 0 14 9 (inline1Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline1Output, inline1WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline1Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline1Template, stack := vs}) hout)

#print axioms inline1Template_length
#print axioms run_inline1Template_raw
#print axioms run_inline1Template
#print axioms run_inline1Template_word

def inline2Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 63),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline2Template_length : inline2Template.length = 44 := rfl

theorem run_inline2Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline2Template {s with pc := pc, stack := inline2Entry q rho} =
      some {s with pc := pcAfter pc inline2Template, stack := inline2Output q (scaledT (inline2Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 23) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline2Template, inline2Entry, inline2Output,
    scaledT, scaledRotation, inlineSum, inline2Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline2Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline2Template {s with pc := pc, stack := inline2Entry q rho} =
      some {s with pc := pcAfter pc inline2Template, stack := inline2Output q (scaledT (inline2Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 23) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline2Template_raw s pc q rho hstack hrun hactive

theorem run_inline2Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline2Template {s with pc := pc, stack := inline2Entry q rho} =
      some {s with pc := pcAfter pc inline2Template, stack := inline2WordStack q (PairedLaneWordRound.wordStep 0 15 9 (inline2Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline2Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 23) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 15 9 q.a q.b q.c q.d q.e
        (inline2Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline2Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 23)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline2Frame s.memory q) 0 15 9 (UInt256.ofNat 63) (UInt256.ofNat 23) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline2Output q (scaledT (inline2Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 23) (inline0Boolean q)) rho =
      inline2WordStack q
        (PairedLaneWordRound.wordStep 0 15 9 (inline2Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline2Output, inline2WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline2Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline2Template, stack := vs}) hout)

#print axioms inline2Template_length
#print axioms run_inline2Template_raw
#print axioms run_inline2Template
#print axioms run_inline2Template_word

def inline3Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline3Template_length : inline3Template.length = 42 := rfl

theorem run_inline3Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline3Template {s with pc := pc, stack := inline3Entry q rho} =
      some {s with pc := pcAfter pc inline3Template, stack := inline3Output q (scaledOneT (inline3Frame s.memory q) q.lower (UInt256.ofNat 21) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline3Template, inline3Entry, inline3Output,
    scaledOneT, scaledOneRotation, inlineSum, inline3Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline3Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline3Template {s with pc := pc, stack := inline3Entry q rho} =
      some {s with pc := pcAfter pc inline3Template, stack := inline3Output q (scaledOneT (inline3Frame s.memory q) q.lower (UInt256.ofNat 21) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline3Template_raw s pc q rho hstack hrun hactive

theorem run_inline3Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline3Template {s with pc := pc, stack := inline3Entry q rho} =
      some {s with pc := pcAfter pc inline3Template, stack := inline3WordStack q (PairedLaneWordRound.wordStep 0 12 11 (inline3Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledOneT (inline3Frame s.memory q) q.lower (UInt256.ofNat 21) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 12 11 q.a q.b q.c q.d q.e
        (inline3Frame s.memory q).message0 q.k :=
    (congrArg (scaledOneT (inline3Frame s.memory q) q.lower (UInt256.ofNat 21)) (inline0Boolean_eq q hupper)).trans
      (scaledOneT_of_boolean_low (inline3Frame s.memory q) 0 12 11 (UInt256.ofNat 21) (by decide) rfl hfactor hpair hlower rfl)
  have hout : inline3Output q (scaledOneT (inline3Frame s.memory q) q.lower (UInt256.ofNat 21) (inline0Boolean q)) rho =
      inline3WordStack q
        (PairedLaneWordRound.wordStep 0 12 11 (inline3Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline3Output, inline3WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline3Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline3Template, stack := vs}) hout)

#print axioms inline3Template_length
#print axioms run_inline3Template_raw
#print axioms run_inline3Template
#print axioms run_inline3Template_word

def inline4Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 496),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline4Template_length : inline4Template.length = 44 := rfl

theorem run_inline4Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline4Template {s with pc := pc, stack := inline4Entry q rho} =
      some {s with pc := pcAfter pc inline4Template, stack := inline4Output q (scaledT (inline4Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 27) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline4Template, inline4Entry, inline4Output,
    scaledT, scaledRotation, inlineSum, inline4Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline4Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline4Template {s with pc := pc, stack := inline4Entry q rho} =
      some {s with pc := pcAfter pc inline4Template, stack := inline4Output q (scaledT (inline4Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 27) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline4Template_raw s pc q rho hstack hrun hactive

theorem run_inline4Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline4Template {s with pc := pc, stack := inline4Entry q rho} =
      some {s with pc := pcAfter pc inline4Template, stack := inline4WordStack q (PairedLaneWordRound.wordStep 0 5 13 (inline4Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline4Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 27) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 5 13 q.a q.b q.c q.d q.e
        (inline4Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline4Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 27)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline4Frame s.memory q) 0 5 13 (UInt256.ofNat 255) (UInt256.ofNat 27) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline4Output q (scaledT (inline4Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 27) (inline0Boolean q)) rho =
      inline4WordStack q
        (PairedLaneWordRound.wordStep 0 5 13 (inline4Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline4Output, inline4WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline4Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline4Template, stack := vs}) hout)

#print axioms inline4Template_length
#print axioms run_inline4Template_raw
#print axioms run_inline4Template
#print axioms run_inline4Template_word

def inline5Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 127),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline5Template_length : inline5Template.length = 44 := rfl

theorem run_inline5Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline5Template {s with pc := pc, stack := inline5Entry q rho} =
      some {s with pc := pcAfter pc inline5Template, stack := inline5Output q (scaledT (inline5Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 24) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline5Template, inline5Entry, inline5Output,
    scaledT, scaledRotation, inlineSum, inline5Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline5Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline5Template {s with pc := pc, stack := inline5Entry q rho} =
      some {s with pc := pcAfter pc inline5Template, stack := inline5Output q (scaledT (inline5Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 24) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline5Template_raw s pc q rho hstack hrun hactive

theorem run_inline5Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline5Template {s with pc := pc, stack := inline5Entry q rho} =
      some {s with pc := pcAfter pc inline5Template, stack := inline5WordStack q (PairedLaneWordRound.wordStep 0 8 15 (inline5Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline5Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 24) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 8 15 q.a q.b q.c q.d q.e
        (inline5Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline5Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 24)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline5Frame s.memory q) 0 8 15 (UInt256.ofNat 127) (UInt256.ofNat 24) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline5Output q (scaledT (inline5Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 24) (inline0Boolean q)) rho =
      inline5WordStack q
        (PairedLaneWordRound.wordStep 0 8 15 (inline5Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline5Output, inline5WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline5Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline5Template, stack := vs}) hout)

#print axioms inline5Template_length
#print axioms run_inline5Template_raw
#print axioms run_inline5Template
#print axioms run_inline5Template_word

def inline6Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 560),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline6Template_length : inline6Template.length = 44 := rfl

theorem run_inline6Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline6Template {s with pc := pc, stack := inline6Entry q rho} =
      some {s with pc := pcAfter pc inline6Template, stack := inline6Output q (scaledT (inline6Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline6Template, inline6Entry, inline6Output,
    scaledT, scaledRotation, inlineSum, inline6Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline6Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline6Template {s with pc := pc, stack := inline6Entry q rho} =
      some {s with pc := pcAfter pc inline6Template, stack := inline6Output q (scaledT (inline6Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline6Template_raw s pc q rho hstack hrun hactive

theorem run_inline6Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline6Template {s with pc := pc, stack := inline6Entry q rho} =
      some {s with pc := pcAfter pc inline6Template, stack := inline6WordStack q (PairedLaneWordRound.wordStep 0 7 15 (inline6Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline6Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 7 15 q.a q.b q.c q.d q.e
        (inline6Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline6Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline6Frame s.memory q) 0 7 15 (UInt256.ofNat 255) (UInt256.ofNat 25) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline6Output q (scaledT (inline6Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (inline0Boolean q)) rho =
      inline6WordStack q
        (PairedLaneWordRound.wordStep 0 7 15 (inline6Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline6Output, inline6WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline6Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline6Template, stack := vs}) hout)

#print axioms inline6Template_length
#print axioms run_inline6Template_raw
#print axioms run_inline6Template
#print axioms run_inline6Template_word

def inline7Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 336),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 15),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline7Template_length : inline7Template.length = 44 := rfl

theorem run_inline7Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline7Template {s with pc := pc, stack := inline7Entry q rho} =
      some {s with pc := pcAfter pc inline7Template, stack := inline7Output q (scaledT (inline7Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 27) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline7Template, inline7Entry, inline7Output,
    scaledT, scaledRotation, inlineSum, inline7Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline7Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline7Template {s with pc := pc, stack := inline7Entry q rho} =
      some {s with pc := pcAfter pc inline7Template, stack := inline7Output q (scaledT (inline7Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 27) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline7Template_raw s pc q rho hstack hrun hactive

theorem run_inline7Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline7Template {s with pc := pc, stack := inline7Entry q rho} =
      some {s with pc := pcAfter pc inline7Template, stack := inline7WordStack q (PairedLaneWordRound.wordStep 0 9 5 (inline7Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline7Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 27) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 9 5 q.a q.b q.c q.d q.e
        (inline7Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline7Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 27)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline7Frame s.memory q) 0 9 5 (UInt256.ofNat 15) (UInt256.ofNat 27) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline7Output q (scaledT (inline7Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 27) (inline0Boolean q)) rho =
      inline7WordStack q
        (PairedLaneWordRound.wordStep 0 9 5 (inline7Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline7Output, inline7WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline7Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline7Template, stack := vs}) hout)

#print axioms inline7Template_length
#print axioms run_inline7Template_raw
#print axioms run_inline7Template
#print axioms run_inline7Template_word

def inline8Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 15),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline8Template_length : inline8Template.length = 44 := rfl

theorem run_inline8Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline8Template {s with pc := pc, stack := inline8Entry q rho} =
      some {s with pc := pcAfter pc inline8Template, stack := inline8Output q (scaledT (inline8Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 25) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline8Template, inline8Entry, inline8Output,
    scaledT, scaledRotation, inlineSum, inline8Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline8Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline8Template {s with pc := pc, stack := inline8Entry q rho} =
      some {s with pc := pcAfter pc inline8Template, stack := inline8Output q (scaledT (inline8Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 25) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline8Template_raw s pc q rho hstack hrun hactive

theorem run_inline8Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline8Template {s with pc := pc, stack := inline8Entry q rho} =
      some {s with pc := pcAfter pc inline8Template, stack := inline8WordStack q (PairedLaneWordRound.wordStep 0 11 7 (inline8Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline8Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 25) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 11 7 q.a q.b q.c q.d q.e
        (inline8Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline8Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 25)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline8Frame s.memory q) 0 11 7 (UInt256.ofNat 15) (UInt256.ofNat 25) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline8Output q (scaledT (inline8Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 25) (inline0Boolean q)) rho =
      inline8WordStack q
        (PairedLaneWordRound.wordStep 0 11 7 (inline8Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline8Output, inline8WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline8Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline8Template, stack := vs}) hout)

#print axioms inline8Template_length
#print axioms run_inline8Template_raw
#print axioms run_inline8Template
#print axioms run_inline8Template_word

def inline9Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 400),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 63),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline9Template_length : inline9Template.length = 44 := rfl

theorem run_inline9Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline9Template {s with pc := pc, stack := inline9Entry q rho} =
      some {s with pc := pcAfter pc inline9Template, stack := inline9Output q (scaledT (inline9Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 25) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline9Template, inline9Entry, inline9Output,
    scaledT, scaledRotation, inlineSum, inline9Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline9Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline9Template {s with pc := pc, stack := inline9Entry q rho} =
      some {s with pc := pcAfter pc inline9Template, stack := inline9Output q (scaledT (inline9Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 25) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline9Template_raw s pc q rho hstack hrun hactive

theorem run_inline9Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline9Template {s with pc := pc, stack := inline9Entry q rho} =
      some {s with pc := pcAfter pc inline9Template, stack := inline9WordStack q (PairedLaneWordRound.wordStep 0 13 7 (inline9Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline9Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 25) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 13 7 q.a q.b q.c q.d q.e
        (inline9Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline9Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 25)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline9Frame s.memory q) 0 13 7 (UInt256.ofNat 63) (UInt256.ofNat 25) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline9Output q (scaledT (inline9Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 25) (inline0Boolean q)) rho =
      inline9WordStack q
        (PairedLaneWordRound.wordStep 0 13 7 (inline9Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline9Output, inline9WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline9Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline9Template, stack := vs}) hout)

#print axioms inline9Template_length
#print axioms run_inline9Template_raw
#print axioms run_inline9Template
#print axioms run_inline9Template_word

def inline10Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 63),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline10Template_length : inline10Template.length = 44 := rfl

theorem run_inline10Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline10Template {s with pc := pc, stack := inline10Entry q rho} =
      some {s with pc := pcAfter pc inline10Template, stack := inline10Output q (scaledT (inline10Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 24) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline10Template, inline10Entry, inline10Output,
    scaledT, scaledRotation, inlineSum, inline10Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline10Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline10Template {s with pc := pc, stack := inline10Entry q rho} =
      some {s with pc := pcAfter pc inline10Template, stack := inline10Output q (scaledT (inline10Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 24) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline10Template_raw s pc q rho hstack hrun hactive

theorem run_inline10Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline10Template {s with pc := pc, stack := inline10Entry q rho} =
      some {s with pc := pcAfter pc inline10Template, stack := inline10WordStack q (PairedLaneWordRound.wordStep 0 14 8 (inline10Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline10Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 24) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 14 8 q.a q.b q.c q.d q.e
        (inline10Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline10Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 24)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline10Frame s.memory q) 0 14 8 (UInt256.ofNat 63) (UInt256.ofNat 24) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline10Output q (scaledT (inline10Frame s.memory q) q.lower (UInt256.ofNat 63) (UInt256.ofNat 24) (inline0Boolean q)) rho =
      inline10WordStack q
        (PairedLaneWordRound.wordStep 0 14 8 (inline10Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline10Output, inline10WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline10Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline10Template, stack := vs}) hout)

#print axioms inline10Template_length
#print axioms run_inline10Template_raw
#print axioms run_inline10Template
#print axioms run_inline10Template_word

def inline11Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 15),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline11Template_length : inline11Template.length = 44 := rfl

theorem run_inline11Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline11Template {s with pc := pc, stack := inline11Entry q rho} =
      some {s with pc := pcAfter pc inline11Template, stack := inline11Output q (scaledT (inline11Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 21) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline11Template, inline11Entry, inline11Output,
    scaledT, scaledRotation, inlineSum, inline11Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline11Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline11Template {s with pc := pc, stack := inline11Entry q rho} =
      some {s with pc := pcAfter pc inline11Template, stack := inline11Output q (scaledT (inline11Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 21) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline11Template_raw s pc q rho hstack hrun hactive

theorem run_inline11Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline11Template {s with pc := pc, stack := inline11Entry q rho} =
      some {s with pc := pcAfter pc inline11Template, stack := inline11WordStack q (PairedLaneWordRound.wordStep 0 15 11 (inline11Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline11Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 21) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 15 11 q.a q.b q.c q.d q.e
        (inline11Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline11Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 21)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline11Frame s.memory q) 0 15 11 (UInt256.ofNat 15) (UInt256.ofNat 21) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline11Output q (scaledT (inline11Frame s.memory q) q.lower (UInt256.ofNat 15) (UInt256.ofNat 21) (inline0Boolean q)) rho =
      inline11WordStack q
        (PairedLaneWordRound.wordStep 0 15 11 (inline11Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline11Output, inline11WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline11Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline11Template, stack := vs}) hout)

#print axioms inline11Template_length
#print axioms run_inline11Template_raw
#print axioms run_inline11Template
#print axioms run_inline11Template_word

def inline12Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline12Template_length : inline12Template.length = 44 := rfl

theorem run_inline12Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline12Template {s with pc := pc, stack := inline12Entry q rho} =
      some {s with pc := pcAfter pc inline12Template, stack := inline12Output q (scaledT (inline12Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 26) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline12Template, inline12Entry, inline12Output,
    scaledT, scaledRotation, inlineSum, inline12Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline12Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline12Template {s with pc := pc, stack := inline12Entry q rho} =
      some {s with pc := pcAfter pc inline12Template, stack := inline12Output q (scaledT (inline12Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 26) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline12Template_raw s pc q rho hstack hrun hactive

theorem run_inline12Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline12Template {s with pc := pc, stack := inline12Entry q rho} =
      some {s with pc := pcAfter pc inline12Template, stack := inline12WordStack q (PairedLaneWordRound.wordStep 0 6 14 (inline12Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline12Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 26) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 6 14 q.a q.b q.c q.d q.e
        (inline12Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline12Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 26)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline12Frame s.memory q) 0 6 14 (UInt256.ofNat 255) (UInt256.ofNat 26) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline12Output q (scaledT (inline12Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 26) (inline0Boolean q)) rho =
      inline12WordStack q
        (PairedLaneWordRound.wordStep 0 6 14 (inline12Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline12Output, inline12WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline12Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline12Template, stack := vs}) hout)

#print axioms inline12Template_length
#print axioms run_inline12Template_raw
#print axioms run_inline12Template
#print axioms run_inline12Template_word

def inline13Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 127),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline13Template_length : inline13Template.length = 44 := rfl

theorem run_inline13Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline13Template {s with pc := pc, stack := inline13Entry q rho} =
      some {s with pc := pcAfter pc inline13Template, stack := inline13Output q (scaledT (inline13Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 25) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline13Template, inline13Entry, inline13Output,
    scaledT, scaledRotation, inlineSum, inline13Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline13Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline13Template {s with pc := pc, stack := inline13Entry q rho} =
      some {s with pc := pcAfter pc inline13Template, stack := inline13Output q (scaledT (inline13Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 25) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline13Template_raw s pc q rho hstack hrun hactive

theorem run_inline13Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline13Template {s with pc := pc, stack := inline13Entry q rho} =
      some {s with pc := pcAfter pc inline13Template, stack := inline13WordStack q (PairedLaneWordRound.wordStep 0 7 14 (inline13Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline13Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 25) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 7 14 q.a q.b q.c q.d q.e
        (inline13Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline13Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 25)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline13Frame s.memory q) 0 7 14 (UInt256.ofNat 127) (UInt256.ofNat 25) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline13Output q (scaledT (inline13Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 25) (inline0Boolean q)) rho =
      inline13WordStack q
        (PairedLaneWordRound.wordStep 0 7 14 (inline13Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline13Output, inline13WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline13Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline13Template, stack := vs}) hout)

#print axioms inline13Template_length
#print axioms run_inline13Template_raw
#print axioms run_inline13Template
#print axioms run_inline13Template_word

def inline14Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 640),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 7),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline14Template_length : inline14Template.length = 44 := rfl

theorem run_inline14Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline14Template {s with pc := pc, stack := inline14Entry q rho} =
      some {s with pc := pcAfter pc inline14Template, stack := inline14Output q (scaledT (inline14Frame s.memory q) q.upper (UInt256.ofNat 7) (UInt256.ofNat 23) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline14Template, inline14Entry, inline14Output,
    scaledT, scaledRotation, inlineSum, inline14Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline14Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline14Template {s with pc := pc, stack := inline14Entry q rho} =
      some {s with pc := pcAfter pc inline14Template, stack := inline14Output q (scaledT (inline14Frame s.memory q) q.upper (UInt256.ofNat 7) (UInt256.ofNat 23) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline14Template_raw s pc q rho hstack hrun hactive

theorem run_inline14Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline14Template {s with pc := pc, stack := inline14Entry q rho} =
      some {s with pc := pcAfter pc inline14Template, stack := inline14WordStack q (PairedLaneWordRound.wordStep 0 9 12 (inline14Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline14Frame s.memory q) q.upper (UInt256.ofNat 7) (UInt256.ofNat 23) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 9 12 q.a q.b q.c q.d q.e
        (inline14Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline14Frame s.memory q) q.upper (UInt256.ofNat 7) (UInt256.ofNat 23)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline14Frame s.memory q) 0 9 12 (UInt256.ofNat 7) (UInt256.ofNat 23) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline14Output q (scaledT (inline14Frame s.memory q) q.upper (UInt256.ofNat 7) (UInt256.ofNat 23) (inline0Boolean q)) rho =
      inline14WordStack q
        (PairedLaneWordRound.wordStep 0 9 12 (inline14Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline14Output, inline14WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline14Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline14Template, stack := vs}) hout)

#print axioms inline14Template_length
#print axioms run_inline14Template_raw
#print axioms run_inline14Template
#print axioms run_inline14Template_word

def inline15Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline15Template_length : inline15Template.length = 44 := rfl

theorem run_inline15Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc inline15Template, stack := inline15Output q (scaledT (inline15Frame s.memory q) q.lower (UInt256.ofNat 3) (UInt256.ofNat 26) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline15Template, inline15Entry, inline15Output,
    scaledT, scaledRotation, inlineSum, inline15Frame, zeroRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline15Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc inline15Template, stack := inline15Output q (scaledT (inline15Frame s.memory q) q.lower (UInt256.ofNat 3) (UInt256.ofNat 26) (inline0Boolean q)) rho} := by
  simpa only [zeroRaw_eq_inline0Boolean] using
    run_inline15Template_raw s pc q rho hstack hrun hactive

theorem run_inline15Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc inline15Template, stack := inline15WordStack q (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline15Frame s.memory q) q.lower (UInt256.ofNat 3) (UInt256.ofNat 26) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 8 6 q.a q.b q.c q.d q.e
        (inline15Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline15Frame s.memory q) q.lower (UInt256.ofNat 3) (UInt256.ofNat 26)) (inline0Boolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline15Frame s.memory q) 0 8 6 (UInt256.ofNat 3) (UInt256.ofNat 26) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline15Output q (scaledT (inline15Frame s.memory q) q.lower (UInt256.ofNat 3) (UInt256.ofNat 26) (inline0Boolean q)) rho =
      inline15WordStack q
        (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline15Output, inline15WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline15Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline15Template, stack := vs}) hout)

#print axioms inline15Template_length
#print axioms run_inline15Template_raw
#print axioms run_inline15Template
#print axioms run_inline15Template_word

def inline64Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline64Template_length : inline64Template.length = 46 := rfl

theorem run_inline64Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline64Template {s with pc := pc, stack := inline64Entry q rho} =
      some {s with pc := pcAfter pc inline64Template, stack := inline64Output q (inlineT (inline64Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline64Template, inline64Entry, inline64Output,
    inlineT, inlineRotation, inline64Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline64Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline64Template {s with pc := pc, stack := inline64Entry q rho} =
      some {s with pc := pcAfter pc inline64Template, stack := inline64Output q (inlineT (inline64Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline64Template_raw s pc q rho hstack hrun hactive

#print axioms inline64Template_length
#print axioms run_inline64Template_raw
#print axioms run_inline64Template
def inline65Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 10),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline65Template_length : inline65Template.length = 46 := rfl

theorem run_inline65Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline65Template {s with pc := pc, stack := inline65Entry q rho} =
      some {s with pc := pcAfter pc inline65Template, stack := inline65Output q (inlineT (inline65Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline65Template, inline65Entry, inline65Output,
    inlineT, inlineRotation, inline65Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline65Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline65Template {s with pc := pc, stack := inline65Entry q rho} =
      some {s with pc := pcAfter pc inline65Template, stack := inline65Output q (inlineT (inline65Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline65Template_raw s pc q rho hstack hrun hactive

#print axioms inline65Template_length
#print axioms run_inline65Template_raw
#print axioms run_inline65Template
def inline66Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline66Template_length : inline66Template.length = 47 := rfl

theorem run_inline66Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline66Template {s with pc := pc, stack := inline66Entry q rho} =
      some {s with pc := pcAfter pc inline66Template, stack := inline66Output q (inlineT (inline66Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline66Template, inline66Entry, inline66Output,
    inlineT, inlineRotation, inline66Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline66Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline66Template {s with pc := pc, stack := inline66Entry q rho} =
      some {s with pc := pcAfter pc inline66Template, stack := inline66Output q (inlineT (inline66Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline66Template_raw s pc q rho hstack hrun hactive

#print axioms inline66Template_length
#print axioms run_inline66Template_raw
#print axioms run_inline66Template
def inline67Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 336),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 2),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline67Template_length : inline67Template.length = 46 := rfl

theorem run_inline67Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline67Template {s with pc := pc, stack := inline67Entry q rho} =
      some {s with pc := pcAfter pc inline67Template, stack := inline67Output q (inlineT (inline67Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline67Template, inline67Entry, inline67Output,
    inlineT, inlineRotation, inline67Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline67Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline67Template {s with pc := pc, stack := inline67Entry q rho} =
      some {s with pc := pcAfter pc inline67Template, stack := inline67Output q (inlineT (inline67Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline67Template_raw s pc q rho hstack hrun hactive

#print axioms inline67Template_length
#print axioms run_inline67Template_raw
#print axioms run_inline67Template
def inline68Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline68Template_length : inline68Template.length = 47 := rfl

theorem run_inline68Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline68Template {s with pc := pc, stack := inline68Entry q rho} =
      some {s with pc := pcAfter pc inline68Template, stack := inline68Output q (inlineT (inline68Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline68Template, inline68Entry, inline68Output,
    inlineT, inlineRotation, inline68Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline68Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline68Template {s with pc := pc, stack := inline68Entry q rho} =
      some {s with pc := pcAfter pc inline68Template, stack := inline68Output q (inlineT (inline68Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline68Template_raw s pc q rho hstack hrun hactive

#print axioms inline68Template_length
#print axioms run_inline68Template_raw
#print axioms run_inline68Template
def inline69Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline69Template_length : inline69Template.length = 46 := rfl

theorem run_inline69Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline69Template {s with pc := pc, stack := inline69Entry q rho} =
      some {s with pc := pcAfter pc inline69Template, stack := inline69Output q (inlineT (inline69Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline69Template, inline69Entry, inline69Output,
    inlineT, inlineRotation, inline69Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline69Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline69Template {s with pc := pc, stack := inline69Entry q rho} =
      some {s with pc := pcAfter pc inline69Template, stack := inline69Output q (inlineT (inline69Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline69Template_raw s pc q rho hstack hrun hactive

#print axioms inline69Template_length
#print axioms run_inline69Template_raw
#print axioms run_inline69Template
def inline70Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline70Template_length : inline70Template.length = 47 := rfl

theorem run_inline70Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline70Template {s with pc := pc, stack := inline70Entry q rho} =
      some {s with pc := pcAfter pc inline70Template, stack := inline70Output q (inlineT (inline70Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline70Template, inline70Entry, inline70Output,
    inlineT, inlineRotation, inline70Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline70Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline70Template {s with pc := pc, stack := inline70Entry q rho} =
      some {s with pc := pcAfter pc inline70Template, stack := inline70Output q (inlineT (inline70Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline70Template_raw s pc q rho hstack hrun hactive

#print axioms inline70Template_length
#print axioms run_inline70Template_raw
#print axioms run_inline70Template
def inline71Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 6),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline71Template_length : inline71Template.length = 46 := rfl

theorem run_inline71Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline71Template {s with pc := pc, stack := inline71Entry q rho} =
      some {s with pc := pcAfter pc inline71Template, stack := inline71Output q (inlineT (inline71Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline71Template, inline71Entry, inline71Output,
    inlineT, inlineRotation, inline71Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline71Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline71Template {s with pc := pc, stack := inline71Entry q rho} =
      some {s with pc := pcAfter pc inline71Template, stack := inline71Output q (inlineT (inline71Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline71Template_raw s pc q rho hstack hrun hactive

#print axioms inline71Template_length
#print axioms run_inline71Template_raw
#print axioms run_inline71Template
def inline72Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 640),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 400),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline72Template_length : inline72Template.length = 47 := rfl

theorem run_inline72Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline72Template {s with pc := pc, stack := inline72Entry q rho} =
      some {s with pc := pcAfter pc inline72Template, stack := inline72Output q (inlineT (inline72Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline72Template, inline72Entry, inline72Output,
    inlineT, inlineRotation, inline72Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline72Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline72Template {s with pc := pc, stack := inline72Entry q rho} =
      some {s with pc := pcAfter pc inline72Template, stack := inline72Output q (inlineT (inline72Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline72Template_raw s pc q rho hstack hrun hactive

#print axioms inline72Template_length
#print axioms run_inline72Template_raw
#print axioms run_inline72Template
def inline73Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline73Template_length : inline73Template.length = 47 := rfl

theorem run_inline73Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline73Template {s with pc := pc, stack := inline73Entry q rho} =
      some {s with pc := pcAfter pc inline73Template, stack := inline73Output q (inlineT (inline73Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline73Template, inline73Entry, inline73Output,
    inlineT, inlineRotation, inline73Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline73Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline73Template {s with pc := pc, stack := inline73Entry q rho} =
      some {s with pc := pcAfter pc inline73Template, stack := inline73Output q (inlineT (inline73Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline73Template_raw s pc q rho hstack hrun hactive

#print axioms inline73Template_length
#print axioms run_inline73Template_raw
#print axioms run_inline73Template
def inline74Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 7),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline74Template_length : inline74Template.length = 46 := rfl

theorem run_inline74Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline74Template {s with pc := pc, stack := inline74Entry q rho} =
      some {s with pc := pcAfter pc inline74Template, stack := inline74Output q (inlineT (inline74Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline74Template, inline74Entry, inline74Output,
    inlineT, inlineRotation, inline74Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline74Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline74Template {s with pc := pc, stack := inline74Entry q rho} =
      some {s with pc := pcAfter pc inline74Template, stack := inline74Output q (inlineT (inline74Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline74Template_raw s pc q rho hstack hrun hactive

#print axioms inline74Template_length
#print axioms run_inline74Template_raw
#print axioms run_inline74Template
def inline75Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 9),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline75Template_length : inline75Template.length = 46 := rfl

theorem run_inline75Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline75Template {s with pc := pc, stack := inline75Entry q rho} =
      some {s with pc := pcAfter pc inline75Template, stack := inline75Output q (inlineT (inline75Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline75Template, inline75Entry, inline75Output,
    inlineT, inlineRotation, inline75Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline75Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline75Template {s with pc := pc, stack := inline75Entry q rho} =
      some {s with pc := pcAfter pc inline75Template, stack := inline75Output q (inlineT (inline75Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline75Template_raw s pc q rho hstack hrun hactive

#print axioms inline75Template_length
#print axioms run_inline75Template_raw
#print axioms run_inline75Template
def inline76Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline76Template_length : inline76Template.length = 47 := rfl

theorem run_inline76Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline76Template {s with pc := pc, stack := inline76Entry q rho} =
      some {s with pc := pcAfter pc inline76Template, stack := inline76Output q (inlineT (inline76Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline76Template, inline76Entry, inline76Output,
    inlineT, inlineRotation, inline76Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline76Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline76Template {s with pc := pc, stack := inline76Entry q rho} =
      some {s with pc := pcAfter pc inline76Template, stack := inline76Output q (inlineT (inline76Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline76Template_raw s pc q rho hstack hrun hactive

#print axioms inline76Template_length
#print axioms run_inline76Template_raw
#print axioms run_inline76Template
def inline77Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline77Template_length : inline77Template.length = 47 := rfl

theorem run_inline77Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline77Template {s with pc := pc, stack := inline77Entry q rho} =
      some {s with pc := pcAfter pc inline77Template, stack := inline77Output q (inlineT (inline77Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline77Template, inline77Entry, inline77Output,
    inlineT, inlineRotation, inline77Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline77Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline77Template {s with pc := pc, stack := inline77Entry q rho} =
      some {s with pc := pcAfter pc inline77Template, stack := inline77Output q (inlineT (inline77Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline77Template_raw s pc q rho hstack hrun hactive

#print axioms inline77Template_length
#print axioms run_inline77Template_raw
#print axioms run_inline77Template
def inline78Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 496),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline78Template_length : inline78Template.length = 47 := rfl

theorem run_inline78Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline78Template {s with pc := pc, stack := inline78Entry q rho} =
      some {s with pc := pcAfter pc inline78Template, stack := inline78Output q (inlineT (inline78Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline78Template, inline78Entry, inline78Output,
    inlineT, inlineRotation, inline78Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline78Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline78Template {s with pc := pc, stack := inline78Entry q rho} =
      some {s with pc := pcAfter pc inline78Template, stack := inline78Output q (inlineT (inline78Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline78Template_raw s pc q rho hstack hrun hactive

#print axioms inline78Template_length
#print axioms run_inline78Template_raw
#print axioms run_inline78Template
def inline79Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 560),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline79Template_length : inline79Template.length = 47 := rfl

theorem run_inline79Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline79Template {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc inline79Template, stack := inline79Output q (inlineT (inline79Frame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline79Template, inline79Entry, inline79Output,
    inlineT, inlineRotation, inline79Frame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline79Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline79Template {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc inline79Template, stack := inline79Output q (inlineT (inline79Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline79Template_raw s pc q rho hstack hrun hactive

#print axioms inline79Template_length
#print axioms run_inline79Template_raw
#print axioms run_inline79Template
def oneRaw (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  UInt256.lor (UInt256.land q.c q.b)
    (UInt256.xor q.d (UInt256.land (UInt256.lor q.d q.c) (UInt256.xor q.upper q.b)))

def threeRaw (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  UInt256.xor q.c
    (UInt256.land (UInt256.xor (UInt256.lor q.upper q.c) q.b)
      (UInt256.xor (UInt256.land q.upper q.c) q.d))

theorem oneRaw_eq_oneWord (q : PairedHelperBooleanTrace.Frame) :
    oneRaw q = PairedLaneBooleanSynthesis.oneWord q.b q.c q.d q.upper := by
  apply bits_injective
  simp only [oneRaw, PairedLaneBooleanSynthesis.oneWord, bits_lor, bits_land, bits_xor]
  ac_rfl

#print axioms oneRaw_eq_oneWord

theorem threeRaw_eq_threeWord (q : PairedHelperBooleanTrace.Frame) :
    threeRaw q = PairedLaneBooleanSynthesis.threeWord q.b q.c q.d q.upper := by
  apply bits_injective
  simp only [threeRaw, PairedLaneBooleanSynthesis.threeWord, bits_lor, bits_land, bits_xor]
  ac_rfl

#print axioms threeRaw_eq_threeWord

theorem oneRaw_eq_rawBoolean (q : PairedHelperBooleanTrace.Frame) :
    oneRaw q = rawBoolean q := by
  apply bits_injective
  simp only [oneRaw, rawBoolean, bits_lor, bits_land, bits_xor, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits q.upper).getLsbD i <;> rfl

#print axioms oneRaw_eq_rawBoolean

theorem threeRaw_eq_inline3Boolean (q : PairedHelperBooleanTrace.Frame) :
    threeRaw q = inline3Boolean q := by
  apply bits_injective
  simp only [threeRaw, inline3Boolean, bits_lor, bits_land, bits_xor, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits q.upper).getLsbD i <;> rfl

#print axioms threeRaw_eq_inline3Boolean

def template : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op .OR]

theorem template_length : template.length = 15 := rfl

theorem run_template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := pcAfter pc template, stack := firstTEntry q (oneRaw q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, entryStack, firstTEntry, oneRaw,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl

theorem run_template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := pcAfter pc template, stack := resultStack q rho} := by
  have h := run_template_raw s pc q rho hstack hrun
  simpa only [oneRaw_eq_rawBoolean, firstTEntry, resultStack] using h

#print axioms template_length
#print axioms run_template_raw
#print axioms run_template

def secondBooleanTemplate : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op .OR]

theorem secondBooleanTemplate_length : secondBooleanTemplate.length = 14 := rfl

theorem run_secondBooleanTemplate_raw (s : State) (pc first : UInt256)
    (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondBooleanTemplate {s with pc := pc, stack := afterC10Stack q first rho} =
      some {s with pc := pcAfter pc secondBooleanTemplate, stack := secondTEntry q first (oneRaw (secondFrame q first)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [secondBooleanTemplate, afterC10Stack, secondTEntry,
    secondFrame, oneRaw, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap]
  rfl

theorem run_secondBooleanTemplate (s : State) (pc first : UInt256)
    (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondBooleanTemplate {s with pc := pc, stack := afterC10Stack q first rho} =
      some {s with pc := pcAfter pc secondBooleanTemplate, stack := secondTEntry q first (rawBoolean (secondFrame q first)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_secondBooleanTemplate_raw s pc first q rho hstack hrun

#print axioms secondBooleanTemplate_length
#print axioms run_secondBooleanTemplate_raw
#print axioms run_secondBooleanTemplate

/-- Local two-SWAP elision from fkiene's public de17e3ad; old shared source stays unchanged. -/
def firstTTemplate : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .SHR,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND]

theorem firstTTemplate_length : firstTTemplate.length = 23 := rfl

theorem run_firstTTemplate (s : State) (pc value : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq firstTTemplate {s with pc := pc, stack := firstTEntry q value rho} =
      some {s with pc := pcAfter pc firstTTemplate, stack := afterTStack q (rawT q value) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [firstTTemplate, firstTEntry, afterTStack,
    rawT, rawRotation, rawProduct, rawSum, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩

#print axioms firstTTemplate_length
#print axioms run_firstTTemplate

def secondTTemplate : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .SHR,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND]

theorem secondTTemplate_length : secondTTemplate.length = 23 := rfl

theorem run_secondTTemplate (s : State) (pc first value : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondTTemplate {s with pc := pc, stack := secondTEntry q first value rho} =
      some {s with pc := pcAfter pc secondTTemplate, stack := secondTStack q first (rawT (secondFrame q first) value) rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [secondTTemplate, secondTEntry, secondTStack,
    rawT, rawRotation, rawProduct, rawSum, secondFrame, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩

#print axioms secondTTemplate_length
#print axioms run_secondTTemplate

def fullTemplate : List Instr :=
  (((((template ++ firstTTemplate) ++ firstC10Template) ++ secondBooleanTemplate) ++
    secondTTemplate) ++ secondC10Template) ++ returnTemplate

theorem fullTemplate_length : fullTemplate.length = 91 := by decide

theorem fullTemplate_byteLength : (fullTemplate.map Instr.size).sum = 93 := by decide

theorem run_fullTemplate (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code q.ret.toNat = true) :
    runInstrSeq fullTemplate {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := q.ret, stack := returnedStack q (rawT q (rawBoolean q)) (rawT (secondFrame q (rawT q (rawBoolean q))) (rawBoolean (secondFrame q (rawT q (rawBoolean q))))) rho} := by
  let first := rawT q (rawBoolean q)
  let second := rawT (secondFrame q first) (rawBoolean (secondFrame q first))
  let p1 := pcAfter pc template
  let p2 := pcAfter p1 firstTTemplate
  let p3 := pcAfter p2 firstC10Template
  let p4 := pcAfter p3 secondBooleanTemplate
  let p5 := pcAfter p4 secondTTemplate
  let p6 := pcAfter p5 secondC10Template
  have h0 := run_template s pc q rho hstack hrun
  have h1 := run_firstTTemplate s p1 (rawBoolean q) q rho hstack hrun
  have h2 := run_firstC10Template s p2 first q rho hstack hrun
  have h3 := run_secondBooleanTemplate s p3 first q rho hstack hrun
  have h4 := run_secondTTemplate s p4 first (rawBoolean (secondFrame q first)) q rho hstack hrun
  have h5 := run_secondC10Template s p5 first second q rho hstack hrun
  have h6 := run_returnTemplate s p6 first second q rho hstack hrun hvalid
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 hrun h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 hrun h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 hrun h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 hrun h5
  have h06 := DenseScheduleTrace.runInstrSeq_append_running h05 hrun h6
  exact h06



#print axioms fullTemplate_length
#print axioms fullTemplate_byteLength
#print axioms run_fullTemplate


def frozenHelperInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .SHR,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Swap ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .SHR,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op .JUMP]

theorem fullTemplate_eq_frozenHelper : fullTemplate = frozenHelperInstructions := rfl

#print axioms fullTemplate_eq_frozenHelper


def inline18Template : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline18Template_length : inline18Template.length = 48 := rfl

theorem run_inline18Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline18Template {s with pc := pc, stack := inline18Entry q rho} =
      some {s with pc := pcAfter pc inline18Template, stack := inline18Output q (inlineT (inline18Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline18Template, inline18Entry, inline18Output,
    inlineT, inlineRotation, inline18Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline18Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline18Template {s with pc := pc, stack := inline18Entry q rho} =
      some {s with pc := pcAfter pc inline18Template, stack := inline18Output q (inlineT (inline18Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline18Template_raw s pc q rho hstack hrun hactive

#print axioms inline18Template_length
#print axioms run_inline18Template_raw
#print axioms run_inline18Template


def inline19Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 6),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline19Template_length : inline19Template.length = 48 := rfl

theorem run_inline19Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline19Template {s with pc := pc, stack := inline19Entry q rho} =
      some {s with pc := pcAfter pc inline19Template, stack := inline19Output q (inlineT (inline19Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline19Template, inline19Entry, inline19Output,
    inlineT, inlineRotation, inline19Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline19Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline19Template {s with pc := pc, stack := inline19Entry q rho} =
      some {s with pc := pcAfter pc inline19Template, stack := inline19Output q (inlineT (inline19Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline19Template_raw s pc q rho hstack hrun hactive

#print axioms inline19Template_length
#print axioms run_inline19Template_raw
#print axioms run_inline19Template


abbrev inline22Frame := PairedCall22Inline.inline22Frame

abbrev inline22Template : List Instr := PairedCall22Inline.inline22Template

abbrev inline23Frame := PairedCall22Inline.inline23Frame

abbrev inline23Template : List Instr := PairedCall22Inline.inline23Template

/-- The added SWAP1 explicitly restores the parent inline24 entry frame. -/
def inline24Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline24Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline24Template_length : inline24Template.length = 40 := rfl

theorem run_inline24Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline24Template {s with pc := pc, stack := inline24Entry q rho} =
      some {s with pc := pcAfter pc inline24Template, stack := inline24Output q (singleT (inline24Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline24Template, inline24Entry, inline24Output,
    singleT, inline24Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline24Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline24Template {s with pc := pc, stack := inline24Entry q rho} =
      some {s with pc := pcAfter pc inline24Template, stack := inline24Output q (singleT (inline24Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline24Template_raw s pc q rho hstack hrun hactive

#print axioms inline24Template_length
#print axioms run_inline24Template_raw
#print axioms run_inline24Template


def inline25Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 5),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline25Template_length : inline25Template.length = 48 := rfl

theorem run_inline25Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline25Template {s with pc := pc, stack := inline25Entry q rho} =
      some {s with pc := pcAfter pc inline25Template, stack := inline25Output q (inlineT (inline25Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline25Template, inline25Entry, inline25Output,
    inlineT, inlineRotation, inline25Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline25Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline25Template {s with pc := pc, stack := inline25Entry q rho} =
      some {s with pc := pcAfter pc inline25Template, stack := inline25Output q (inlineT (inline25Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline25Template_raw s pc q rho hstack hrun hactive

#print axioms inline25Template_length
#print axioms run_inline25Template_raw
#print axioms run_inline25Template


def inline30Template : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline30Template_length : inline30Template.length = 39 := rfl

theorem run_inline30Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline30Template {s with pc := pc, stack := inline30Entry q rho} =
      some {s with pc := pcAfter pc inline30Template, stack := inline30Output q (singleT (inline30Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline30Template, inline30Entry, inline30Output,
    singleT, inline30Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline30Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline30Template {s with pc := pc, stack := inline30Entry q rho} =
      some {s with pc := pcAfter pc inline30Template, stack := inline30Output q (singleT (inline30Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline30Template_raw s pc q rho hstack hrun hactive

#print axioms inline30Template_length
#print axioms run_inline30Template_raw
#print axioms run_inline30Template


def inline31Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op .OR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline31Template_length : inline31Template.length = 48 := rfl

theorem run_inline31Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline31Template {s with pc := pc, stack := inline31Entry q rho} =
      some {s with pc := pcAfter pc inline31Template, stack := inline31Output q (inlineT (inline31Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline31Template, inline31Entry, inline31Output,
    inlineT, inlineRotation, inline31Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline31Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline31Template {s with pc := pc, stack := inline31Entry q rho} =
      some {s with pc := pcAfter pc inline31Template, stack := inline31Output q (inlineT (inline31Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline31Template_raw s pc q rho hstack hrun hactive

#print axioms inline31Template_length
#print axioms run_inline31Template_raw
#print axioms run_inline31Template


def inline48Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline48Template_length : inline48Template.length = 49 := rfl

theorem run_inline48Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline48Template {s with pc := pc, stack := inline48Entry q rho} =
      some {s with pc := pcAfter pc inline48Template, stack := inline48Output q (inlineT (inline48Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline48Template, inline48Entry, inline48Output,
    inlineT, inlineRotation, inline48Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline48Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline48Template {s with pc := pc, stack := inline48Entry q rho} =
      some {s with pc := pcAfter pc inline48Template, stack := inline48Output q (inlineT (inline48Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline48Template_raw s pc q rho hstack hrun hactive

#print axioms inline48Template_length
#print axioms run_inline48Template_raw
#print axioms run_inline48Template


def inline49Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 400),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 7),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline49Template_length : inline49Template.length = 48 := rfl

theorem run_inline49Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline49Template {s with pc := pc, stack := inline49Entry q rho} =
      some {s with pc := pcAfter pc inline49Template, stack := inline49Output q (inlineT (inline49Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline49Template, inline49Entry, inline49Output,
    inlineT, inlineRotation, inline49Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline49Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline49Template {s with pc := pc, stack := inline49Entry q rho} =
      some {s with pc := pcAfter pc inline49Template, stack := inline49Output q (inlineT (inline49Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline49Template_raw s pc q rho hstack hrun hactive

#print axioms inline49Template_length
#print axioms run_inline49Template_raw
#print axioms run_inline49Template


def inline50Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 336),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 6),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline50Template_length : inline50Template.length = 48 := rfl

theorem run_inline50Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline50Template {s with pc := pc, stack := inline50Entry q rho} =
      some {s with pc := pcAfter pc inline50Template, stack := inline50Output q (inlineT (inline50Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline50Template, inline50Entry, inline50Output,
    inlineT, inlineRotation, inline50Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline50Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline50Template {s with pc := pc, stack := inline50Entry q rho} =
      some {s with pc := pcAfter pc inline50Template, stack := inline50Output q (inlineT (inline50Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline50Template_raw s pc q rho hstack hrun hactive

#print axioms inline50Template_length
#print axioms run_inline50Template_raw
#print axioms run_inline50Template


def inline51Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 4),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline51Template_length : inline51Template.length = 48 := rfl

theorem run_inline51Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline51Template {s with pc := pc, stack := inline51Entry q rho} =
      some {s with pc := pcAfter pc inline51Template, stack := inline51Output q (inlineT (inline51Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline51Template, inline51Entry, inline51Output,
    inlineT, inlineRotation, inline51Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline51Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline51Template {s with pc := pc, stack := inline51Entry q rho} =
      some {s with pc := pcAfter pc inline51Template, stack := inline51Output q (inlineT (inline51Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline51Template_raw s pc q rho hstack hrun hactive

#print axioms inline51Template_length
#print axioms run_inline51Template_raw
#print axioms run_inline51Template


def inline52Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline52Template_length : inline52Template.length = 40 := rfl

theorem run_inline52Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline52Template {s with pc := pc, stack := inline52Entry q rho} =
      some {s with pc := pcAfter pc inline52Template, stack := inline52Output q (singleT (inline52Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline52Template, inline52Entry, inline52Output,
    singleT, inline52Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline52Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline52Template {s with pc := pc, stack := inline52Entry q rho} =
      some {s with pc := pcAfter pc inline52Template, stack := inline52Output q (singleT (inline52Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline52Template_raw s pc q rho hstack hrun hactive

#print axioms inline52Template_length
#print axioms run_inline52Template_raw
#print axioms run_inline52Template


def inline53Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 560),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline53Template_length : inline53Template.length = 48 := rfl

theorem run_inline53Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline53Template {s with pc := pc, stack := inline53Entry q rho} =
      some {s with pc := pcAfter pc inline53Template, stack := inline53Output q (inlineT (inline53Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline53Template, inline53Entry, inline53Output,
    inlineT, inlineRotation, inline53Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline53Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline53Template {s with pc := pc, stack := inline53Entry q rho} =
      some {s with pc := pcAfter pc inline53Template, stack := inline53Output q (inlineT (inline53Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline53Template_raw s pc q rho hstack hrun hactive

#print axioms inline53Template_length
#print axioms run_inline53Template_raw
#print axioms run_inline53Template


def inline54Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline54Template_length : inline54Template.length = 48 := rfl

theorem run_inline54Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline54Template {s with pc := pc, stack := inline54Entry q rho} =
      some {s with pc := pcAfter pc inline54Template, stack := inline54Output q (inlineT (inline54Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline54Template, inline54Entry, inline54Output,
    inlineT, inlineRotation, inline54Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline54Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline54Template {s with pc := pc, stack := inline54Entry q rho} =
      some {s with pc := pcAfter pc inline54Template, stack := inline54Output q (inlineT (inline54Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline54Template_raw s pc q rho hstack hrun hactive

#print axioms inline54Template_length
#print axioms run_inline54Template_raw
#print axioms run_inline54Template


def inline55Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline55Template_length : inline55Template.length = 49 := rfl

theorem run_inline55Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline55Template {s with pc := pc, stack := inline55Entry q rho} =
      some {s with pc := pcAfter pc inline55Template, stack := inline55Output q (inlineT (inline55Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline55Template, inline55Entry, inline55Output,
    inlineT, inlineRotation, inline55Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline55Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline55Template {s with pc := pc, stack := inline55Entry q rho} =
      some {s with pc := pcAfter pc inline55Template, stack := inline55Output q (inlineT (inline55Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline55Template_raw s pc q rho hstack hrun hactive

#print axioms inline55Template_length
#print axioms run_inline55Template_raw
#print axioms run_inline55Template


def inline56Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline56Template_length : inline56Template.length = 48 := rfl

theorem run_inline56Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline56Template {s with pc := pc, stack := inline56Entry q rho} =
      some {s with pc := pcAfter pc inline56Template, stack := inline56Output q (inlineT (inline56Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline56Template, inline56Entry, inline56Output,
    inlineT, inlineRotation, inline56Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline56Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline56Template {s with pc := pc, stack := inline56Entry q rho} =
      some {s with pc := pcAfter pc inline56Template, stack := inline56Output q (inlineT (inline56Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline56Template_raw s pc q rho hstack hrun hactive

#print axioms inline56Template_length
#print axioms run_inline56Template_raw
#print axioms run_inline56Template


def inline57Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 5),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline57Template_length : inline57Template.length = 48 := rfl

theorem run_inline57Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline57Template {s with pc := pc, stack := inline57Entry q rho} =
      some {s with pc := pcAfter pc inline57Template, stack := inline57Output q (inlineT (inline57Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline57Template, inline57Entry, inline57Output,
    inlineT, inlineRotation, inline57Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline57Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline57Template {s with pc := pc, stack := inline57Entry q rho} =
      some {s with pc := pcAfter pc inline57Template, stack := inline57Output q (inlineT (inline57Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline57Template_raw s pc q rho hstack hrun hactive

#print axioms inline57Template_length
#print axioms run_inline57Template_raw
#print axioms run_inline57Template


def inline58Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline58Template_length : inline58Template.length = 49 := rfl

theorem run_inline58Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline58Template {s with pc := pc, stack := inline58Entry q rho} =
      some {s with pc := pcAfter pc inline58Template, stack := inline58Output q (inlineT (inline58Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline58Template, inline58Entry, inline58Output,
    inlineT, inlineRotation, inline58Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline58Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline58Template {s with pc := pc, stack := inline58Entry q rho} =
      some {s with pc := pcAfter pc inline58Template, stack := inline58Output q (inlineT (inline58Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline58Template_raw s pc q rho hstack hrun hactive

#print axioms inline58Template_length
#print axioms run_inline58Template_raw
#print axioms run_inline58Template


def inline59Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline59Template_length : inline59Template.length = 49 := rfl

theorem run_inline59Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline59Template {s with pc := pc, stack := inline59Entry q rho} =
      some {s with pc := pcAfter pc inline59Template, stack := inline59Output q (inlineT (inline59Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline59Template, inline59Entry, inline59Output,
    inlineT, inlineRotation, inline59Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline59Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline59Template {s with pc := pc, stack := inline59Entry q rho} =
      some {s with pc := pcAfter pc inline59Template, stack := inline59Output q (inlineT (inline59Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline59Template_raw s pc q rho hstack hrun hactive

#print axioms inline59Template_length
#print axioms run_inline59Template_raw
#print axioms run_inline59Template


def inline60Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 640),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 496),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline60Template_length : inline60Template.length = 49 := rfl

theorem run_inline60Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline60Template {s with pc := pc, stack := inline60Entry q rho} =
      some {s with pc := pcAfter pc inline60Template, stack := inline60Output q (inlineT (inline60Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline60Template, inline60Entry, inline60Output,
    inlineT, inlineRotation, inline60Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline60Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline60Template {s with pc := pc, stack := inline60Entry q rho} =
      some {s with pc := pcAfter pc inline60Template, stack := inline60Output q (inlineT (inline60Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline60Template_raw s pc q rho hstack hrun hactive

#print axioms inline60Template_length
#print axioms run_inline60Template_raw
#print axioms run_inline60Template


def inline61Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline61Template_length : inline61Template.length = 48 := rfl

theorem run_inline61Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline61Template {s with pc := pc, stack := inline61Entry q rho} =
      some {s with pc := pcAfter pc inline61Template, stack := inline61Output q (inlineT (inline61Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline61Template, inline61Entry, inline61Output,
    inlineT, inlineRotation, inline61Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline61Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline61Template {s with pc := pc, stack := inline61Entry q rho} =
      some {s with pc := pcAfter pc inline61Template, stack := inline61Output q (inlineT (inline61Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline61Template_raw s pc q rho hstack hrun hactive

#print axioms inline61Template_length
#print axioms run_inline61Template_raw
#print axioms run_inline61Template


def inline62Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline62Template_length : inline62Template.length = 49 := rfl

theorem run_inline62Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline62Template {s with pc := pc, stack := inline62Entry q rho} =
      some {s with pc := pcAfter pc inline62Template, stack := inline62Output q (inlineT (inline62Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline62Template, inline62Entry, inline62Output,
    inlineT, inlineRotation, inline62Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline62Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline62Template {s with pc := pc, stack := inline62Entry q rho} =
      some {s with pc := pcAfter pc inline62Template, stack := inline62Output q (inlineT (inline62Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline62Template_raw s pc q rho hstack hrun hactive

#print axioms inline62Template_length
#print axioms run_inline62Template_raw
#print axioms run_inline62Template


def inline63Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op .XOR,
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 4),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline63Template_length : inline63Template.length = 48 := rfl

theorem run_inline63Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline63Template {s with pc := pc, stack := inline63Entry q rho} =
      some {s with pc := pcAfter pc inline63Template, stack := inline63Output q (inlineT (inline63Frame s.memory q) (threeRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline63Template, inline63Entry, inline63Output,
    inlineT, inlineRotation, inline63Frame, threeRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline63Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline63Template {s with pc := pc, stack := inline63Entry q rho} =
      some {s with pc := pcAfter pc inline63Template, stack := inline63Output q (inlineT (inline63Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline63Template_raw s pc q rho hstack hrun hactive

#print axioms inline63Template_length
#print axioms run_inline63Template_raw
#print axioms run_inline63Template


/-- The new raw group-two Boolean: no support premise is built into the definition. -/
def inlineHoistedBoolean (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  rawHoistedBoolean q.b q.c q.d

theorem rawSum_hoisted (q : PairedHelperBooleanTrace.Frame) (hpair : q.pair = pairWord) :
    rawSum q (inlineHoistedBoolean q) =
      hoistedSum q.a q.b q.c q.d q.message0 q.k := by
  have hb : inlineHoistedBoolean q = hoistedBoolean q.b q.c q.d :=
    rawHoistedBoolean_eq q.b q.c q.d
  have hs (v : UInt256) :
      rawSum q v =
        UInt256.land (UInt256.add (UInt256.add (UInt256.add q.a v) q.message0) q.k) pairWord := by
    apply bits_injective
    simp only [rawSum, hpair, bits_land, bits_add]
    ac_rfl
  exact (congrArg (rawSum q) hb).trans (hs (hoistedBoolean q.b q.c q.d))

#print axioms rawSum_hoisted

theorem scaledT_hoisted_low (q : PairedHelperBooleanTrace.Frame) (r s : Nat)
    (scale shift : UInt256) (hlt : s < r)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hlower : q.lower = lowerWord)
    (hscale : scale = UInt256.ofNat (2 ^ (r - s) - 1))
    (hshift : shift = UInt256.ofNat (32 - s)) :
    scaledT q q.lower scale shift (inlineHoistedBoolean q) =
      hoistedT r s q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [scaledT, scaledRotation_eq_low q _ r s scale shift hlt hfactor hlower hscale hshift,
    rawSum_hoisted q hpair, hoistedT]
  apply bits_injective
  simp only [hpair, bits_land, bits_add]
  ac_rfl

theorem scaledT_hoisted_high (q : PairedHelperBooleanTrace.Frame) (r s : Nat)
    (scale shift : UInt256) (hlt : r < s)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hscale : scale = UInt256.ofNat (2 ^ (s - r) - 1))
    (hshift : shift = UInt256.ofNat (32 - r)) :
    scaledT q q.upper scale shift (inlineHoistedBoolean q) =
      hoistedT r s q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [scaledT, scaledRotation_eq_high q _ r s scale shift hlt hfactor hupper hscale hshift,
    rawSum_hoisted q hpair, hoistedT]
  apply bits_injective
  simp only [hpair, bits_land, bits_add]
  ac_rfl

theorem scaledOneT_hoisted_low (q : PairedHelperBooleanTrace.Frame) (r s : Nat)
    (shift : UInt256) (hlt : s < r) (hd : r - s = 1)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hlower : q.lower = lowerWord)
    (hshift : shift = UInt256.ofNat (32 - s)) :
    scaledOneT q q.lower shift (inlineHoistedBoolean q) =
      hoistedT r s q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [scaledOneT_eq]
  exact scaledT_hoisted_low q r s _ shift hlt hfactor hpair hlower (by simp [hd]) hshift

theorem scaledOneT_hoisted_high (q : PairedHelperBooleanTrace.Frame) (r s : Nat)
    (shift : UInt256) (hlt : r < s) (hd : s - r = 1)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hshift : shift = UInt256.ofNat (32 - r)) :
    scaledOneT q q.upper shift (inlineHoistedBoolean q) =
      hoistedT r s q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [scaledOneT_eq]
  exact scaledT_hoisted_high q r s _ shift hlt hfactor hpair hupper (by simp [hd]) hshift

/-- Equal rotations keep the single shift. -/
theorem singleT_hoisted (q : PairedHelperBooleanTrace.Frame) (r : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord) (hpair : q.pair = pairWord)
    (hshift : q.leftShift0 = UInt256.ofNat (32 - r)) :
    singleT q (inlineHoistedBoolean q) =
      hoistedT r r q.a q.b q.c q.d q.e q.message0 q.k := by
  have hp : inlineProduct q (inlineHoistedBoolean q) =
      UInt256.mul (hoistedSum q.a q.b q.c q.d q.message0 q.k) PairedLaneWordRotate.factorWord := by
    rw [inlineProduct_eq, rawProduct, rawSum_hoisted q hpair, hfactor, umul_comm]
  rw [singleT, hp, hshift, hoistedT, PairedLaneWordRotate.wordRotate, if_pos rfl,
    PairedLaneWordRotate.wordShift]
  apply bits_injective
  simp only [hpair, bits_land, bits_add]
  ac_rfl

#print axioms scaledT_hoisted_low
#print axioms scaledT_hoisted_high
#print axioms scaledOneT_hoisted_low
#print axioms scaledOneT_hoisted_high
#print axioms singleT_hoisted

def inline32Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 2),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline32Template_length : inline32Template.length = 41 := rfl

theorem run_inline32Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline32Template {s with pc := pc, stack := inline32Entry q rho} =
      some {s with pc := pcAfter pc inline32Template, stack := inline32Output q (inlineT (inline32Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline32Template, inline32Entry, inline32Output,
    inlineT, inlineRotation, inline32Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline32Template_length
#print axioms run_inline32Template



def inline33Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 6),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline33Template_length : inline33Template.length = 41 := rfl

theorem run_inline33Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline33Template {s with pc := pc, stack := inline33Entry q rho} =
      some {s with pc := pcAfter pc inline33Template, stack := inline33Output q (inlineT (inline33Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline33Template, inline33Entry, inline33Output,
    inlineT, inlineRotation, inline33Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline33Template_length
#print axioms run_inline33Template



def inline34Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 640),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline34Template_length : inline34Template.length = 42 := rfl

theorem run_inline34Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline34Template {s with pc := pc, stack := inline34Entry q rho} =
      some {s with pc := pcAfter pc inline34Template, stack := inline34Output q (inlineT (inline34Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline34Template, inline34Entry, inline34Output,
    inlineT, inlineRotation, inline34Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline34Template_length
#print axioms run_inline34Template



def inline35Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline35Template_length : inline35Template.length = 42 := rfl

theorem run_inline35Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline35Template {s with pc := pc, stack := inline35Entry q rho} =
      some {s with pc := pcAfter pc inline35Template, stack := inline35Output q (inlineT (inline35Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline35Template, inline35Entry, inline35Output,
    inlineT, inlineRotation, inline35Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline35Template_length
#print axioms run_inline35Template



def inline36Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 6),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline36Template_length : inline36Template.length = 41 := rfl

theorem run_inline36Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline36Template {s with pc := pc, stack := inline36Entry q rho} =
      some {s with pc := pcAfter pc inline36Template, stack := inline36Output q (inlineT (inline36Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline36Template, inline36Entry, inline36Output,
    inlineT, inlineRotation, inline36Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline36Template_length
#print axioms run_inline36Template



def inline37Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline37Template_length : inline37Template.length = 41 := rfl

theorem run_inline37Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline37Template {s with pc := pc, stack := inline37Entry q rho} =
      some {s with pc := pcAfter pc inline37Template, stack := inline37Output q (inlineT (inline37Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline37Template, inline37Entry, inline37Output,
    inlineT, inlineRotation, inline37Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline37Template_length
#print axioms run_inline37Template



def inline38Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 400),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 7),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline38Template_length : inline38Template.length = 41 := rfl

theorem run_inline38Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline38Template {s with pc := pc, stack := inline38Entry q rho} =
      some {s with pc := pcAfter pc inline38Template, stack := inline38Output q (inlineT (inline38Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline38Template, inline38Entry, inline38Output,
    inlineT, inlineRotation, inline38Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline38Template_length
#print axioms run_inline38Template



def inline39Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 496),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 1),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline39Template_length : inline39Template.length = 41 := rfl

theorem run_inline39Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline39Template {s with pc := pc, stack := inline39Entry q rho} =
      some {s with pc := pcAfter pc inline39Template, stack := inline39Output q (inlineT (inline39Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline39Template, inline39Entry, inline39Output,
    inlineT, inlineRotation, inline39Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline39Template_length
#print axioms run_inline39Template



def inline40Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 560),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 2),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline40Template_length : inline40Template.length = 41 := rfl

theorem run_inline40Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline40Template {s with pc := pc, stack := inline40Entry q rho} =
      some {s with pc := pcAfter pc inline40Template, stack := inline40Output q (inlineT (inline40Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline40Template, inline40Entry, inline40Output,
    inlineT, inlineRotation, inline40Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline40Template_length
#print axioms run_inline40Template



def inline41Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline41Template_length : inline41Template.length = 42 := rfl

theorem run_inline41Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline41Template {s with pc := pc, stack := inline41Entry q rho} =
      some {s with pc := pcAfter pc inline41Template, stack := inline41Output q (inlineT (inline41Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline41Template, inline41Entry, inline41Output,
    inlineT, inlineRotation, inline41Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline41Template_length
#print axioms run_inline41Template



def inline42Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 8),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline42Template_length : inline42Template.length = 41 := rfl

theorem run_inline42Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline42Template {s with pc := pc, stack := inline42Entry q rho} =
      some {s with pc := pcAfter pc inline42Template, stack := inline42Output q (inlineT (inline42Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline42Template, inline42Entry, inline42Output,
    inlineT, inlineRotation, inline42Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline42Template_length
#print axioms run_inline42Template



def inline43Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline43Template_length : inline43Template.length = 42 := rfl

theorem run_inline43Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline43Template {s with pc := pc, stack := inline43Entry q rho} =
      some {s with pc := pcAfter pc inline43Template, stack := inline43Output q (inlineT (inline43Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline43Template, inline43Entry, inline43Output,
    inlineT, inlineRotation, inline43Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline43Template_length
#print axioms run_inline43Template



def inline44Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline44Template_length : inline44Template.length = 42 := rfl

theorem run_inline44Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline44Template {s with pc := pc, stack := inline44Entry q rho} =
      some {s with pc := pcAfter pc inline44Template, stack := inline44Output q (inlineT (inline44Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline44Template, inline44Entry, inline44Output,
    inlineT, inlineRotation, inline44Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline44Template_length
#print axioms run_inline44Template



def inline45Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline45Template_length : inline45Template.length = 42 := rfl

theorem run_inline45Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline45Template {s with pc := pc, stack := inline45Entry q rho} =
      some {s with pc := pcAfter pc inline45Template, stack := inline45Output q (inlineT (inline45Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline45Template, inline45Entry, inline45Output,
    inlineT, inlineRotation, inline45Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline45Template_length
#print axioms run_inline45Template



def inline46Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 336),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline46Template_length : inline46Template.length = 33 := rfl

theorem run_inline46Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline46Template {s with pc := pc, stack := inline46Entry q rho} =
      some {s with pc := pcAfter pc inline46Template, stack := inline46Output q (singleT (inline46Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline46Template, inline46Entry, inline46Output,
    singleT, inline46Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline46Template_length
#print axioms run_inline46Template



def inline47Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND]

theorem inline47Template_length : inline47Template.length = 33 := rfl

theorem run_inline47Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline47Template {s with pc := pc, stack := inline47Entry q rho} =
      some {s with pc := pcAfter pc inline47Template, stack := inline47Output q (singleT (inline47Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline47Template, inline47Entry, inline47Output,
    singleT, inline47Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩


#print axioms inline47Template_length
#print axioms run_inline47Template


/-- A distinct raw step. Logical K is adjusted only in group two; all raw words remain admissible. -/
def hoistedWordStep (j r t : Nat) (message k : UInt256)
    (q : PairedLaneWordRound.WordLane) : PairedLaneWordRound.WordLane :=
  if j = 2 then rawWordStep2 r t message (adjustedK k) q
  else PairedLaneWordRound.wordStep j r t message k q

theorem hoistedWordStep_of_crypto (j r t : Nat)
    (hr0 : 0 < r) (hr : r < 32) (ht0 : 0 < t) (ht : t < 32)
    (ml mr kl kr : UInt32) (left right : PairedLaneCryptoBridge.CryptoLane) :
    hoistedWordStep j r t (packed32 ml mr) (packed32 kl kr)
        (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (PairedLaneCryptoBridge.cryptoStep j r ml kl left)
        (PairedLaneCryptoBridge.cryptoStep (4 - j) t mr kr right) := by
  by_cases hj : j = 2
  · subst j
    simp only [hoistedWordStep]
    exact rawWordStep2_of_crypto r t hr0 hr ht0 ht ml mr kl kr left right
  · simp only [hoistedWordStep, if_neg hj]
    exact PairedLaneWordRound.wordStep_of_crypto j r t hr0 hr ht0 ht ml mr kl kr left right

#print axioms hoistedWordStep_of_crypto

def hoistedWordFold (group leftRotation rightRotation : Nat → Nat)
    (message constant : Nat → UInt256) :
    Nat → PairedLaneWordRound.WordLane → PairedLaneWordRound.WordLane
  | 0, q => q
  | i + 1, q =>
      hoistedWordStep (group i) (leftRotation i) (rightRotation i)
        (message i) (constant i)
        (hoistedWordFold group leftRotation rightRotation message constant i q)

theorem hoistedWordFold_crypto
    (group leftRotation rightRotation : Nat → Nat)
    (leftMessage rightMessage leftConstant rightConstant : Nat → UInt32)
    (count : Nat) (left right : PairedLaneCryptoBridge.CryptoLane)
    (hrotation : ∀ i < count,
      0 < leftRotation i ∧ leftRotation i < 32 ∧
      0 < rightRotation i ∧ rightRotation i < 32) :
    hoistedWordFold group leftRotation rightRotation
        (fun i => packed32 (leftMessage i) (rightMessage i))
        (fun i => packed32 (leftConstant i) (rightConstant i)) count
        (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold group leftRotation leftMessage leftConstant count left)
        (scalarRightFold group rightRotation rightMessage rightConstant count right) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hprev := ih (fun n hn => hrotation n (by omega))
    obtain ⟨hr0, hr, ht0, ht⟩ := hrotation i (by omega)
    exact (congrArg
      (hoistedWordStep (group i) (leftRotation i) (rightRotation i)
        (packed32 (leftMessage i) (rightMessage i))
        (packed32 (leftConstant i) (rightConstant i))) hprev).trans
      (hoistedWordStep_of_crypto (group i) (leftRotation i) (rightRotation i)
        hr0 hr ht0 ht (leftMessage i) (rightMessage i) (leftConstant i) (rightConstant i)
        (scalarLeftFold group leftRotation leftMessage leftConstant i left)
        (scalarRightFold group rightRotation rightMessage rightConstant i right))

#print axioms hoistedWordFold_crypto

theorem hoistedWordFold_add
    (group leftRotation rightRotation : Nat → Nat)
    (message constant : Nat → UInt256) (a b : Nat)
    (q : PairedLaneWordRound.WordLane) :
    hoistedWordFold group leftRotation rightRotation message constant (a + b) q =
      hoistedWordFold
        (fun i => group (a + i)) (fun i => leftRotation (a + i))
        (fun i => rightRotation (a + i)) (fun i => message (a + i))
        (fun i => constant (a + i)) b
        (hoistedWordFold group leftRotation rightRotation message constant a q) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    exact congrArg
      (hoistedWordStep (group (a + b)) (leftRotation (a + b))
        (rightRotation (a + b)) (message (a + b)) (constant (a + b))) ih

#print axioms hoistedWordFold_add

theorem hoistedWordFold_congr
    (group leftRotation rightRotation : Nat → Nat)
    (message0 constant0 message1 constant1 : Nat → UInt256)
    (count : Nat) (q : PairedLaneWordRound.WordLane)
    (hmessage : ∀ i < count, message0 i = message1 i)
    (hconstant : ∀ i < count, constant0 i = constant1 i) :
    hoistedWordFold group leftRotation rightRotation message0 constant0 count q =
      hoistedWordFold group leftRotation rightRotation message1 constant1 count q := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hprev := ih (fun j hj => hmessage j (by omega)) (fun j hj => hconstant j (by omega))
    exact (congrArg₂
      (fun m k : UInt256 => hoistedWordStep (group i) (leftRotation i) (rightRotation i)
        m k (hoistedWordFold group leftRotation rightRotation message0 constant0 i q))
      (hmessage i (by omega)) (hconstant i (by omega))).trans
        (congrArg (hoistedWordStep (group i) (leftRotation i) (rightRotation i)
          (message1 i) (constant1 i)) hprev)

#print axioms hoistedWordFold_congr

def physicalKey (j : Nat) : UInt256 :=
  if j = 2 then adjustedK (algorithmKey j) else algorithmKey j

theorem physicalKey_two :
    physicalKey 2 = UInt256.ofNat 2086284798122997420139349764661223671126594022305 := by
  decide

#print axioms physicalKey_two

def hoistedAlgorithmFold (memory : ByteArray) (start count : Nat)
    (q : PairedLaneWordRound.WordLane) : PairedLaneWordRound.WordLane :=
  hoistedWordFold
    (fun i => (start + i) / 16)
    (fun i => Crypto.Ripemd160.s[start + i]!)
    (fun i => Crypto.Ripemd160.sP[start + i]!)
    (fun i => algorithmMessage memory (start + i))
    (fun i => algorithmKey ((start + i) / 16)) count q

def hoistedAlgorithmStep (memory : ByteArray) (i : Nat)
    (q : PairedLaneWordRound.WordLane) : PairedLaneWordRound.WordLane :=
  hoistedWordStep (i / 16) (Crypto.Ripemd160.s[i]!)
    (Crypto.Ripemd160.sP[i]!) (algorithmMessage memory i) (algorithmKey (i / 16)) q

theorem hoistedAlgorithmFold_succ (memory : ByteArray) (start count : Nat)
    (q : PairedLaneWordRound.WordLane) :
    hoistedAlgorithmFold memory start (count + 1) q =
      hoistedAlgorithmStep memory (start + count) (hoistedAlgorithmFold memory start count q) := rfl

#print axioms hoistedAlgorithmFold_succ

theorem hoistedAlgorithmFold_crypto (memory : ByteArray) (words : Nat → UInt32)
    (count : Nat) (hcount : count ≤ 80)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hmessage : ∀ i < count, algorithmMessage memory i =
      packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)) :
    hoistedAlgorithmFold memory 0 count (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
          (fun i => words Crypto.Ripemd160.r[i]!) (fun i => Crypto.Ripemd160.K[i / 16]!) count left)
        (scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
          (fun i => words Crypto.Ripemd160.rP[i]!) (fun i => Crypto.Ripemd160.KP[i / 16]!) count right) := by
  simp only [hoistedAlgorithmFold, Nat.zero_add]
  have hconstant (i : Nat) (hi : i < count) :
      algorithmKey (i / 16) =
        packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]! :=
    algorithmKey_packed ⟨i / 16, by omega⟩
  have hrotation (i : Nat) (hi : i < count) :
      0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 ∧
      0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 :=
    algorithmRotation_bounds ⟨i, by omega⟩
  have h0 := hoistedWordFold_congr
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (algorithmMessage memory) (fun i => algorithmKey (i / 16))
    (fun i => packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
    (fun i => packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!)
    count (PairedLaneWordRound.packCrypto left right) hmessage hconstant
  exact h0.trans (hoistedWordFold_crypto
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (fun i => words Crypto.Ripemd160.r[i]!) (fun i => words Crypto.Ripemd160.rP[i]!)
    (fun i => Crypto.Ripemd160.K[i / 16]!) (fun i => Crypto.Ripemd160.KP[i / 16]!)
    count left right hrotation)




#print axioms hoistedAlgorithmFold_crypto

def call16Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1773),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 560),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 400),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5070),
   .op .JUMP]

def call16Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23, message1 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 320), leftShift1 := UInt256.ofNat 26, rightShift1 := UInt256.ofNat 19, ret := UInt256.ofNat 1773}

def call16Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem call16Template_length : call16Template.length = 24 := rfl

theorem run_call16Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5070 = true) :
    runInstrSeq call16Template {s with pc := pc, stack := call16Entry q rho} =
      some {s with pc := UInt256.ofNat 5070, stack := entryStack (call16Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call16Template, call16Entry, call16Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

def call28Template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 2351),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 640),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 496),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 336),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5070),
   .op .JUMP]

def call28Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 26, message1 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 640), leftShift1 := UInt256.ofNat 25, rightShift1 := UInt256.ofNat 17, ret := UInt256.ofNat 2351}

def call28Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem call28Template_length : call28Template.length = 21 := rfl

theorem run_call28Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5070 = true) :
    runInstrSeq call28Template {s with pc := pc, stack := call28Entry q rho} =
      some {s with pc := UInt256.ofNat 5070, stack := entryStack (call28Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call28Template, call28Entry, call28Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

#print axioms call16Template_length
#print axioms run_call16Template
#print axioms call28Template_length
#print axioms run_call28Template

def group32Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push ⟨21, by decide⟩ (UInt256.ofNat 2086284798122997420139349764661223671126594022305)]

def group32Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def group32Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 2086284798122997420139349764661223671126594022305, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem run_group32Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group32Template {s with pc := pc, stack := group32Entry q rho} =
      some {s with pc := pcAfter pc group32Template, stack := group32Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group32Template, group32Entry, group32Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl



#print axioms run_group32Template

def CoreJumpValid (s : State) : Prop :=
  ∀ dest ∈ [5057, 1760, 2338],
    Decode.isValidJumpDest s.executionEnv.code dest = true

structure CoreBlock (start finish : Nat) (input output : List CoreReg) where
  code : List Instr
  eval : ByteArray → CoreFrame → CoreFrame
  run : ∀ (s : State) (f : CoreFrame) (rho : List UInt256),
    rho.length ≤ 1002 → s.halt = .Running → 23 ≤ s.activeWords.toNat →
    CoreJumpValid s →
    runInstrSeq code {s with pc := UInt256.ofNat start, stack := coreStack input f rho} =
      some {s with pc := UInt256.ofNat finish, stack := coreStack output (eval s.memory f) rho}

/-- Adjacent physical frame and PC interfaces are checked by the type. -/
inductive CoreChain : Nat → List CoreReg → Nat → List CoreReg → Type where
  | nil (pc : Nat) (shape : List CoreReg) : CoreChain pc shape pc shape
  | cons {a b c : Nat} {xs ys zs : List CoreReg}
      (block : CoreBlock a b xs ys) (tail : CoreChain b ys c zs) :
      CoreChain a xs c zs

def CoreChain.code {a b : Nat} {xs ys : List CoreReg} :
    CoreChain a xs b ys → List Instr
  | .nil _ _ => []
  | .cons block tail => block.code ++ tail.code

def CoreChain.eval {a b : Nat} {xs ys : List CoreReg} :
    CoreChain a xs b ys → ByteArray → CoreFrame → CoreFrame
  | .nil _ _, _, f => f
  | .cons block tail, memory, f => tail.eval memory (block.eval memory f)

theorem CoreChain.run {a b : Nat} {xs ys : List CoreReg}
    (chain : CoreChain a xs b ys) (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s) :
    runInstrSeq chain.code {s with pc := UInt256.ofNat a, stack := coreStack xs f rho} =
      some {s with pc := UInt256.ofNat b, stack := coreStack ys (chain.eval s.memory f) rho} := by
  induction chain generalizing f with
  | nil => rfl
  | cons block tail ih =>
    have h0 := block.run s f rho hstack hrun hactive hvalid
    have h1 := ih (block.eval s.memory f)
    exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1





#print axioms CoreChain.run



abbrev inline20Template : List Instr := PairedCall20Inline.inline20Template

abbrev inline20Frame := PairedCall20Inline.inline20Frame

abbrev inline21Template : List Instr := PairedCall20Inline.inline21Template

abbrev inline21Frame := PairedCall20Inline.inline21Frame

abbrev inline26Template : List Instr := PairedCall26Inline.inline26Template

abbrev inline26Frame := PairedCall26Inline.inline26Frame

abbrev inline27Template : List Instr := PairedCall26Inline.inline27Template

abbrev inline27Frame := PairedCall26Inline.inline27Frame

inductive CoreEvalCert : {a b : Nat} → {xs ys : List CoreReg} →
    CoreChain a xs b ys → ByteArray → CoreFrame → CoreFrame → Prop where
  | nil {pc : Nat} {shape : List CoreReg} {memory : ByteArray} {f : CoreFrame} :
      CoreEvalCert (.nil pc shape) memory f f
  | cons {a b c : Nat} {xs ys zs : List CoreReg}
      (block : CoreBlock a b xs ys) (tail : CoreChain b ys c zs)
      {memory : ByteArray} {first middle result : CoreFrame}
      (hstep : block.eval memory first = middle)
      (hrest : CoreEvalCert tail memory middle result) :
      CoreEvalCert (.cons block tail) memory first result

theorem CoreEvalCert.sound {a b : Nat} {xs ys : List CoreReg}
    {chain : CoreChain a xs b ys} {memory : ByteArray}
    {first result : CoreFrame} (h : CoreEvalCert chain memory first result) :
    chain.eval memory first = result := by
  induction h with
  | nil => rfl
  | cons block tail hstep _ ih =>
    exact (congrArg (tail.eval _) hstep).trans ih


#print axioms CoreEvalCert.sound
open Challenge.EvmProof StackRoundTemplate

theorem fullTemplate_terminal_advances :
    ∀ instruction ∈ fullTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms fullTemplate_terminal_advances

theorem call16Template_terminal_advances :
    ∀ instruction ∈ call16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

structure CoreGasBlock {a b : Nat} {xs ys : List CoreReg}
    (block : CoreBlock a b xs ys) (artifact : ProgramArtifact) (fork : Fork) where
  run : ∀ (s : State) (f : CoreFrame) (rho : List UInt256),
    rho.length ≤ 1002 → s.halt = .Running → 23 ≤ s.activeWords.toNat →
    CoreJumpValid s → s.executionEnv.code = artifact.code → s.fork = fork →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false →
    GasSteps {s with pc := UInt256.ofNat a, stack := coreStack xs f rho}
      {s with pc := UInt256.ofNat b, stack := coreStack ys (block.eval s.memory f) rho}

def CoreGasBlock.of_site {a b : Nat} {xs ys : List CoreReg}
    (block : CoreBlock a b xs ys) {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork block.code)
    (hpc : site.startPC = UInt256.ofNat a)
    (hform : ∀ instruction ∈ block.code.dropLast, DenseScheduleLift.Advances instruction) :
    CoreGasBlock block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    exact gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm hform
      (block.run s f rho hstack hrun hactive hvalid)

inductive CoreGasChain (artifact : ProgramArtifact) (fork : Fork) :
    {a b : Nat} → {xs ys : List CoreReg} → CoreChain a xs b ys → Type where
  | nil (pc : Nat) (shape : List CoreReg) :
      CoreGasChain artifact fork (.nil pc shape)
  | cons {a b c : Nat} {xs ys zs : List CoreReg}
      (block : CoreBlock a b xs ys) (tail : CoreChain b ys c zs)
      (first : CoreGasBlock block artifact fork)
      (rest : CoreGasChain artifact fork tail) :
      CoreGasChain artifact fork (.cons block tail)

def CoreGasChain.run {artifact : ProgramArtifact} {fork : Fork}
    {a b : Nat} {xs ys : List CoreReg} {chain : CoreChain a xs b ys}
    (steps : CoreGasChain artifact fork chain) (s : State) (f : CoreFrame)
    (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat a, stack := coreStack xs f rho}
      {s with pc := UInt256.ofNat b, stack := coreStack ys (chain.eval s.memory f) rho} :=
  match steps with
  | .nil _ _ => GasSteps.refl _
  | .cons block _ first rest =>
      (first.run s f rho hstack hrun hactive hvalid hcode hfork hnp).trans
        (CoreGasChain.run rest s (block.eval s.memory f) rho
          hstack hrun hactive hvalid hcode hfork hnp)

theorem group0Template_terminal_advances :
    ∀ instruction ∈ group0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline0Template_terminal_advances :
    ∀ instruction ∈ inline0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline0Template_terminal_advances

theorem inline1Template_terminal_advances :
    ∀ instruction ∈ inline1Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline2Template_terminal_advances :
    ∀ instruction ∈ inline2Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline3Template_terminal_advances :
    ∀ instruction ∈ inline3Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline4Template_terminal_advances :
    ∀ instruction ∈ inline4Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline5Template_terminal_advances :
    ∀ instruction ∈ inline5Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline6Template_terminal_advances :
    ∀ instruction ∈ inline6Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline7Template_terminal_advances :
    ∀ instruction ∈ inline7Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline8Template_terminal_advances :
    ∀ instruction ∈ inline8Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline9Template_terminal_advances :
    ∀ instruction ∈ inline9Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline10Template_terminal_advances :
    ∀ instruction ∈ inline10Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline11Template_terminal_advances :
    ∀ instruction ∈ inline11Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline12Template_terminal_advances :
    ∀ instruction ∈ inline12Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline13Template_terminal_advances :
    ∀ instruction ∈ inline13Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline14Template_terminal_advances :
    ∀ instruction ∈ inline14Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline15Template_terminal_advances :
    ∀ instruction ∈ inline15Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem group16Template_terminal_advances :
    ∀ instruction ∈ group16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem return18Template_terminal_advances :
    ∀ instruction ∈ return18Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline18Template_terminal_advances :
    ∀ instruction ∈ inline18Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline19Template_terminal_advances :
    ∀ instruction ∈ inline19Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline20Template_terminal_advances :
    ∀ instruction ∈ inline20Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall20Inline.inline20Template_terminal_advances

#print axioms inline20Template_terminal_advances

theorem inline21Template_terminal_advances :
    ∀ instruction ∈ inline21Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall20Inline.inline21Template_terminal_advances

#print axioms inline21Template_terminal_advances

theorem inline22Template_terminal_advances :
    ∀ instruction ∈ inline22Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall22Inline.inline22Template_terminal_advances

#print axioms inline22Template_terminal_advances

theorem inline23Template_terminal_advances :
    ∀ instruction ∈ inline23Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall22Inline.inline23Template_terminal_advances

#print axioms inline23Template_terminal_advances

theorem inline24Template_terminal_advances :
    ∀ instruction ∈ inline24Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline25Template_terminal_advances :
    ∀ instruction ∈ inline25Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline26Template_terminal_advances :
    ∀ instruction ∈ inline26Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall26Inline.inline26Template_terminal_advances

#print axioms inline26Template_terminal_advances

theorem inline27Template_terminal_advances :
    ∀ instruction ∈ inline27Template.dropLast, DenseScheduleLift.Advances instruction :=
  PairedCall26Inline.inline27Template_terminal_advances

#print axioms inline27Template_terminal_advances

theorem call28Template_terminal_advances :
    ∀ instruction ∈ call28Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem return30Template_terminal_advances :
    ∀ instruction ∈ return30Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline30Template_terminal_advances :
    ∀ instruction ∈ inline30Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline31Template_terminal_advances :
    ∀ instruction ∈ inline31Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem group32Template_terminal_advances :
    ∀ instruction ∈ group32Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline32Template_terminal_advances :
    ∀ instruction ∈ inline32Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline33Template_terminal_advances :
    ∀ instruction ∈ inline33Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline34Template_terminal_advances :
    ∀ instruction ∈ inline34Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline35Template_terminal_advances :
    ∀ instruction ∈ inline35Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline36Template_terminal_advances :
    ∀ instruction ∈ inline36Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline37Template_terminal_advances :
    ∀ instruction ∈ inline37Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline38Template_terminal_advances :
    ∀ instruction ∈ inline38Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline39Template_terminal_advances :
    ∀ instruction ∈ inline39Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline40Template_terminal_advances :
    ∀ instruction ∈ inline40Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline41Template_terminal_advances :
    ∀ instruction ∈ inline41Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline42Template_terminal_advances :
    ∀ instruction ∈ inline42Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline43Template_terminal_advances :
    ∀ instruction ∈ inline43Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline44Template_terminal_advances :
    ∀ instruction ∈ inline44Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline45Template_terminal_advances :
    ∀ instruction ∈ inline45Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline46Template_terminal_advances :
    ∀ instruction ∈ inline46Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline47Template_terminal_advances :
    ∀ instruction ∈ inline47Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem group48Template_terminal_advances :
    ∀ instruction ∈ group48Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline48Template_terminal_advances :
    ∀ instruction ∈ inline48Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline49Template_terminal_advances :
    ∀ instruction ∈ inline49Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline50Template_terminal_advances :
    ∀ instruction ∈ inline50Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline51Template_terminal_advances :
    ∀ instruction ∈ inline51Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline52Template_terminal_advances :
    ∀ instruction ∈ inline52Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline53Template_terminal_advances :
    ∀ instruction ∈ inline53Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline54Template_terminal_advances :
    ∀ instruction ∈ inline54Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline55Template_terminal_advances :
    ∀ instruction ∈ inline55Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline56Template_terminal_advances :
    ∀ instruction ∈ inline56Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline57Template_terminal_advances :
    ∀ instruction ∈ inline57Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline58Template_terminal_advances :
    ∀ instruction ∈ inline58Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline59Template_terminal_advances :
    ∀ instruction ∈ inline59Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline60Template_terminal_advances :
    ∀ instruction ∈ inline60Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline61Template_terminal_advances :
    ∀ instruction ∈ inline61Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline62Template_terminal_advances :
    ∀ instruction ∈ inline62Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline63Template_terminal_advances :
    ∀ instruction ∈ inline63Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem group64Template_terminal_advances :
    ∀ instruction ∈ group64Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline64Template_terminal_advances :
    ∀ instruction ∈ inline64Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline65Template_terminal_advances :
    ∀ instruction ∈ inline65Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline66Template_terminal_advances :
    ∀ instruction ∈ inline66Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline67Template_terminal_advances :
    ∀ instruction ∈ inline67Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline68Template_terminal_advances :
    ∀ instruction ∈ inline68Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline69Template_terminal_advances :
    ∀ instruction ∈ inline69Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline70Template_terminal_advances :
    ∀ instruction ∈ inline70Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline71Template_terminal_advances :
    ∀ instruction ∈ inline71Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline72Template_terminal_advances :
    ∀ instruction ∈ inline72Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline73Template_terminal_advances :
    ∀ instruction ∈ inline73Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline74Template_terminal_advances :
    ∀ instruction ∈ inline74Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline75Template_terminal_advances :
    ∀ instruction ∈ inline75Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline76Template_terminal_advances :
    ∀ instruction ∈ inline76Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline77Template_terminal_advances :
    ∀ instruction ∈ inline77Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline78Template_terminal_advances :
    ∀ instruction ∈ inline78Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline79Template_terminal_advances :
    ∀ instruction ∈ inline79Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem coreExitTemplate_terminal_advances :
    ∀ instruction ∈ coreExitTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide


/-- Each physical window has its own exact bytecode binding; calls share one helper. -/
structure WholeCoreSites (artifact : ProgramArtifact) (fork : Fork) where
  group0 : {site : GenericRoundSite artifact fork group0Template // site.startPC = UInt256.ofNat 832}
  inline0 : {site : GenericRoundSite artifact fork inline0Template // site.startPC = UInt256.ofNat 853}
  inline1 : {site : GenericRoundSite artifact fork inline1Template // site.startPC = UInt256.ofNat 905}
  inline2 : {site : GenericRoundSite artifact fork inline2Template // site.startPC = UInt256.ofNat 957}
  inline3 : {site : GenericRoundSite artifact fork inline3Template // site.startPC = UInt256.ofNat 1010}
  inline4 : {site : GenericRoundSite artifact fork inline4Template // site.startPC = UInt256.ofNat 1062}
  inline5 : {site : GenericRoundSite artifact fork inline5Template // site.startPC = UInt256.ofNat 1116}
  inline6 : {site : GenericRoundSite artifact fork inline6Template // site.startPC = UInt256.ofNat 1170}
  inline7 : {site : GenericRoundSite artifact fork inline7Template // site.startPC = UInt256.ofNat 1224}
  inline8 : {site : GenericRoundSite artifact fork inline8Template // site.startPC = UInt256.ofNat 1277}
  inline9 : {site : GenericRoundSite artifact fork inline9Template // site.startPC = UInt256.ofNat 1330}
  inline10 : {site : GenericRoundSite artifact fork inline10Template // site.startPC = UInt256.ofNat 1383}
  inline11 : {site : GenericRoundSite artifact fork inline11Template // site.startPC = UInt256.ofNat 1436}
  inline12 : {site : GenericRoundSite artifact fork inline12Template // site.startPC = UInt256.ofNat 1489}
  inline13 : {site : GenericRoundSite artifact fork inline13Template // site.startPC = UInt256.ofNat 1542}
  inline14 : {site : GenericRoundSite artifact fork inline14Template // site.startPC = UInt256.ofNat 1596}
  inline15 : {site : GenericRoundSite artifact fork inline15Template // site.startPC = UInt256.ofNat 1657}
  group16 : {site : GenericRoundSite artifact fork group16Template // site.startPC = UInt256.ofNat 1710}
  call16 : {site : GenericRoundSite artifact fork call16Template // site.startPC = UInt256.ofNat 1733}
  return18 : {site : GenericRoundSite artifact fork return18Template // site.startPC = UInt256.ofNat 1773}
  inline18 : {site : GenericRoundSite artifact fork inline18Template // site.startPC = UInt256.ofNat 1774}
  inline19 : {site : GenericRoundSite artifact fork inline19Template // site.startPC = UInt256.ofNat 1829}
  inline20 : {site : GenericRoundSite artifact fork inline20Template // site.startPC = UInt256.ofNat 1883}
  inline21 : {site : GenericRoundSite artifact fork inline21Template // site.startPC = UInt256.ofNat 1938}
  inline22 : {site : GenericRoundSite artifact fork inline22Template // site.startPC = UInt256.ofNat 1993}
  inline23 : {site : GenericRoundSite artifact fork inline23Template // site.startPC = UInt256.ofNat 2049}
  inline24 : {site : GenericRoundSite artifact fork inline24Template // site.startPC = UInt256.ofNat 2104}
  inline25 : {site : GenericRoundSite artifact fork inline25Template // site.startPC = UInt256.ofNat 2150}
  inline26 : {site : GenericRoundSite artifact fork inline26Template // site.startPC = UInt256.ofNat 2204}
  inline27 : {site : GenericRoundSite artifact fork inline27Template // site.startPC = UInt256.ofNat 2259}
  call28 : {site : GenericRoundSite artifact fork call28Template // site.startPC = UInt256.ofNat 2314}
  return30 : {site : GenericRoundSite artifact fork return30Template // site.startPC = UInt256.ofNat 2351}
  inline30 : {site : GenericRoundSite artifact fork inline30Template // site.startPC = UInt256.ofNat 2352}
  inline31 : {site : GenericRoundSite artifact fork inline31Template // site.startPC = UInt256.ofNat 2396}
  group32 : {site : GenericRoundSite artifact fork group32Template // site.startPC = UInt256.ofNat 2451}
  inline32 : {site : GenericRoundSite artifact fork inline32Template // site.startPC = UInt256.ofNat 2475}
  inline33 : {site : GenericRoundSite artifact fork inline33Template // site.startPC = UInt256.ofNat 2523}
  inline34 : {site : GenericRoundSite artifact fork inline34Template // site.startPC = UInt256.ofNat 2571}
  inline35 : {site : GenericRoundSite artifact fork inline35Template // site.startPC = UInt256.ofNat 2619}
  inline36 : {site : GenericRoundSite artifact fork inline36Template // site.startPC = UInt256.ofNat 2668}
  inline37 : {site : GenericRoundSite artifact fork inline37Template // site.startPC = UInt256.ofNat 2716}
  inline38 : {site : GenericRoundSite artifact fork inline38Template // site.startPC = UInt256.ofNat 2764}
  inline39 : {site : GenericRoundSite artifact fork inline39Template // site.startPC = UInt256.ofNat 2812}
  inline40 : {site : GenericRoundSite artifact fork inline40Template // site.startPC = UInt256.ofNat 2859}
  inline41 : {site : GenericRoundSite artifact fork inline41Template // site.startPC = UInt256.ofNat 2907}
  inline42 : {site : GenericRoundSite artifact fork inline42Template // site.startPC = UInt256.ofNat 2956}
  inline43 : {site : GenericRoundSite artifact fork inline43Template // site.startPC = UInt256.ofNat 3003}
  inline44 : {site : GenericRoundSite artifact fork inline44Template // site.startPC = UInt256.ofNat 3052}
  inline45 : {site : GenericRoundSite artifact fork inline45Template // site.startPC = UInt256.ofNat 3101}
  inline46 : {site : GenericRoundSite artifact fork inline46Template // site.startPC = UInt256.ofNat 3149}
  inline47 : {site : GenericRoundSite artifact fork inline47Template // site.startPC = UInt256.ofNat 3188}
  group48 : {site : GenericRoundSite artifact fork group48Template // site.startPC = UInt256.ofNat 3227}
  inline48 : {site : GenericRoundSite artifact fork inline48Template // site.startPC = UInt256.ofNat 3250}
  inline49 : {site : GenericRoundSite artifact fork inline49Template // site.startPC = UInt256.ofNat 3305}
  inline50 : {site : GenericRoundSite artifact fork inline50Template // site.startPC = UInt256.ofNat 3360}
  inline51 : {site : GenericRoundSite artifact fork inline51Template // site.startPC = UInt256.ofNat 3415}
  inline52 : {site : GenericRoundSite artifact fork inline52Template // site.startPC = UInt256.ofNat 3469}
  inline53 : {site : GenericRoundSite artifact fork inline53Template // site.startPC = UInt256.ofNat 3514}
  inline54 : {site : GenericRoundSite artifact fork inline54Template // site.startPC = UInt256.ofNat 3569}
  inline55 : {site : GenericRoundSite artifact fork inline55Template // site.startPC = UInt256.ofNat 3624}
  inline56 : {site : GenericRoundSite artifact fork inline56Template // site.startPC = UInt256.ofNat 3679}
  inline57 : {site : GenericRoundSite artifact fork inline57Template // site.startPC = UInt256.ofNat 3734}
  inline58 : {site : GenericRoundSite artifact fork inline58Template // site.startPC = UInt256.ofNat 3789}
  inline59 : {site : GenericRoundSite artifact fork inline59Template // site.startPC = UInt256.ofNat 3845}
  inline60 : {site : GenericRoundSite artifact fork inline60Template // site.startPC = UInt256.ofNat 3901}
  inline61 : {site : GenericRoundSite artifact fork inline61Template // site.startPC = UInt256.ofNat 3957}
  inline62 : {site : GenericRoundSite artifact fork inline62Template // site.startPC = UInt256.ofNat 4012}
  inline63 : {site : GenericRoundSite artifact fork inline63Template // site.startPC = UInt256.ofNat 4068}
  group64 : {site : GenericRoundSite artifact fork group64Template // site.startPC = UInt256.ofNat 4123}
  inline64 : {site : GenericRoundSite artifact fork inline64Template // site.startPC = UInt256.ofNat 4130}
  inline65 : {site : GenericRoundSite artifact fork inline65Template // site.startPC = UInt256.ofNat 4183}
  inline66 : {site : GenericRoundSite artifact fork inline66Template // site.startPC = UInt256.ofNat 4235}
  inline67 : {site : GenericRoundSite artifact fork inline67Template // site.startPC = UInt256.ofNat 4289}
  inline68 : {site : GenericRoundSite artifact fork inline68Template // site.startPC = UInt256.ofNat 4342}
  inline69 : {site : GenericRoundSite artifact fork inline69Template // site.startPC = UInt256.ofNat 4395}
  inline70 : {site : GenericRoundSite artifact fork inline70Template // site.startPC = UInt256.ofNat 4448}
  inline71 : {site : GenericRoundSite artifact fork inline71Template // site.startPC = UInt256.ofNat 4502}
  inline72 : {site : GenericRoundSite artifact fork inline72Template // site.startPC = UInt256.ofNat 4555}
  inline73 : {site : GenericRoundSite artifact fork inline73Template // site.startPC = UInt256.ofNat 4609}
  inline74 : {site : GenericRoundSite artifact fork inline74Template // site.startPC = UInt256.ofNat 4662}
  inline75 : {site : GenericRoundSite artifact fork inline75Template // site.startPC = UInt256.ofNat 4715}
  inline76 : {site : GenericRoundSite artifact fork inline76Template // site.startPC = UInt256.ofNat 4768}
  inline77 : {site : GenericRoundSite artifact fork inline77Template // site.startPC = UInt256.ofNat 4821}
  inline78 : {site : GenericRoundSite artifact fork inline78Template // site.startPC = UInt256.ofNat 4875}
  inline79 : {site : GenericRoundSite artifact fork inline79Template // site.startPC = UInt256.ofNat 4929}
  coreExit : {site : GenericRoundSite artifact fork coreExitTemplate // site.startPC = UInt256.ofNat 4983}
  helper : {site : GenericRoundSite artifact fork fullTemplate // site.startPC = UInt256.ofNat 5070}

#print axioms call16Template_terminal_advances
#print axioms CoreGasBlock.of_site
#print axioms CoreGasChain.run
#print axioms group0Template_terminal_advances
#print axioms inline1Template_terminal_advances
#print axioms inline2Template_terminal_advances
#print axioms inline3Template_terminal_advances
#print axioms inline4Template_terminal_advances
#print axioms inline5Template_terminal_advances
#print axioms inline6Template_terminal_advances
#print axioms inline7Template_terminal_advances
#print axioms inline8Template_terminal_advances
#print axioms inline9Template_terminal_advances
#print axioms inline10Template_terminal_advances
#print axioms inline11Template_terminal_advances
#print axioms inline12Template_terminal_advances
#print axioms inline13Template_terminal_advances
#print axioms inline14Template_terminal_advances
#print axioms inline15Template_terminal_advances
#print axioms group16Template_terminal_advances
#print axioms return18Template_terminal_advances
#print axioms inline18Template_terminal_advances
#print axioms inline19Template_terminal_advances
#print axioms inline24Template_terminal_advances
#print axioms inline25Template_terminal_advances
#print axioms call28Template_terminal_advances
#print axioms return30Template_terminal_advances
#print axioms inline30Template_terminal_advances
#print axioms inline31Template_terminal_advances
#print axioms group32Template_terminal_advances
#print axioms inline32Template_terminal_advances
#print axioms inline33Template_terminal_advances
#print axioms inline34Template_terminal_advances
#print axioms inline35Template_terminal_advances
#print axioms inline36Template_terminal_advances
#print axioms inline37Template_terminal_advances
#print axioms inline38Template_terminal_advances
#print axioms inline39Template_terminal_advances
#print axioms inline40Template_terminal_advances
#print axioms inline41Template_terminal_advances
#print axioms inline42Template_terminal_advances
#print axioms inline43Template_terminal_advances
#print axioms inline44Template_terminal_advances
#print axioms inline45Template_terminal_advances
#print axioms inline46Template_terminal_advances
#print axioms inline47Template_terminal_advances
#print axioms group48Template_terminal_advances
#print axioms inline48Template_terminal_advances
#print axioms inline49Template_terminal_advances
#print axioms inline50Template_terminal_advances
#print axioms inline51Template_terminal_advances
#print axioms inline52Template_terminal_advances
#print axioms inline53Template_terminal_advances
#print axioms inline54Template_terminal_advances
#print axioms inline55Template_terminal_advances
#print axioms inline56Template_terminal_advances
#print axioms inline57Template_terminal_advances
#print axioms inline58Template_terminal_advances
#print axioms inline59Template_terminal_advances
#print axioms inline60Template_terminal_advances
#print axioms inline61Template_terminal_advances
#print axioms inline62Template_terminal_advances
#print axioms inline63Template_terminal_advances
#print axioms group64Template_terminal_advances
#print axioms inline64Template_terminal_advances
#print axioms inline65Template_terminal_advances
#print axioms inline66Template_terminal_advances
#print axioms inline67Template_terminal_advances
#print axioms inline68Template_terminal_advances
#print axioms inline69Template_terminal_advances
#print axioms inline70Template_terminal_advances
#print axioms inline71Template_terminal_advances
#print axioms inline72Template_terminal_advances
#print axioms inline73Template_terminal_advances
#print axioms inline74Template_terminal_advances
#print axioms inline75Template_terminal_advances
#print axioms inline76Template_terminal_advances
#print axioms inline77Template_terminal_advances
#print axioms inline78Template_terminal_advances
#print axioms inline79Template_terminal_advances
#print axioms coreExitTemplate_terminal_advances
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace
