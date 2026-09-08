import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSequentialShift

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall26Inline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace

def oneRaw (q : PairedHelperBooleanTrace.Frame) : UInt256 :=
  UInt256.lor (UInt256.land q.c q.b)
    (UInt256.xor q.d (UInt256.land (UInt256.lor q.d q.c) (UInt256.xor q.upper q.b)))


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


def inline26Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 20}

def inline26Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline26Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline26WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.upper, state.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline26Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

theorem inline26Template_length : inline26Template.length = 48 := rfl

#print axioms inline26Template_length

theorem run_inline26Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline26Template {s with pc := pc, stack := inline26Entry q rho} =
      some {s with pc := pcAfter pc inline26Template, stack := inline26Output q (inlineT (inline26Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline26Template, inline26Entry, inline26Output,
    inlineT, inlineRotation, inline26Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline26Template_raw

theorem run_inline26Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline26Template {s with pc := pc, stack := inline26Entry q rho} =
      some {s with pc := pcAfter pc inline26Template, stack := inline26Output q (inlineT (inline26Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline26Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline26Template

theorem run_inline26Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline26Template {s with pc := pc, stack := inline26Entry q rho} =
      some {s with pc := pcAfter pc inline26Template, stack := inline26WordStack q (PairedLaneWordRound.wordStep 1 15 12 (inline26Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline26Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 15 12 q.a q.b q.c q.d q.e
        (inline26Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline26Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline26Frame s.memory q) 1 15 12 hfactor hpair hupper rfl rfl))
  have hout : inline26Output q (inlineT (inline26Frame s.memory q) (rawBoolean q)) rho =
      inline26WordStack q (PairedLaneWordRound.wordStep 1 15 12
        (inline26Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline26Output, inline26WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline26Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline26Template, stack := vs}) hout)

#print axioms run_inline26Template_word

theorem inline26Template_terminal_advances :
    ∀ instruction ∈ inline26Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline26Template_terminal_advances

def inline27Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 25}

def inline27Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline27Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

def inline27WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.upper, state.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline27Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 2),
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

theorem inline27Template_length : inline27Template.length = 48 := rfl

#print axioms inline27Template_length

theorem run_inline27Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline27Template {s with pc := pc, stack := inline27Entry q rho} =
      some {s with pc := pcAfter pc inline27Template, stack := inline27Output q (inlineT (inline27Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline27Template, inline27Entry, inline27Output,
    inlineT, inlineRotation, inline27Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline27Template_raw

theorem run_inline27Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline27Template {s with pc := pc, stack := inline27Entry q rho} =
      some {s with pc := pcAfter pc inline27Template, stack := inline27Output q (inlineT (inline27Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline27Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline27Template

theorem run_inline27Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline27Template {s with pc := pc, stack := inline27Entry q rho} =
      some {s with pc := pcAfter pc inline27Template, stack := inline27WordStack q (PairedLaneWordRound.wordStep 1 9 7 (inline27Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline27Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 9 7 q.a q.b q.c q.d q.e
        (inline27Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline27Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline27Frame s.memory q) 1 9 7 hfactor hpair hupper rfl rfl))
  have hout : inline27Output q (inlineT (inline27Frame s.memory q) (rawBoolean q)) rho =
      inline27WordStack q (PairedLaneWordRound.wordStep 1 9 7
        (inline27Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline27Output, inline27WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline27Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline27Template, stack := vs}) hout)

#print axioms run_inline27Template_word

theorem inline27Template_terminal_advances :
    ∀ instruction ∈ inline27Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline27Template_terminal_advances


def inline28Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 26}

def inline28Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline28Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline28WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.upper, state.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline28Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 256),
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 5),
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

theorem inline28Template_length : inline28Template.length = 48 := rfl

#print axioms inline28Template_length

theorem run_inline28Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline28Template {s with pc := pc, stack := inline28Entry q rho} =
      some {s with pc := pcAfter pc inline28Template, stack := inline28Output q (inlineT (inline28Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline28Template, inline28Entry, inline28Output,
    inlineT, inlineRotation, inline28Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline28Template_raw

theorem run_inline28Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline28Template {s with pc := pc, stack := inline28Entry q rho} =
      some {s with pc := pcAfter pc inline28Template, stack := inline28Output q (inlineT (inline28Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline28Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline28Template

theorem run_inline28Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline28Template {s with pc := pc, stack := inline28Entry q rho} =
      some {s with pc := pcAfter pc inline28Template, stack := inline28WordStack q (PairedLaneWordRound.wordStep 1 11 6 (inline28Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline28Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 11 6 q.a q.b q.c q.d q.e
        (inline28Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline28Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline28Frame s.memory q) 1 11 6 hfactor hpair hupper rfl rfl))
  have hout : inline28Output q (inlineT (inline28Frame s.memory q) (rawBoolean q)) rho =
      inline28WordStack q (PairedLaneWordRound.wordStep 1 11 6
        (inline28Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline28Output, inline28WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline28Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline28Template, stack := vs}) hout)

#print axioms run_inline28Template_word

theorem inline28Template_terminal_advances :
    ∀ instruction ∈ inline28Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline28Template_terminal_advances

def inline29Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 17}

def inline29Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline29Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

def inline29WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.upper, state.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline29Template : List Instr :=
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

theorem inline29Template_length : inline29Template.length = 49 := rfl

#print axioms inline29Template_length

theorem run_inline29Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline29Template {s with pc := pc, stack := inline29Entry q rho} =
      some {s with pc := pcAfter pc inline29Template, stack := inline29Output q (inlineT (inline29Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline29Template, inline29Entry, inline29Output,
    inlineT, inlineRotation, inline29Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline29Template_raw

theorem run_inline29Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline29Template {s with pc := pc, stack := inline29Entry q rho} =
      some {s with pc := pcAfter pc inline29Template, stack := inline29Output q (inlineT (inline29Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline29Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline29Template

theorem run_inline29Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline29Template {s with pc := pc, stack := inline29Entry q rho} =
      some {s with pc := pcAfter pc inline29Template, stack := inline29WordStack q (PairedLaneWordRound.wordStep 1 7 15 (inline29Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline29Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 15 q.a q.b q.c q.d q.e
        (inline29Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline29Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline29Frame s.memory q) 1 7 15 hfactor hpair hupper rfl rfl))
  have hout : inline29Output q (inlineT (inline29Frame s.memory q) (rawBoolean q)) rho =
      inline29WordStack q (PairedLaneWordRound.wordStep 1 7 15
        (inline29Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline29Output, inline29WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline29Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline29Template, stack := vs}) hout)

#print axioms run_inline29Template_word

theorem inline29Template_terminal_advances :
    ∀ instruction ∈ inline29Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline29Template_terminal_advances

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall26Inline
