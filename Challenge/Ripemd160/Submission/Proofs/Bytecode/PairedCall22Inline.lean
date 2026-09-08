import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall20Inline

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall22Inline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace
open PairedCall26Inline (oneRaw oneRaw_eq_rawBoolean)

def inline22Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23}

def inline22Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline22Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline22WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.upper, state.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline22Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
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

theorem inline22Template_length : inline22Template.length = 49 := rfl

#print axioms inline22Template_length

theorem run_inline22Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline22Template {s with pc := pc, stack := inline22Entry q rho} =
      some {s with pc := pcAfter pc inline22Template, stack := inline22Output q (inlineT (inline22Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline22Template, inline22Entry, inline22Output,
    inlineT, inlineRotation, inline22Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline22Template_raw

theorem run_inline22Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline22Template {s with pc := pc, stack := inline22Entry q rho} =
      some {s with pc := pcAfter pc inline22Template, stack := inline22Output q (inlineT (inline22Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline22Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline22Template

theorem run_inline22Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline22Template {s with pc := pc, stack := inline22Entry q rho} =
      some {s with pc := pcAfter pc inline22Template, stack := inline22WordStack q (PairedLaneWordRound.wordStep 1 7 9 (inline22Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline22Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 9 q.a q.b q.c q.d q.e
        (inline22Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline22Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline22Frame s.memory q) 1 7 9 hfactor hpair hupper rfl rfl))
  have hout : inline22Output q (inlineT (inline22Frame s.memory q) (rawBoolean q)) rho =
      inline22WordStack q (PairedLaneWordRound.wordStep 1 7 9
        (inline22Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline22Output, inline22WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline22Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline22Template, stack := vs}) hout)

#print axioms run_inline22Template_word

theorem inline22Template_terminal_advances :
    ∀ instruction ∈ inline22Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline22Template_terminal_advances

def inline23Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 21}

def inline23Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline23Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

def inline23WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.upper, state.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline23Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
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

theorem inline23Template_length : inline23Template.length = 48 := rfl

#print axioms inline23Template_length

theorem run_inline23Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline23Template {s with pc := pc, stack := inline23Entry q rho} =
      some {s with pc := pcAfter pc inline23Template, stack := inline23Output q (inlineT (inline23Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline23Template, inline23Entry, inline23Output,
    inlineT, inlineRotation, inline23Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline23Template_raw

theorem run_inline23Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline23Template {s with pc := pc, stack := inline23Entry q rho} =
      some {s with pc := pcAfter pc inline23Template, stack := inline23Output q (inlineT (inline23Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline23Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline23Template

theorem run_inline23Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline23Template {s with pc := pc, stack := inline23Entry q rho} =
      some {s with pc := pcAfter pc inline23Template, stack := inline23WordStack q (PairedLaneWordRound.wordStep 1 15 11 (inline23Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline23Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 15 11 q.a q.b q.c q.d q.e
        (inline23Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline23Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline23Frame s.memory q) 1 15 11 hfactor hpair hupper rfl rfl))
  have hout : inline23Output q (inlineT (inline23Frame s.memory q) (rawBoolean q)) rho =
      inline23WordStack q (PairedLaneWordRound.wordStep 1 15 11
        (inline23Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline23Output, inline23WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline23Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline23Template, stack := vs}) hout)

#print axioms run_inline23Template_word

theorem inline23Template_terminal_advances :
    ∀ instruction ∈ inline23Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline23Template_terminal_advances

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall22Inline
