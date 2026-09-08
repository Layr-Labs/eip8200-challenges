import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall20Inline

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall16Inline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace
open PairedCall26Inline (oneRaw oneRaw_eq_rawBoolean)

/-- Group-16 stack `[k,d,b,c,a,e,…]` into the even-lane `[d,a,b,c,upper,e,…]`. -/
def prelude16Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def prelude16Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def even16Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem prelude16Template_length : prelude16Template.length = 3 := rfl

theorem run_prelude16Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq prelude16Template {s with pc := pc, stack := prelude16Entry q rho} =
      some {s with pc := pcAfter pc prelude16Template, stack := even16Entry q rho} := by
  have hcap (n : Nat) (hn : n ≤ 12) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [prelude16Template, prelude16Entry, even16Entry,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl, rfl⟩

#print axioms prelude16Template_length
#print axioms run_prelude16Template

def inline16Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23}

def even16Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def even16WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.upper, state.a, q.factor, q.pair, q.k, q.lower] ++ rho

def even16Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 416),
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

theorem even16Template_length : even16Template.length = 49 := rfl

def inline16Template : List Instr := prelude16Template ++ even16Template

theorem inline16Template_length : inline16Template.length = 52 := rfl

theorem run_even16Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq even16Template {s with pc := pc, stack := even16Entry q rho} =
      some {s with pc := pcAfter pc even16Template, stack := even16Output q (inlineT (inline16Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [even16Template, even16Entry, even16Output,
    inlineT, inlineRotation, inline16Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline16Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline16Template {s with pc := pc, stack := prelude16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := even16Output q (inlineT (inline16Frame s.memory q) (oneRaw q)) rho} := by
  have h0 := run_prelude16Template s pc q rho hstack hrun
  have h1 := run_even16Template_raw s (pcAfter pc prelude16Template) q rho hstack hrun hactive
  have h := DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1
  simpa [inline16Template, pcAfter, List.map_append, List.sum_append] using h

theorem run_inline16Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline16Template {s with pc := pc, stack := prelude16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := even16Output q (inlineT (inline16Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline16Template_raw s pc q rho hstack hrun hactive

theorem run_inline16Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline16Template {s with pc := pc, stack := prelude16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := even16WordStack q (PairedLaneWordRound.wordStep 1 7 9 (inline16Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline16Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 9 q.a q.b q.c q.d q.e
        (inline16Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline16Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline16Frame s.memory q) 1 7 9 hfactor hpair hupper rfl rfl))
  have hout : even16Output q (inlineT (inline16Frame s.memory q) (rawBoolean q)) rho =
      even16WordStack q (PairedLaneWordRound.wordStep 1 7 9
        (inline16Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [even16Output, even16WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline16Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline16Template, stack := vs}) hout)

theorem inline16Template_terminal_advances :
    ∀ instruction ∈ inline16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms even16Template_length
#print axioms inline16Template_length
#print axioms run_inline16Template_raw
#print axioms run_inline16Template
#print axioms run_inline16Template_word
#print axioms inline16Template_terminal_advances

def inline17Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 19}

def inline17Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def odd17Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

/-- Helper-return shuffle: SWAP1 turns `[d,a,…]` into `[a,d,…]`. -/
def inline17Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.e, rawC10 q, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

def inline17WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.a, state.d, state.b, state.c, q.upper, state.e, q.factor, q.pair, q.k, q.lower] ++ rho

def odd17Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 320),
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
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

def inline17Template : List Instr :=
  odd17Template ++ [.op (.Swap ⟨0, by decide⟩)]

theorem odd17Template_length : odd17Template.length = 49 := rfl
theorem inline17Template_length : inline17Template.length = 50 := rfl

theorem run_odd17Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq odd17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc odd17Template, stack := odd17Output q (inlineT (inline17Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [odd17Template, inline17Entry, odd17Output,
    inlineT, inlineRotation, inline17Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

theorem run_inline17Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17Output q (inlineT (inline17Frame s.memory q) (oneRaw q)) rho} := by
  have h0 := run_odd17Template_raw s pc q rho hstack hrun hactive
  have hcap : rho.length + 12 < 1024 := by omega
  have h1 :
      runInstrSeq [.op (.Swap ⟨0, by decide⟩)]
        {s with pc := pcAfter pc odd17Template, stack := odd17Output q (inlineT (inline17Frame s.memory q) (oneRaw q)) rho} =
        some {s with pc := pcAfter pc inline17Template,
          stack := inline17Output q (inlineT (inline17Frame s.memory q) (oneRaw q)) rho} := by
    simp (discharger := omega) [odd17Output, inline17Output, runInstrSeq,
      Challenge.EvmProof.Stepper.runInstr, pcAfter, inline17Template, odd17Template,
      UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hcap]
    exact ⟨rfl, rfl, rfl⟩
  have h := DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1
  simpa [inline17Template] using h

theorem run_inline17Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17Output q (inlineT (inline17Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline17Template_raw s pc q rho hstack hrun hactive

theorem run_inline17Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17WordStack q (PairedLaneWordRound.wordStep 1 6 13 (inline17Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline17Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 6 13 q.a q.b q.c q.d q.e
        (inline17Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline17Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline17Frame s.memory q) 1 6 13 hfactor hpair hupper rfl rfl))
  have hout : inline17Output q (inlineT (inline17Frame s.memory q) (rawBoolean q)) rho =
      inline17WordStack q (PairedLaneWordRound.wordStep 1 6 13
        (inline17Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline17Output, inline17WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
    -- SWAP1 of [d, a, b, c, …] is [a, d, b, c, …]
    rfl
  exact (run_inline17Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline17Template, stack := vs}) hout)

theorem inline17Template_terminal_advances :
    ∀ instruction ∈ inline17Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms odd17Template_length
#print axioms inline17Template_length
#print axioms run_inline17Template_raw
#print axioms run_inline17Template
#print axioms run_inline17Template_word
#print axioms inline17Template_terminal_advances

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall16Inline
