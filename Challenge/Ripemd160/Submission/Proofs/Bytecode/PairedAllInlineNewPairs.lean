import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall26Inline

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineNewPairs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace
open PairedCall26Inline (oneRaw oneRaw_eq_rawBoolean)

def inline16Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23}

def inline16Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline16Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline16WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline16Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 3),
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

theorem inline16Template_length : inline16Template.length = 46 := rfl

#print axioms inline16Template_length

theorem run_inline16Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline16Template {s with pc := pc, stack := inline16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := inline16Output q (scaledT (inline16Frame s.memory q) q.upper (UInt256.ofNat 3) (UInt256.ofNat 25) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline16Template, inline16Entry, inline16Output,
    scaledT, scaledRotation, inlineSum, inline16Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline16Template_raw

theorem run_inline16Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline16Template {s with pc := pc, stack := inline16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := inline16Output q (scaledT (inline16Frame s.memory q) q.upper (UInt256.ofNat 3) (UInt256.ofNat 25) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline16Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline16Template

theorem run_inline16Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline16Template {s with pc := pc, stack := inline16Entry q rho} =
      some {s with pc := pcAfter pc inline16Template, stack := inline16WordStack q (PairedLaneWordRound.wordStep 1 7 9 (inline16Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline16Frame s.memory q) q.upper (UInt256.ofNat 3) (UInt256.ofNat 25) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 9 q.a q.b q.c q.d q.e
        (inline16Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline16Frame s.memory q) q.upper (UInt256.ofNat 3) (UInt256.ofNat 25)) (rawBoolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline16Frame s.memory q) 1 7 9 (UInt256.ofNat 3) (UInt256.ofNat 25) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline16Output q (scaledT (inline16Frame s.memory q) q.upper (UInt256.ofNat 3) (UInt256.ofNat 25) (rawBoolean q)) rho =
      inline16WordStack q (PairedLaneWordRound.wordStep 1 7 9
        (inline16Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline16Output, inline16WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline16Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline16Template, stack := vs}) hout)

#print axioms run_inline16Template_word

theorem inline16Template_terminal_advances :
    ∀ instruction ∈ inline16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline16Template_terminal_advances

def inline17Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 19}

def inline17Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline17Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline17WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline17Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
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

theorem inline17Template_length : inline17Template.length = 46 := rfl

#print axioms inline17Template_length

theorem run_inline17Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17Output q (scaledT (inline17Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 26) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline17Template, inline17Entry, inline17Output,
    scaledT, scaledRotation, inlineSum, inline17Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline17Template_raw

theorem run_inline17Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17Output q (scaledT (inline17Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 26) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline17Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline17Template

theorem run_inline17Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline17Template {s with pc := pc, stack := inline17Entry q rho} =
      some {s with pc := pcAfter pc inline17Template, stack := inline17WordStack q (PairedLaneWordRound.wordStep 1 6 13 (inline17Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline17Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 26) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 6 13 q.a q.b q.c q.d q.e
        (inline17Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline17Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 26)) (rawBoolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline17Frame s.memory q) 1 6 13 (UInt256.ofNat 127) (UInt256.ofNat 26) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline17Output q (scaledT (inline17Frame s.memory q) q.upper (UInt256.ofNat 127) (UInt256.ofNat 26) (rawBoolean q)) rho =
      inline17WordStack q (PairedLaneWordRound.wordStep 1 6 13
        (inline17Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline17Output, inline17WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline17Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline17Template, stack := vs}) hout)

#print axioms run_inline17Template_word

theorem inline17Template_terminal_advances :
    ∀ instruction ∈ inline17Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline17Template_terminal_advances

def inline28Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 26}

def inline28Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline28Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline28WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline28Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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

theorem inline28Template_length : inline28Template.length = 46 := rfl

#print axioms inline28Template_length

theorem run_inline28Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline28Template {s with pc := pc, stack := inline28Entry q rho} =
      some {s with pc := pcAfter pc inline28Template, stack := inline28Output q (scaledT (inline28Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 26) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline28Template, inline28Entry, inline28Output,
    scaledT, scaledRotation, inlineSum, inline28Frame, oneRaw, inlineProduct, rawC10,
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
      some {s with pc := pcAfter pc inline28Template, stack := inline28Output q (scaledT (inline28Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 26) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline28Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline28Template

theorem run_inline28Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline28Template {s with pc := pc, stack := inline28Entry q rho} =
      some {s with pc := pcAfter pc inline28Template, stack := inline28WordStack q (PairedLaneWordRound.wordStep 1 11 6 (inline28Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline28Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 26) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 11 6 q.a q.b q.c q.d q.e
        (inline28Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline28Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 26)) (rawBoolean_eq q hupper)).trans
      (scaledT_of_boolean_low (inline28Frame s.memory q) 1 11 6 (UInt256.ofNat 31) (UInt256.ofNat 26) (by decide) hfactor hpair hlower rfl rfl)
  have hout : inline28Output q (scaledT (inline28Frame s.memory q) q.lower (UInt256.ofNat 31) (UInt256.ofNat 26) (rawBoolean q)) rho =
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
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline29Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline29WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline29Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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

theorem inline29Template_length : inline29Template.length = 46 := rfl

#print axioms inline29Template_length

theorem run_inline29Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline29Template {s with pc := pc, stack := inline29Entry q rho} =
      some {s with pc := pcAfter pc inline29Template, stack := inline29Output q (scaledT (inline29Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline29Template, inline29Entry, inline29Output,
    scaledT, scaledRotation, inlineSum, inline29Frame, oneRaw, inlineProduct, rawC10,
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
      some {s with pc := pcAfter pc inline29Template, stack := inline29Output q (scaledT (inline29Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline29Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline29Template

theorem run_inline29Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline29Template {s with pc := pc, stack := inline29Entry q rho} =
      some {s with pc := pcAfter pc inline29Template, stack := inline29WordStack q (PairedLaneWordRound.wordStep 1 7 15 (inline29Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : scaledT (inline29Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 15 q.a q.b q.c q.d q.e
        (inline29Frame s.memory q).message0 q.k :=
    (congrArg (scaledT (inline29Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25)) (rawBoolean_eq q hupper)).trans
      (scaledT_of_boolean_high (inline29Frame s.memory q) 1 7 15 (UInt256.ofNat 255) (UInt256.ofNat 25) (by decide) hfactor hpair hupper rfl rfl)
  have hout : inline29Output q (scaledT (inline29Frame s.memory q) q.upper (UInt256.ofNat 255) (UInt256.ofNat 25) (rawBoolean q)) rho =
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineNewPairs

