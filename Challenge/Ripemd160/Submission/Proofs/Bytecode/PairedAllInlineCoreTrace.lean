import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineNewPairs
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedFactoredGroupConstants

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist
open PairedSynthCoreTrace (zeroRaw fourRaw zeroRaw_eq_inline0Boolean fourRaw_eq_inline4Boolean
  oneRaw threeRaw oneRaw_eq_rawBoolean threeRaw_eq_inline3Boolean
  inlineHoistedBoolean rawT_hoisted hoistedAlgorithmFold hoistedAlgorithmStep
  hoistedAlgorithmFold_succ hoistedAlgorithmFold_crypto physicalKey)

def groupK_consumedOutput (q : PairedHelperBooleanTrace.Frame) (value : UInt256)
    (rho : List UInt256) : List UInt256 :=
  [rawC10 q, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def groupK_consumedWordStack (q : PairedHelperBooleanTrace.Frame)
    (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def groupK_group47Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 27}

def groupK_group47Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def groupK_consumed15Template : List Instr :=
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
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 2),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND]

theorem groupK_consumed15Template_length : groupK_consumed15Template.length = 45 := rfl

#print axioms groupK_consumed15Template_length

theorem groupK_run_consumed15Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq groupK_consumed15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc groupK_consumed15Template, stack := groupK_consumedOutput q (inlineT (inline15Frame s.memory q) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word,
    groupK_consumed15Template, inline15Entry, groupK_consumedOutput,
    inlineT, inlineRotation, inline15Frame, zeroRaw,
    PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  refine ⟨rfl, rfl, ?_⟩
  let post (v : UInt256) : UInt256 :=
    let product := UInt256.mul q.factor (UInt256.land q.pair v)
    UInt256.land q.pair (UInt256.add q.e
      (UInt256.xor
        (UInt256.land q.upper
          (UInt256.xor (UInt256.shiftRight product (UInt256.ofNat 24))
            (UInt256.shiftRight product (UInt256.ofNat 26))))
        (UInt256.shiftRight product (UInt256.ofNat 24))))
  let sum := UInt256.add (inline15Frame s.memory q).message0 (UInt256.add (zeroRaw q) q.a)
  change post (UInt256.add sum q.k) = post (UInt256.add q.k sum)
  exact congrArg post (Challenge.EvmProof.Word.word_add_comm sum q.k)

#print axioms groupK_run_consumed15Template_raw

theorem groupK_run_consumed15Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq groupK_consumed15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc groupK_consumed15Template, stack := groupK_consumedWordStack q (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline15Frame s.memory q) (zeroRaw q) =
      PairedLaneWordRound.wordT 0 8 6 q.a q.b q.c q.d q.e
        (inline15Frame s.memory q).message0 q.k := by
    rw [zeroRaw_eq_inline0Boolean]
    exact (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline15Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline15Frame s.memory q) 0 8 6 hfactor hpair hupper rfl rfl))
  have hout : groupK_consumedOutput q (inlineT (inline15Frame s.memory q) (zeroRaw q)) rho =
      groupK_consumedWordStack q
        (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [groupK_consumedOutput, groupK_consumedWordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (groupK_run_consumed15Template_raw s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc groupK_consumed15Template, stack := vs}) hout)

#print axioms groupK_run_consumed15Template_word

theorem groupK_consumed15Template_bytes : (groupK_consumed15Template.map Instr.size).sum = 52 := rfl

#print axioms groupK_consumed15Template_bytes

def groupK_consumed47Template : List Instr :=
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
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
   .op .SHR,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND]

theorem groupK_consumed47Template_length : groupK_consumed47Template.length = 32 := rfl

#print axioms groupK_consumed47Template_length

theorem groupK_run_consumed47Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq groupK_consumed47Template {s with pc := pc, stack := groupK_group47Entry q rho} =
      some {s with pc := pcAfter pc groupK_consumed47Template, stack := groupK_consumedOutput q (singleT (groupK_group47Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [groupK_consumed47Template, groupK_group47Entry, groupK_consumedOutput,
    singleT, groupK_group47Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  refine ⟨rfl, rfl, ?_⟩
  let post (v : UInt256) : UInt256 :=
    UInt256.land q.pair (UInt256.add q.e
      (UInt256.shiftRight (UInt256.mul q.factor (UInt256.land q.pair v)) (UInt256.ofNat 27)))
  let sum := UInt256.add (groupK_group47Frame s.memory q).message0
    (UInt256.add (inlineHoistedBoolean q) q.a)
  change post (UInt256.add sum q.k) = post (UInt256.add q.k sum)
  exact congrArg post (Challenge.EvmProof.Word.word_add_comm sum q.k)

#print axioms groupK_run_consumed47Template_raw

theorem groupK_run_consumed47Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq groupK_consumed47Template {s with pc := pc, stack := groupK_group47Entry q rho} =
      some {s with pc := pcAfter pc groupK_consumed47Template, stack := groupK_consumedWordStack q (rawWordStep2 5 5 (groupK_group47Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (groupK_group47Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 5 5 q.a q.b q.c q.d q.e (groupK_group47Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      (rawT_hoisted (groupK_group47Frame s.memory q) 5 5 hfactor hpair hupper rfl rfl)
  have hout : groupK_consumedOutput q (singleT (groupK_group47Frame s.memory q) (inlineHoistedBoolean q)) rho =
      groupK_consumedWordStack q
        (rawWordStep2 5 5 (groupK_group47Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [groupK_consumedOutput, groupK_consumedWordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (groupK_run_consumed47Template_raw s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc groupK_consumed47Template, stack := vs}) hout)

#print axioms groupK_run_consumed47Template_word

theorem groupK_consumed47Template_bytes : (groupK_consumed47Template.map Instr.size).sum = 38 := rfl

#print axioms groupK_consumed47Template_bytes

private theorem groupK_word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem groupK_word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [groupK_word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

def groupK_materialize16Template : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0x5c4dd124),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .SHL,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x5a827999), .op .OR]

theorem groupK_run_materialize16Template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq groupK_materialize16Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc groupK_materialize16Template, stack := UInt256.ofNat 526962527014005041256681316140890030896371104153 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  have hzero : rho.length < 1024 := by omega
  simp [groupK_materialize16Template, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, Nat.add_assoc, UInt256.succ, hrun, hzero, hcap,
    PairedFactoredGroupConstants.mixed_value, groupK_word_add_ofNat_assoc]
  change (((pc + UInt256.ofNat 7) + UInt256.ofNat 1) + UInt256.ofNat 5) + UInt256.ofNat 1 = pc + UInt256.ofNat 14
  simp only [groupK_word_add_ofNat_assoc]

#print axioms groupK_run_materialize16Template

def groupK_materialize48Template : List Instr :=
  [.push ⟨20, by decide⟩ (UInt256.ofNat 698938013802679700166637234969497128417458109660)]

theorem groupK_run_materialize48Template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1024) (hrun : s.halt = .Running) :
    runInstrSeq groupK_materialize48Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc groupK_materialize48Template, stack := UInt256.ofNat 698938013802679700166637234969497128417458109660 :: rho} := by
  simp [groupK_materialize48Template, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, hrun, hstack]

#print axioms groupK_run_materialize48Template

theorem groupK_materialize_lengths :
    groupK_materialize16Template.length = 5 ∧ groupK_materialize48Template.length = 1 := by decide

#print axioms groupK_materialize_lengths

theorem groupK_materialize_bytes :
    (groupK_materialize16Template.map Instr.size).sum = 14 ∧
    (groupK_materialize48Template.map Instr.size).sum = 21 := by decide

#print axioms groupK_materialize_bytes

def inline18Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 17}

def inline18Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline18Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline18WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline18Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 608),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 304),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

theorem inline18Template_length : inline18Template.length = 49 := rfl

#print axioms inline18Template_length

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

#print axioms run_inline18Template_raw

theorem run_inline18Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline18Template {s with pc := pc, stack := inline18Entry q rho} =
      some {s with pc := pcAfter pc inline18Template, stack := inline18Output q (inlineT (inline18Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline18Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline18Template

theorem run_inline18Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline18Template {s with pc := pc, stack := inline18Entry q rho} =
      some {s with pc := pcAfter pc inline18Template, stack := inline18WordStack q (PairedLaneWordRound.wordStep 1 8 15 (inline18Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline18Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 8 15 q.a q.b q.c q.d q.e
        (inline18Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline18Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline18Frame s.memory q) 1 8 15 hfactor hpair hupper rfl rfl))
  have hout : inline18Output q (inlineT (inline18Frame s.memory q) (rawBoolean q)) rho =
      inline18WordStack q
        (PairedLaneWordRound.wordStep 1 8 15 (inline18Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline18Output, inline18WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline18Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline18Template, stack := vs}) hout)

#print axioms run_inline18Template_word

def inline19Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 25}

def inline19Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline19Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline19WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline19Template : List Instr :=
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 224),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 432),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline19Template_length

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

#print axioms run_inline19Template_raw

theorem run_inline19Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline19Template {s with pc := pc, stack := inline19Entry q rho} =
      some {s with pc := pcAfter pc inline19Template, stack := inline19Output q (inlineT (inline19Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline19Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline19Template

theorem run_inline19Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline19Template {s with pc := pc, stack := inline19Entry q rho} =
      some {s with pc := pcAfter pc inline19Template, stack := inline19WordStack q (PairedLaneWordRound.wordStep 1 13 7 (inline19Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline19Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 13 7 q.a q.b q.c q.d q.e
        (inline19Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline19Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline19Frame s.memory q) 1 13 7 hfactor hpair hupper rfl rfl))
  have hout : inline19Output q (inlineT (inline19Frame s.memory q) (rawBoolean q)) rho =
      inline19WordStack q
        (PairedLaneWordRound.wordStep 1 13 7 (inline19Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline19Output, inline19WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline19Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline19Template, stack := vs}) hout)

#print axioms run_inline19Template_word

def inline20Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 20}

def inline20Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline20Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline20WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline20Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
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

theorem inline20Template_length : inline20Template.length = 49 := rfl

#print axioms inline20Template_length

theorem run_inline20Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline20Template {s with pc := pc, stack := inline20Entry q rho} =
      some {s with pc := pcAfter pc inline20Template, stack := inline20Output q (inlineT (inline20Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline20Template, inline20Entry, inline20Output,
    inlineT, inlineRotation, inline20Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline20Template_raw

theorem run_inline20Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline20Template {s with pc := pc, stack := inline20Entry q rho} =
      some {s with pc := pcAfter pc inline20Template, stack := inline20Output q (inlineT (inline20Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline20Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline20Template

theorem run_inline20Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline20Template {s with pc := pc, stack := inline20Entry q rho} =
      some {s with pc := pcAfter pc inline20Template, stack := inline20WordStack q (PairedLaneWordRound.wordStep 1 11 12 (inline20Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline20Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 11 12 q.a q.b q.c q.d q.e
        (inline20Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline20Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline20Frame s.memory q) 1 11 12 hfactor hpair hupper rfl rfl))
  have hout : inline20Output q (inlineT (inline20Frame s.memory q) (rawBoolean q)) rho =
      inline20WordStack q
        (PairedLaneWordRound.wordStep 1 11 12 (inline20Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline20Output, inline20WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline20Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline20Template, stack := vs}) hout)

#print axioms run_inline20Template_word

def inline21Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 24}

def inline21Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline21Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline21WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline21Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

theorem inline21Template_length : inline21Template.length = 48 := rfl

#print axioms inline21Template_length

theorem run_inline21Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline21Template {s with pc := pc, stack := inline21Entry q rho} =
      some {s with pc := pcAfter pc inline21Template, stack := inline21Output q (inlineT (inline21Frame s.memory q) (oneRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word, inline21Template, inline21Entry, inline21Output,
    inlineT, inlineRotation, inline21Frame, oneRaw, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_inline21Template_raw

theorem run_inline21Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline21Template {s with pc := pc, stack := inline21Entry q rho} =
      some {s with pc := pcAfter pc inline21Template, stack := inline21Output q (inlineT (inline21Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline21Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline21Template

theorem run_inline21Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline21Template {s with pc := pc, stack := inline21Entry q rho} =
      some {s with pc := pcAfter pc inline21Template, stack := inline21WordStack q (PairedLaneWordRound.wordStep 1 9 8 (inline21Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline21Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 9 8 q.a q.b q.c q.d q.e
        (inline21Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline21Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline21Frame s.memory q) 1 9 8 hfactor hpair hupper rfl rfl))
  have hout : inline21Output q (inlineT (inline21Frame s.memory q) (rawBoolean q)) rho =
      inline21WordStack q
        (PairedLaneWordRound.wordStep 1 9 8 (inline21Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline21Output, inline21WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline21Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline21Template, stack := vs}) hout)

#print axioms run_inline21Template_word

def inline22Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23}

def inline22Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline22Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline22WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline22Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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
      inline22WordStack q
        (PairedLaneWordRound.wordStep 1 7 9 (inline22Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline22Output, inline22WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline22Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline22Template, stack := vs}) hout)

#print axioms run_inline22Template_word

def inline23Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 21}

def inline23Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline23Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline23WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline23Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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
      inline23WordStack q
        (PairedLaneWordRound.wordStep 1 15 11 (inline23Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline23Output, inline23WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline23Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline23Template, stack := vs}) hout)

#print axioms run_inline23Template_word

def inline24Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 25}

def inline24Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline24Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline24WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline24Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 576),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 656),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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

#print axioms inline24Template_length

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

#print axioms run_inline24Template_raw

theorem run_inline24Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline24Template {s with pc := pc, stack := inline24Entry q rho} =
      some {s with pc := pcAfter pc inline24Template, stack := inline24Output q (singleT (inline24Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline24Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline24Template

theorem run_inline24Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline24Template {s with pc := pc, stack := inline24Entry q rho} =
      some {s with pc := pcAfter pc inline24Template, stack := inline24WordStack q (PairedLaneWordRound.wordStep 1 7 7 (inline24Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline24Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 7 7 q.a q.b q.c q.d q.e
        (inline24Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      ((congrArg (rawT (inline24Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline24Frame s.memory q) 1 7 7 hfactor hpair hupper rfl rfl))
  have hout : inline24Output q (singleT (inline24Frame s.memory q) (rawBoolean q)) rho =
      inline24WordStack q
        (PairedLaneWordRound.wordStep 1 7 7 (inline24Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline24Output, inline24WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline24Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline24Template, stack := vs}) hout)

#print axioms run_inline24Template_word

def inline25Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 25}

def inline25Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline25Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline25WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline25Template : List Instr :=
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 192),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 688),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline25Template_length

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

#print axioms run_inline25Template_raw

theorem run_inline25Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline25Template {s with pc := pc, stack := inline25Entry q rho} =
      some {s with pc := pcAfter pc inline25Template, stack := inline25Output q (inlineT (inline25Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline25Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline25Template

theorem run_inline25Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline25Template {s with pc := pc, stack := inline25Entry q rho} =
      some {s with pc := pcAfter pc inline25Template, stack := inline25WordStack q (PairedLaneWordRound.wordStep 1 12 7 (inline25Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline25Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 12 7 q.a q.b q.c q.d q.e
        (inline25Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline25Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline25Frame s.memory q) 1 12 7 hfactor hpair hupper rfl rfl))
  have hout : inline25Output q (inlineT (inline25Frame s.memory q) (rawBoolean q)) rho =
      inline25WordStack q
        (PairedLaneWordRound.wordStep 1 12 7 (inline25Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline25Output, inline25WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline25Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline25Template, stack := vs}) hout)

#print axioms run_inline25Template_word

def inline26Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 20}

def inline26Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline26Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline26WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline26Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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
      inline26WordStack q
        (PairedLaneWordRound.wordStep 1 15 12 (inline26Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline26Output, inline26WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline26Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline26Template, stack := vs}) hout)

#print axioms run_inline26Template_word

def inline27Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 25}

def inline27Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline27Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline27WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline27Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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
      inline27WordStack q
        (PairedLaneWordRound.wordStep 1 9 7 (inline27Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline27Output, inline27WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline27Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline27Template, stack := vs}) hout)

#print axioms run_inline27Template_word

def inline30Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 19}

def inline30Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline30Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline30WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline30Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 544),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 240),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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

theorem inline30Template_length : inline30Template.length = 40 := rfl

#print axioms inline30Template_length

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

#print axioms run_inline30Template_raw

theorem run_inline30Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline30Template {s with pc := pc, stack := inline30Entry q rho} =
      some {s with pc := pcAfter pc inline30Template, stack := inline30Output q (singleT (inline30Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline30Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline30Template

theorem run_inline30Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline30Template {s with pc := pc, stack := inline30Entry q rho} =
      some {s with pc := pcAfter pc inline30Template, stack := inline30WordStack q (PairedLaneWordRound.wordStep 1 13 13 (inline30Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline30Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 13 13 q.a q.b q.c q.d q.e
        (inline30Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      ((congrArg (rawT (inline30Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline30Frame s.memory q) 1 13 13 hfactor hpair hupper rfl rfl))
  have hout : inline30Output q (singleT (inline30Frame s.memory q) (rawBoolean q)) rho =
      inline30WordStack q
        (PairedLaneWordRound.wordStep 1 13 13 (inline30Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline30Output, inline30WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline30Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline30Template, stack := vs}) hout)

#print axioms run_inline30Template_word

def inline31Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 21}

def inline31Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline31Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline31WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline31Template : List Instr :=
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 448),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 272),
   .op .MLOAD,
   .op .OR,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline31Template_length

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

#print axioms run_inline31Template_raw

theorem run_inline31Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline31Template {s with pc := pc, stack := inline31Entry q rho} =
      some {s with pc := pcAfter pc inline31Template, stack := inline31Output q (inlineT (inline31Frame s.memory q) (rawBoolean q)) rho} := by
  simpa only [oneRaw_eq_rawBoolean] using
    run_inline31Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline31Template

theorem run_inline31Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline31Template {s with pc := pc, stack := inline31Entry q rho} =
      some {s with pc := pcAfter pc inline31Template, stack := inline31WordStack q (PairedLaneWordRound.wordStep 1 12 11 (inline31Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline31Frame s.memory q) (rawBoolean q) =
      PairedLaneWordRound.wordT 1 12 11 q.a q.b q.c q.d q.e
        (inline31Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline31Frame s.memory q)) (rawBoolean_eq q hupper)).trans
        (rawT_of_boolean (inline31Frame s.memory q) 1 12 11 hfactor hpair hupper rfl rfl))
  have hout : inline31Output q (inlineT (inline31Frame s.memory q) (rawBoolean q)) rho =
      inline31WordStack q
        (PairedLaneWordRound.wordStep 1 12 11 (inline31Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline31Output, inline31WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline31Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline31Template, stack := vs}) hout)

#print axioms run_inline31Template_word

def inline32Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 23}

def inline32Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline32Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline32WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline32Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline32Template_length

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

#print axioms run_inline32Template

theorem run_inline32Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline32Template {s with pc := pc, stack := inline32Entry q rho} =
      some {s with pc := pcAfter pc inline32Template, stack := inline32WordStack q (rawWordStep2 11 9 (inline32Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline32Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 11 9 q.a q.b q.c q.d q.e (inline32Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline32Frame s.memory q) 11 9 hfactor hpair hupper rfl rfl)
  have hout : inline32Output q (inlineT (inline32Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline32WordStack q
        (rawWordStep2 11 9 (inline32Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline32Output, inline32WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline32Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline32Template, stack := vs}) hout)

#print axioms run_inline32Template_word

def inline33Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 25}

def inline33Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline33Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline33WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline33Template_length : inline33Template.length = 41 := rfl

#print axioms inline33Template_length

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

#print axioms run_inline33Template

theorem run_inline33Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline33Template {s with pc := pc, stack := inline33Entry q rho} =
      some {s with pc := pcAfter pc inline33Template, stack := inline33WordStack q (rawWordStep2 13 7 (inline33Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline33Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 13 7 q.a q.b q.c q.d q.e (inline33Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline33Frame s.memory q) 13 7 hfactor hpair hupper rfl rfl)
  have hout : inline33Output q (inlineT (inline33Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline33WordStack q
        (rawWordStep2 13 7 (inline33Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline33Output, inline33WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline33Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline33Template, stack := vs}) hout)

#print axioms run_inline33Template_word

def inline34Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 17}

def inline34Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline34Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline34WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline34Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline34Template_length

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

#print axioms run_inline34Template

theorem run_inline34Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline34Template {s with pc := pc, stack := inline34Entry q rho} =
      some {s with pc := pcAfter pc inline34Template, stack := inline34WordStack q (rawWordStep2 6 15 (inline34Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline34Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 6 15 q.a q.b q.c q.d q.e (inline34Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline34Frame s.memory q) 6 15 hfactor hpair hupper rfl rfl)
  have hout : inline34Output q (inlineT (inline34Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline34WordStack q
        (rawWordStep2 6 15 (inline34Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline34Output, inline34WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline34Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline34Template, stack := vs}) hout)

#print axioms run_inline34Template_word

def inline35Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 21}

def inline35Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline35Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline35WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline35Template_length : inline35Template.length = 42 := rfl

#print axioms inline35Template_length

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

#print axioms run_inline35Template

theorem run_inline35Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline35Template {s with pc := pc, stack := inline35Entry q rho} =
      some {s with pc := pcAfter pc inline35Template, stack := inline35WordStack q (rawWordStep2 7 11 (inline35Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline35Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 7 11 q.a q.b q.c q.d q.e (inline35Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline35Frame s.memory q) 7 11 hfactor hpair hupper rfl rfl)
  have hout : inline35Output q (inlineT (inline35Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline35WordStack q
        (rawWordStep2 7 11 (inline35Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline35Output, inline35WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline35Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline35Template, stack := vs}) hout)

#print axioms run_inline35Template_word

def inline36Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 24}

def inline36Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline36Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline36WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline36Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline36Template_length

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

#print axioms run_inline36Template

theorem run_inline36Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline36Template {s with pc := pc, stack := inline36Entry q rho} =
      some {s with pc := pcAfter pc inline36Template, stack := inline36WordStack q (rawWordStep2 14 8 (inline36Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline36Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 14 8 q.a q.b q.c q.d q.e (inline36Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline36Frame s.memory q) 14 8 hfactor hpair hupper rfl rfl)
  have hout : inline36Output q (inlineT (inline36Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline36WordStack q
        (rawWordStep2 14 8 (inline36Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline36Output, inline36WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline36Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline36Template, stack := vs}) hout)

#print axioms run_inline36Template_word

def inline37Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline37Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline37Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline37WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline37Template_length : inline37Template.length = 41 := rfl

#print axioms inline37Template_length

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

#print axioms run_inline37Template

theorem run_inline37Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline37Template {s with pc := pc, stack := inline37Entry q rho} =
      some {s with pc := pcAfter pc inline37Template, stack := inline37WordStack q (rawWordStep2 9 6 (inline37Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline37Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 9 6 q.a q.b q.c q.d q.e (inline37Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline37Frame s.memory q) 9 6 hfactor hpair hupper rfl rfl)
  have hout : inline37Output q (inlineT (inline37Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline37WordStack q
        (rawWordStep2 9 6 (inline37Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline37Output, inline37WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline37Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline37Template, stack := vs}) hout)

#print axioms run_inline37Template_word

def inline38Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 26}

def inline38Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline38Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline38WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline38Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline38Template_length

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

#print axioms run_inline38Template

theorem run_inline38Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline38Template {s with pc := pc, stack := inline38Entry q rho} =
      some {s with pc := pcAfter pc inline38Template, stack := inline38WordStack q (rawWordStep2 13 6 (inline38Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline38Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 13 6 q.a q.b q.c q.d q.e (inline38Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline38Frame s.memory q) 13 6 hfactor hpair hupper rfl rfl)
  have hout : inline38Output q (inlineT (inline38Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline38WordStack q
        (rawWordStep2 13 6 (inline38Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline38Output, inline38WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline38Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline38Template, stack := vs}) hout)

#print axioms run_inline38Template_word

def inline39Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 18}

def inline39Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline39Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline39WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline39Template_length : inline39Template.length = 41 := rfl

#print axioms inline39Template_length

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

#print axioms run_inline39Template

theorem run_inline39Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline39Template {s with pc := pc, stack := inline39Entry q rho} =
      some {s with pc := pcAfter pc inline39Template, stack := inline39WordStack q (rawWordStep2 15 14 (inline39Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline39Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 15 14 q.a q.b q.c q.d q.e (inline39Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline39Frame s.memory q) 15 14 hfactor hpair hupper rfl rfl)
  have hout : inline39Output q (inlineT (inline39Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline39WordStack q
        (rawWordStep2 15 14 (inline39Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline39Output, inline39WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline39Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline39Template, stack := vs}) hout)

#print axioms run_inline39Template_word

def inline40Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 20}

def inline40Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline40Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline40WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline40Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline40Template_length

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

#print axioms run_inline40Template

theorem run_inline40Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline40Template {s with pc := pc, stack := inline40Entry q rho} =
      some {s with pc := pcAfter pc inline40Template, stack := inline40WordStack q (rawWordStep2 14 12 (inline40Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline40Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 14 12 q.a q.b q.c q.d q.e (inline40Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline40Frame s.memory q) 14 12 hfactor hpair hupper rfl rfl)
  have hout : inline40Output q (inlineT (inline40Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline40WordStack q
        (rawWordStep2 14 12 (inline40Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline40Output, inline40WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline40Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline40Template, stack := vs}) hout)

#print axioms run_inline40Template_word

def inline41Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 19}

def inline41Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline41Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline41WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline41Template_length : inline41Template.length = 42 := rfl

#print axioms inline41Template_length

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

#print axioms run_inline41Template

theorem run_inline41Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline41Template {s with pc := pc, stack := inline41Entry q rho} =
      some {s with pc := pcAfter pc inline41Template, stack := inline41WordStack q (rawWordStep2 8 13 (inline41Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline41Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 8 13 q.a q.b q.c q.d q.e (inline41Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline41Frame s.memory q) 8 13 hfactor hpair hupper rfl rfl)
  have hout : inline41Output q (inlineT (inline41Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline41WordStack q
        (rawWordStep2 8 13 (inline41Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline41Output, inline41WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline41Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline41Template, stack := vs}) hout)

#print axioms run_inline41Template_word

def inline42Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 27}

def inline42Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline42Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline42WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline42Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline42Template_length

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

#print axioms run_inline42Template

theorem run_inline42Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline42Template {s with pc := pc, stack := inline42Entry q rho} =
      some {s with pc := pcAfter pc inline42Template, stack := inline42WordStack q (rawWordStep2 13 5 (inline42Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline42Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 13 5 q.a q.b q.c q.d q.e (inline42Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline42Frame s.memory q) 13 5 hfactor hpair hupper rfl rfl)
  have hout : inline42Output q (inlineT (inline42Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline42WordStack q
        (rawWordStep2 13 5 (inline42Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline42Output, inline42WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline42Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline42Template, stack := vs}) hout)

#print axioms run_inline42Template_word

def inline43Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 18}

def inline43Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline43Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline43WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline43Template_length : inline43Template.length = 42 := rfl

#print axioms inline43Template_length

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

#print axioms run_inline43Template

theorem run_inline43Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline43Template {s with pc := pc, stack := inline43Entry q rho} =
      some {s with pc := pcAfter pc inline43Template, stack := inline43WordStack q (rawWordStep2 6 14 (inline43Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline43Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 6 14 q.a q.b q.c q.d q.e (inline43Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline43Frame s.memory q) 6 14 hfactor hpair hupper rfl rfl)
  have hout : inline43Output q (inlineT (inline43Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline43WordStack q
        (rawWordStep2 6 14 (inline43Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline43Output, inline43WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline43Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline43Template, stack := vs}) hout)

#print axioms run_inline43Template_word

def inline44Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 19}

def inline44Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline44Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline44WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline44Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline44Template_length

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

#print axioms run_inline44Template

theorem run_inline44Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline44Template {s with pc := pc, stack := inline44Entry q rho} =
      some {s with pc := pcAfter pc inline44Template, stack := inline44WordStack q (rawWordStep2 5 13 (inline44Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline44Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 5 13 q.a q.b q.c q.d q.e (inline44Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline44Frame s.memory q) 5 13 hfactor hpair hupper rfl rfl)
  have hout : inline44Output q (inlineT (inline44Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline44WordStack q
        (rawWordStep2 5 13 (inline44Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline44Output, inline44WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline44Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline44Template, stack := vs}) hout)

#print axioms run_inline44Template_word

def inline45Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 19}

def inline45Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline45Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline45WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline45Template_length : inline45Template.length = 42 := rfl

#print axioms inline45Template_length

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

#print axioms run_inline45Template

theorem run_inline45Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline45Template {s with pc := pc, stack := inline45Entry q rho} =
      some {s with pc := pcAfter pc inline45Template, stack := inline45WordStack q (rawWordStep2 12 13 (inline45Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline45Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 12 13 q.a q.b q.c q.d q.e (inline45Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      (rawT_hoisted (inline45Frame s.memory q) 12 13 hfactor hpair hupper rfl rfl)
  have hout : inline45Output q (inlineT (inline45Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline45WordStack q
        (rawWordStep2 12 13 (inline45Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline45Output, inline45WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline45Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline45Template, stack := vs}) hout)

#print axioms run_inline45Template_word

def inline46Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 25}

def inline46Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline46Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline46WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline46Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
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

#print axioms inline46Template_length

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

#print axioms run_inline46Template

theorem run_inline46Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline46Template {s with pc := pc, stack := inline46Entry q rho} =
      some {s with pc := pcAfter pc inline46Template, stack := inline46WordStack q (rawWordStep2 7 7 (inline46Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline46Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 7 7 q.a q.b q.c q.d q.e (inline46Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      (rawT_hoisted (inline46Frame s.memory q) 7 7 hfactor hpair hupper rfl rfl)
  have hout : inline46Output q (singleT (inline46Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline46WordStack q
        (rawWordStep2 7 7 (inline46Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline46Output, inline46WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline46Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline46Template, stack := vs}) hout)

#print axioms run_inline46Template_word

def inline47Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 27}

def inline47Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline47Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline47WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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

theorem inline47Template_length : inline47Template.length = 33 := rfl

#print axioms inline47Template_length

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

#print axioms run_inline47Template

theorem run_inline47Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline47Template {s with pc := pc, stack := inline47Entry q rho} =
      some {s with pc := pcAfter pc inline47Template, stack := inline47WordStack q (rawWordStep2 5 5 (inline47Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline47Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 5 5 q.a q.b q.c q.d q.e (inline47Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      (rawT_hoisted (inline47Frame s.memory q) 5 5 hfactor hpair hupper rfl rfl)
  have hout : inline47Output q (singleT (inline47Frame s.memory q) (inlineHoistedBoolean q)) rho =
      inline47WordStack q
        (rawWordStep2 5 5 (inline47Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline47Output, inline47WordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline47Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline47Template, stack := vs}) hout)



#print axioms run_inline47Template_word

def inline48Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 17}

def inline48Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline48Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline48WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline48Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline48Template_length

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

#print axioms run_inline48Template_raw

theorem run_inline48Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline48Template {s with pc := pc, stack := inline48Entry q rho} =
      some {s with pc := pcAfter pc inline48Template, stack := inline48Output q (inlineT (inline48Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline48Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline48Template

theorem run_inline48Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline48Template {s with pc := pc, stack := inline48Entry q rho} =
      some {s with pc := pcAfter pc inline48Template, stack := inline48WordStack q (PairedLaneWordRound.wordStep 3 11 15 (inline48Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline48Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 11 15 q.a q.b q.c q.d q.e
        (inline48Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline48Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline48Frame s.memory q) 3 11 15 hfactor hpair hupper rfl rfl))
  have hout : inline48Output q (inlineT (inline48Frame s.memory q) (inline3Boolean q)) rho =
      inline48WordStack q
        (PairedLaneWordRound.wordStep 3 11 15 (inline48Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline48Output, inline48WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline48Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline48Template, stack := vs}) hout)

#print axioms run_inline48Template_word

def inline49Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 27}

def inline49Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline49Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline49WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline49Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline49Template_length

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

#print axioms run_inline49Template_raw

theorem run_inline49Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline49Template {s with pc := pc, stack := inline49Entry q rho} =
      some {s with pc := pcAfter pc inline49Template, stack := inline49Output q (inlineT (inline49Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline49Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline49Template

theorem run_inline49Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline49Template {s with pc := pc, stack := inline49Entry q rho} =
      some {s with pc := pcAfter pc inline49Template, stack := inline49WordStack q (PairedLaneWordRound.wordStep 3 12 5 (inline49Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline49Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 12 5 q.a q.b q.c q.d q.e
        (inline49Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline49Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline49Frame s.memory q) 3 12 5 hfactor hpair hupper rfl rfl))
  have hout : inline49Output q (inlineT (inline49Frame s.memory q) (inline3Boolean q)) rho =
      inline49WordStack q
        (PairedLaneWordRound.wordStep 3 12 5 (inline49Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline49Output, inline49WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline49Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline49Template, stack := vs}) hout)

#print axioms run_inline49Template_word

def inline50Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 24}

def inline50Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline50Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline50WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline50Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline50Template_length

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

#print axioms run_inline50Template_raw

theorem run_inline50Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline50Template {s with pc := pc, stack := inline50Entry q rho} =
      some {s with pc := pcAfter pc inline50Template, stack := inline50Output q (inlineT (inline50Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline50Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline50Template

theorem run_inline50Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline50Template {s with pc := pc, stack := inline50Entry q rho} =
      some {s with pc := pcAfter pc inline50Template, stack := inline50WordStack q (PairedLaneWordRound.wordStep 3 14 8 (inline50Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline50Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 14 8 q.a q.b q.c q.d q.e
        (inline50Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline50Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline50Frame s.memory q) 3 14 8 hfactor hpair hupper rfl rfl))
  have hout : inline50Output q (inlineT (inline50Frame s.memory q) (inline3Boolean q)) rho =
      inline50WordStack q
        (PairedLaneWordRound.wordStep 3 14 8 (inline50Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline50Output, inline50WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline50Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline50Template, stack := vs}) hout)

#print axioms run_inline50Template_word

def inline51Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 21}

def inline51Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline51Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline51WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline51Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline51Template_length

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

#print axioms run_inline51Template_raw

theorem run_inline51Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline51Template {s with pc := pc, stack := inline51Entry q rho} =
      some {s with pc := pcAfter pc inline51Template, stack := inline51Output q (inlineT (inline51Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline51Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline51Template

theorem run_inline51Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline51Template {s with pc := pc, stack := inline51Entry q rho} =
      some {s with pc := pcAfter pc inline51Template, stack := inline51WordStack q (PairedLaneWordRound.wordStep 3 15 11 (inline51Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline51Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 15 11 q.a q.b q.c q.d q.e
        (inline51Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline51Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline51Frame s.memory q) 3 15 11 hfactor hpair hupper rfl rfl))
  have hout : inline51Output q (inlineT (inline51Frame s.memory q) (inline3Boolean q)) rho =
      inline51WordStack q
        (PairedLaneWordRound.wordStep 3 15 11 (inline51Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline51Output, inline51WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline51Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline51Template, stack := vs}) hout)

#print axioms run_inline51Template_word

def inline52Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 18}

def inline52Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline52Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline52WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline52Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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

#print axioms inline52Template_length

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

#print axioms run_inline52Template_raw

theorem run_inline52Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline52Template {s with pc := pc, stack := inline52Entry q rho} =
      some {s with pc := pcAfter pc inline52Template, stack := inline52Output q (singleT (inline52Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline52Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline52Template

theorem run_inline52Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline52Template {s with pc := pc, stack := inline52Entry q rho} =
      some {s with pc := pcAfter pc inline52Template, stack := inline52WordStack q (PairedLaneWordRound.wordStep 3 14 14 (inline52Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline52Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 14 14 q.a q.b q.c q.d q.e
        (inline52Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      ((congrArg (rawT (inline52Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline52Frame s.memory q) 3 14 14 hfactor hpair hupper rfl rfl))
  have hout : inline52Output q (singleT (inline52Frame s.memory q) (inline3Boolean q)) rho =
      inline52WordStack q
        (PairedLaneWordRound.wordStep 3 14 14 (inline52Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline52Output, inline52WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline52Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline52Template, stack := vs}) hout)

#print axioms run_inline52Template_word

def inline53Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 18}

def inline53Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline53Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline53WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline53Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline53Template_length

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

#print axioms run_inline53Template_raw

theorem run_inline53Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline53Template {s with pc := pc, stack := inline53Entry q rho} =
      some {s with pc := pcAfter pc inline53Template, stack := inline53Output q (inlineT (inline53Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline53Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline53Template

theorem run_inline53Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline53Template {s with pc := pc, stack := inline53Entry q rho} =
      some {s with pc := pcAfter pc inline53Template, stack := inline53WordStack q (PairedLaneWordRound.wordStep 3 15 14 (inline53Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline53Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 15 14 q.a q.b q.c q.d q.e
        (inline53Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline53Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline53Frame s.memory q) 3 15 14 hfactor hpair hupper rfl rfl))
  have hout : inline53Output q (inlineT (inline53Frame s.memory q) (inline3Boolean q)) rho =
      inline53WordStack q
        (PairedLaneWordRound.wordStep 3 15 14 (inline53Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline53Output, inline53WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline53Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline53Template, stack := vs}) hout)

#print axioms run_inline53Template_word

def inline54Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline54Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline54Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline54WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline54Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline54Template_length

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

#print axioms run_inline54Template_raw

theorem run_inline54Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline54Template {s with pc := pc, stack := inline54Entry q rho} =
      some {s with pc := pcAfter pc inline54Template, stack := inline54Output q (inlineT (inline54Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline54Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline54Template

theorem run_inline54Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline54Template {s with pc := pc, stack := inline54Entry q rho} =
      some {s with pc := pcAfter pc inline54Template, stack := inline54WordStack q (PairedLaneWordRound.wordStep 3 9 6 (inline54Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline54Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 9 6 q.a q.b q.c q.d q.e
        (inline54Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline54Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline54Frame s.memory q) 3 9 6 hfactor hpair hupper rfl rfl))
  have hout : inline54Output q (inlineT (inline54Frame s.memory q) (inline3Boolean q)) rho =
      inline54WordStack q
        (PairedLaneWordRound.wordStep 3 9 6 (inline54Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline54Output, inline54WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline54Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline54Template, stack := vs}) hout)

#print axioms run_inline54Template_word

def inline55Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 18}

def inline55Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline55Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline55WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline55Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline55Template_length

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

#print axioms run_inline55Template_raw

theorem run_inline55Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline55Template {s with pc := pc, stack := inline55Entry q rho} =
      some {s with pc := pcAfter pc inline55Template, stack := inline55Output q (inlineT (inline55Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline55Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline55Template

theorem run_inline55Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline55Template {s with pc := pc, stack := inline55Entry q rho} =
      some {s with pc := pcAfter pc inline55Template, stack := inline55WordStack q (PairedLaneWordRound.wordStep 3 8 14 (inline55Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline55Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 8 14 q.a q.b q.c q.d q.e
        (inline55Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline55Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline55Frame s.memory q) 3 8 14 hfactor hpair hupper rfl rfl))
  have hout : inline55Output q (inlineT (inline55Frame s.memory q) (inline3Boolean q)) rho =
      inline55WordStack q
        (PairedLaneWordRound.wordStep 3 8 14 (inline55Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline55Output, inline55WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline55Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline55Template, stack := vs}) hout)

#print axioms run_inline55Template_word

def inline56Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline56Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline56Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline56WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline56Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline56Template_length

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

#print axioms run_inline56Template_raw

theorem run_inline56Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline56Template {s with pc := pc, stack := inline56Entry q rho} =
      some {s with pc := pcAfter pc inline56Template, stack := inline56Output q (inlineT (inline56Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline56Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline56Template

theorem run_inline56Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline56Template {s with pc := pc, stack := inline56Entry q rho} =
      some {s with pc := pcAfter pc inline56Template, stack := inline56WordStack q (PairedLaneWordRound.wordStep 3 9 6 (inline56Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline56Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 9 6 q.a q.b q.c q.d q.e
        (inline56Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline56Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline56Frame s.memory q) 3 9 6 hfactor hpair hupper rfl rfl))
  have hout : inline56Output q (inlineT (inline56Frame s.memory q) (inline3Boolean q)) rho =
      inline56WordStack q
        (PairedLaneWordRound.wordStep 3 9 6 (inline56Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline56Output, inline56WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline56Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline56Template, stack := vs}) hout)

#print axioms run_inline56Template_word

def inline57Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 23}

def inline57Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline57Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline57WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline57Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline57Template_length

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

#print axioms run_inline57Template_raw

theorem run_inline57Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline57Template {s with pc := pc, stack := inline57Entry q rho} =
      some {s with pc := pcAfter pc inline57Template, stack := inline57Output q (inlineT (inline57Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline57Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline57Template

theorem run_inline57Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline57Template {s with pc := pc, stack := inline57Entry q rho} =
      some {s with pc := pcAfter pc inline57Template, stack := inline57WordStack q (PairedLaneWordRound.wordStep 3 14 9 (inline57Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline57Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 14 9 q.a q.b q.c q.d q.e
        (inline57Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline57Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline57Frame s.memory q) 3 14 9 hfactor hpair hupper rfl rfl))
  have hout : inline57Output q (inlineT (inline57Frame s.memory q) (inline3Boolean q)) rho =
      inline57WordStack q
        (PairedLaneWordRound.wordStep 3 14 9 (inline57Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline57Output, inline57WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline57Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline57Template, stack := vs}) hout)

#print axioms run_inline57Template_word

def inline58Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 20}

def inline58Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline58Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline58WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline58Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline58Template_length

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

#print axioms run_inline58Template_raw

theorem run_inline58Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline58Template {s with pc := pc, stack := inline58Entry q rho} =
      some {s with pc := pcAfter pc inline58Template, stack := inline58Output q (inlineT (inline58Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline58Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline58Template

theorem run_inline58Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline58Template {s with pc := pc, stack := inline58Entry q rho} =
      some {s with pc := pcAfter pc inline58Template, stack := inline58WordStack q (PairedLaneWordRound.wordStep 3 5 12 (inline58Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline58Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 5 12 q.a q.b q.c q.d q.e
        (inline58Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline58Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline58Frame s.memory q) 3 5 12 hfactor hpair hupper rfl rfl))
  have hout : inline58Output q (inlineT (inline58Frame s.memory q) (inline3Boolean q)) rho =
      inline58WordStack q
        (PairedLaneWordRound.wordStep 3 5 12 (inline58Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline58Output, inline58WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline58Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline58Template, stack := vs}) hout)

#print axioms run_inline58Template_word

def inline59Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 23}

def inline59Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline59Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline59WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline59Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline59Template_length

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

#print axioms run_inline59Template_raw

theorem run_inline59Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline59Template {s with pc := pc, stack := inline59Entry q rho} =
      some {s with pc := pcAfter pc inline59Template, stack := inline59Output q (inlineT (inline59Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline59Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline59Template

theorem run_inline59Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline59Template {s with pc := pc, stack := inline59Entry q rho} =
      some {s with pc := pcAfter pc inline59Template, stack := inline59WordStack q (PairedLaneWordRound.wordStep 3 6 9 (inline59Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline59Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 6 9 q.a q.b q.c q.d q.e
        (inline59Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline59Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline59Frame s.memory q) 3 6 9 hfactor hpair hupper rfl rfl))
  have hout : inline59Output q (inlineT (inline59Frame s.memory q) (inline3Boolean q)) rho =
      inline59WordStack q
        (PairedLaneWordRound.wordStep 3 6 9 (inline59Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline59Output, inline59WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline59Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline59Template, stack := vs}) hout)

#print axioms run_inline59Template_word

def inline60Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 20}

def inline60Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline60Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline60WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline60Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline60Template_length

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

#print axioms run_inline60Template_raw

theorem run_inline60Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline60Template {s with pc := pc, stack := inline60Entry q rho} =
      some {s with pc := pcAfter pc inline60Template, stack := inline60Output q (inlineT (inline60Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline60Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline60Template

theorem run_inline60Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline60Template {s with pc := pc, stack := inline60Entry q rho} =
      some {s with pc := pcAfter pc inline60Template, stack := inline60WordStack q (PairedLaneWordRound.wordStep 3 8 12 (inline60Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline60Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 8 12 q.a q.b q.c q.d q.e
        (inline60Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline60Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline60Frame s.memory q) 3 8 12 hfactor hpair hupper rfl rfl))
  have hout : inline60Output q (inlineT (inline60Frame s.memory q) (inline3Boolean q)) rho =
      inline60WordStack q
        (PairedLaneWordRound.wordStep 3 8 12 (inline60Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline60Output, inline60WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline60Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline60Template, stack := vs}) hout)

#print axioms run_inline60Template_word

def inline61Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 27}

def inline61Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline61Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline61WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline61Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline61Template_length

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

#print axioms run_inline61Template_raw

theorem run_inline61Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline61Template {s with pc := pc, stack := inline61Entry q rho} =
      some {s with pc := pcAfter pc inline61Template, stack := inline61Output q (inlineT (inline61Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline61Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline61Template

theorem run_inline61Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline61Template {s with pc := pc, stack := inline61Entry q rho} =
      some {s with pc := pcAfter pc inline61Template, stack := inline61WordStack q (PairedLaneWordRound.wordStep 3 6 5 (inline61Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline61Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 6 5 q.a q.b q.c q.d q.e
        (inline61Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline61Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline61Frame s.memory q) 3 6 5 hfactor hpair hupper rfl rfl))
  have hout : inline61Output q (inlineT (inline61Frame s.memory q) (inline3Boolean q)) rho =
      inline61WordStack q
        (PairedLaneWordRound.wordStep 3 6 5 (inline61Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline61Output, inline61WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline61Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline61Template, stack := vs}) hout)

#print axioms run_inline61Template_word

def inline62Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 17}

def inline62Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline62Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline62WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.e, state.c, state.b, q.k, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline62Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline62Template_length

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

#print axioms run_inline62Template_raw

theorem run_inline62Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline62Template {s with pc := pc, stack := inline62Entry q rho} =
      some {s with pc := pcAfter pc inline62Template, stack := inline62Output q (inlineT (inline62Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline62Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline62Template

theorem run_inline62Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline62Template {s with pc := pc, stack := inline62Entry q rho} =
      some {s with pc := pcAfter pc inline62Template, stack := inline62WordStack q (PairedLaneWordRound.wordStep 3 5 15 (inline62Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline62Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 5 15 q.a q.b q.c q.d q.e
        (inline62Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline62Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline62Frame s.memory q) 3 5 15 hfactor hpair hupper rfl rfl))
  have hout : inline62Output q (inlineT (inline62Frame s.memory q) (inline3Boolean q)) rho =
      inline62WordStack q
        (PairedLaneWordRound.wordStep 3 5 15 (inline62Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline62Output, inline62WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline62Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline62Template, stack := vs}) hout)

#print axioms run_inline62Template_word

def inline63Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 24}

def inline63Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.k, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline63Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.k, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline63WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.a, state.b, state.c, q.k, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline63Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .op (.Dup ⟨4, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline63Template_length

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

#print axioms run_inline63Template_raw

theorem run_inline63Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline63Template {s with pc := pc, stack := inline63Entry q rho} =
      some {s with pc := pcAfter pc inline63Template, stack := inline63Output q (inlineT (inline63Frame s.memory q) (inline3Boolean q)) rho} := by
  simpa only [threeRaw_eq_inline3Boolean] using
    run_inline63Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline63Template

theorem run_inline63Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline63Template {s with pc := pc, stack := inline63Entry q rho} =
      some {s with pc := pcAfter pc inline63Template, stack := inline63WordStack q (PairedLaneWordRound.wordStep 3 12 8 (inline63Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline63Frame s.memory q) (inline3Boolean q) =
      PairedLaneWordRound.wordT 3 12 8 q.a q.b q.c q.d q.e
        (inline63Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline63Frame s.memory q)) (inline3Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline63Frame s.memory q) 3 12 8 hfactor hpair hupper rfl rfl))
  have hout : inline63Output q (inlineT (inline63Frame s.memory q) (inline3Boolean q)) rho =
      inline63WordStack q
        (PairedLaneWordRound.wordStep 3 12 8 (inline63Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline63Output, inline63WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline63Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline63Template, stack := vs}) hout)




#print axioms run_inline63Template_word

def inline64Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 24}

def inline64Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline64Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline64WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline64Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline64Template_length

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

#print axioms run_inline64Template_raw

theorem run_inline64Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline64Template {s with pc := pc, stack := inline64Entry q rho} =
      some {s with pc := pcAfter pc inline64Template, stack := inline64Output q (inlineT (inline64Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline64Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline64Template

theorem run_inline64Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline64Template {s with pc := pc, stack := inline64Entry q rho} =
      some {s with pc := pcAfter pc inline64Template, stack := inline64WordStack q (PairedLaneWordRound.wordStep 4 9 8 (inline64Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline64Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 9 8 q.a q.b q.c q.d q.e
        (inline64Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline64Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline64Frame s.memory q) 4 9 8 hfactor hpair hupper rfl rfl))
  have hout : inline64Output q (inlineT (inline64Frame s.memory q) (inline4Boolean q)) rho =
      inline64WordStack q
        (PairedLaneWordRound.wordStep 4 9 8 (inline64Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline64Output, inline64WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline64Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline64Template, stack := vs}) hout)

#print axioms run_inline64Template_word

def inline65Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 27}

def inline65Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline65Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline65WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline65Template_length : inline65Template.length = 46 := rfl

#print axioms inline65Template_length

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

#print axioms run_inline65Template_raw

theorem run_inline65Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline65Template {s with pc := pc, stack := inline65Entry q rho} =
      some {s with pc := pcAfter pc inline65Template, stack := inline65Output q (inlineT (inline65Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline65Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline65Template

theorem run_inline65Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline65Template {s with pc := pc, stack := inline65Entry q rho} =
      some {s with pc := pcAfter pc inline65Template, stack := inline65WordStack q (PairedLaneWordRound.wordStep 4 15 5 (inline65Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline65Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 15 5 q.a q.b q.c q.d q.e
        (inline65Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline65Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline65Frame s.memory q) 4 15 5 hfactor hpair hupper rfl rfl))
  have hout : inline65Output q (inlineT (inline65Frame s.memory q) (inline4Boolean q)) rho =
      inline65WordStack q
        (PairedLaneWordRound.wordStep 4 15 5 (inline65Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline65Output, inline65WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline65Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline65Template, stack := vs}) hout)

#print axioms run_inline65Template_word

def inline66Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 20}

def inline66Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline66Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline66WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline66Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline66Template_length

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

#print axioms run_inline66Template_raw

theorem run_inline66Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline66Template {s with pc := pc, stack := inline66Entry q rho} =
      some {s with pc := pcAfter pc inline66Template, stack := inline66Output q (inlineT (inline66Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline66Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline66Template

theorem run_inline66Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline66Template {s with pc := pc, stack := inline66Entry q rho} =
      some {s with pc := pcAfter pc inline66Template, stack := inline66WordStack q (PairedLaneWordRound.wordStep 4 5 12 (inline66Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline66Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 5 12 q.a q.b q.c q.d q.e
        (inline66Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline66Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline66Frame s.memory q) 4 5 12 hfactor hpair hupper rfl rfl))
  have hout : inline66Output q (inlineT (inline66Frame s.memory q) (inline4Boolean q)) rho =
      inline66WordStack q
        (PairedLaneWordRound.wordStep 4 5 12 (inline66Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline66Output, inline66WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline66Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline66Template, stack := vs}) hout)

#print axioms run_inline66Template_word

def inline67Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 23}

def inline67Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline67Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline67WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline67Template_length : inline67Template.length = 46 := rfl

#print axioms inline67Template_length

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

#print axioms run_inline67Template_raw

theorem run_inline67Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline67Template {s with pc := pc, stack := inline67Entry q rho} =
      some {s with pc := pcAfter pc inline67Template, stack := inline67Output q (inlineT (inline67Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline67Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline67Template

theorem run_inline67Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline67Template {s with pc := pc, stack := inline67Entry q rho} =
      some {s with pc := pcAfter pc inline67Template, stack := inline67WordStack q (PairedLaneWordRound.wordStep 4 11 9 (inline67Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline67Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 11 9 q.a q.b q.c q.d q.e
        (inline67Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline67Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline67Frame s.memory q) 4 11 9 hfactor hpair hupper rfl rfl))
  have hout : inline67Output q (inlineT (inline67Frame s.memory q) (inline4Boolean q)) rho =
      inline67WordStack q
        (PairedLaneWordRound.wordStep 4 11 9 (inline67Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline67Output, inline67WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline67Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline67Template, stack := vs}) hout)

#print axioms run_inline67Template_word

def inline68Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 20}

def inline68Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline68Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline68WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline68Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline68Template_length

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

#print axioms run_inline68Template_raw

theorem run_inline68Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline68Template {s with pc := pc, stack := inline68Entry q rho} =
      some {s with pc := pcAfter pc inline68Template, stack := inline68Output q (inlineT (inline68Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline68Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline68Template

theorem run_inline68Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline68Template {s with pc := pc, stack := inline68Entry q rho} =
      some {s with pc := pcAfter pc inline68Template, stack := inline68WordStack q (PairedLaneWordRound.wordStep 4 6 12 (inline68Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline68Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 6 12 q.a q.b q.c q.d q.e
        (inline68Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline68Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline68Frame s.memory q) 4 6 12 hfactor hpair hupper rfl rfl))
  have hout : inline68Output q (inlineT (inline68Frame s.memory q) (inline4Boolean q)) rho =
      inline68WordStack q
        (PairedLaneWordRound.wordStep 4 6 12 (inline68Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline68Output, inline68WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline68Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline68Template, stack := vs}) hout)

#print axioms run_inline68Template_word

def inline69Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 27}

def inline69Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline69Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline69WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline69Template_length : inline69Template.length = 46 := rfl

#print axioms inline69Template_length

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

#print axioms run_inline69Template_raw

theorem run_inline69Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline69Template {s with pc := pc, stack := inline69Entry q rho} =
      some {s with pc := pcAfter pc inline69Template, stack := inline69Output q (inlineT (inline69Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline69Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline69Template

theorem run_inline69Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline69Template {s with pc := pc, stack := inline69Entry q rho} =
      some {s with pc := pcAfter pc inline69Template, stack := inline69WordStack q (PairedLaneWordRound.wordStep 4 8 5 (inline69Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline69Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 8 5 q.a q.b q.c q.d q.e
        (inline69Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline69Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline69Frame s.memory q) 4 8 5 hfactor hpair hupper rfl rfl))
  have hout : inline69Output q (inlineT (inline69Frame s.memory q) (inline4Boolean q)) rho =
      inline69WordStack q
        (PairedLaneWordRound.wordStep 4 8 5 (inline69Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline69Output, inline69WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline69Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline69Template, stack := vs}) hout)

#print axioms run_inline69Template_word

def inline70Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 18}

def inline70Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline70Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline70WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline70Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline70Template_length

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

#print axioms run_inline70Template_raw

theorem run_inline70Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline70Template {s with pc := pc, stack := inline70Entry q rho} =
      some {s with pc := pcAfter pc inline70Template, stack := inline70Output q (inlineT (inline70Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline70Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline70Template

theorem run_inline70Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline70Template {s with pc := pc, stack := inline70Entry q rho} =
      some {s with pc := pcAfter pc inline70Template, stack := inline70WordStack q (PairedLaneWordRound.wordStep 4 13 14 (inline70Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline70Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 13 14 q.a q.b q.c q.d q.e
        (inline70Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline70Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline70Frame s.memory q) 4 13 14 hfactor hpair hupper rfl rfl))
  have hout : inline70Output q (inlineT (inline70Frame s.memory q) (inline4Boolean q)) rho =
      inline70WordStack q
        (PairedLaneWordRound.wordStep 4 13 14 (inline70Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline70Output, inline70WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline70Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline70Template, stack := vs}) hout)

#print axioms run_inline70Template_word

def inline71Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 26}

def inline71Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline71Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline71WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline71Template_length : inline71Template.length = 46 := rfl

#print axioms inline71Template_length

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

#print axioms run_inline71Template_raw

theorem run_inline71Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline71Template {s with pc := pc, stack := inline71Entry q rho} =
      some {s with pc := pcAfter pc inline71Template, stack := inline71Output q (inlineT (inline71Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline71Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline71Template

theorem run_inline71Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline71Template {s with pc := pc, stack := inline71Entry q rho} =
      some {s with pc := pcAfter pc inline71Template, stack := inline71WordStack q (PairedLaneWordRound.wordStep 4 12 6 (inline71Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline71Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 12 6 q.a q.b q.c q.d q.e
        (inline71Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline71Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline71Frame s.memory q) 4 12 6 hfactor hpair hupper rfl rfl))
  have hout : inline71Output q (inlineT (inline71Frame s.memory q) (inline4Boolean q)) rho =
      inline71WordStack q
        (PairedLaneWordRound.wordStep 4 12 6 (inline71Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline71Output, inline71WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline71Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline71Template, stack := vs}) hout)

#print axioms run_inline71Template_word

def inline72Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 24}

def inline72Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline72Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline72WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline72Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline72Template_length

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

#print axioms run_inline72Template_raw

theorem run_inline72Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline72Template {s with pc := pc, stack := inline72Entry q rho} =
      some {s with pc := pcAfter pc inline72Template, stack := inline72Output q (inlineT (inline72Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline72Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline72Template

theorem run_inline72Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline72Template {s with pc := pc, stack := inline72Entry q rho} =
      some {s with pc := pcAfter pc inline72Template, stack := inline72WordStack q (PairedLaneWordRound.wordStep 4 5 8 (inline72Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline72Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 5 8 q.a q.b q.c q.d q.e
        (inline72Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline72Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline72Frame s.memory q) 4 5 8 hfactor hpair hupper rfl rfl))
  have hout : inline72Output q (inlineT (inline72Frame s.memory q) (inline4Boolean q)) rho =
      inline72WordStack q
        (PairedLaneWordRound.wordStep 4 5 8 (inline72Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline72Output, inline72WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline72Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline72Template, stack := vs}) hout)

#print axioms run_inline72Template_word

def inline73Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 19}

def inline73Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline73Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline73WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline73Template_length : inline73Template.length = 47 := rfl

#print axioms inline73Template_length

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

#print axioms run_inline73Template_raw

theorem run_inline73Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline73Template {s with pc := pc, stack := inline73Entry q rho} =
      some {s with pc := pcAfter pc inline73Template, stack := inline73Output q (inlineT (inline73Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline73Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline73Template

theorem run_inline73Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline73Template {s with pc := pc, stack := inline73Entry q rho} =
      some {s with pc := pcAfter pc inline73Template, stack := inline73WordStack q (PairedLaneWordRound.wordStep 4 12 13 (inline73Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline73Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 12 13 q.a q.b q.c q.d q.e
        (inline73Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline73Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline73Frame s.memory q) 4 12 13 hfactor hpair hupper rfl rfl))
  have hout : inline73Output q (inlineT (inline73Frame s.memory q) (inline4Boolean q)) rho =
      inline73WordStack q
        (PairedLaneWordRound.wordStep 4 12 13 (inline73Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline73Output, inline73WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline73Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline73Template, stack := vs}) hout)

#print axioms run_inline73Template_word

def inline74Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 26}

def inline74Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline74Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline74WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline74Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline74Template_length

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

#print axioms run_inline74Template_raw

theorem run_inline74Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline74Template {s with pc := pc, stack := inline74Entry q rho} =
      some {s with pc := pcAfter pc inline74Template, stack := inline74Output q (inlineT (inline74Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline74Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline74Template

theorem run_inline74Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline74Template {s with pc := pc, stack := inline74Entry q rho} =
      some {s with pc := pcAfter pc inline74Template, stack := inline74WordStack q (PairedLaneWordRound.wordStep 4 13 6 (inline74Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline74Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 13 6 q.a q.b q.c q.d q.e
        (inline74Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline74Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline74Frame s.memory q) 4 13 6 hfactor hpair hupper rfl rfl))
  have hout : inline74Output q (inlineT (inline74Frame s.memory q) (inline4Boolean q)) rho =
      inline74WordStack q
        (PairedLaneWordRound.wordStep 4 13 6 (inline74Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline74Output, inline74WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline74Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline74Template, stack := vs}) hout)

#print axioms run_inline74Template_word

def inline75Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 27}

def inline75Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline75Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline75WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline75Template_length : inline75Template.length = 46 := rfl

#print axioms inline75Template_length

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

#print axioms run_inline75Template_raw

theorem run_inline75Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline75Template {s with pc := pc, stack := inline75Entry q rho} =
      some {s with pc := pcAfter pc inline75Template, stack := inline75Output q (inlineT (inline75Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline75Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline75Template

theorem run_inline75Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline75Template {s with pc := pc, stack := inline75Entry q rho} =
      some {s with pc := pcAfter pc inline75Template, stack := inline75WordStack q (PairedLaneWordRound.wordStep 4 14 5 (inline75Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline75Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 14 5 q.a q.b q.c q.d q.e
        (inline75Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline75Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline75Frame s.memory q) 4 14 5 hfactor hpair hupper rfl rfl))
  have hout : inline75Output q (inlineT (inline75Frame s.memory q) (inline4Boolean q)) rho =
      inline75WordStack q
        (PairedLaneWordRound.wordStep 4 14 5 (inline75Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline75Output, inline75WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline75Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline75Template, stack := vs}) hout)

#print axioms run_inline75Template_word

def inline76Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 17}

def inline76Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline76Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline76WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline76Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline76Template_length

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

#print axioms run_inline76Template_raw

theorem run_inline76Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline76Template {s with pc := pc, stack := inline76Entry q rho} =
      some {s with pc := pcAfter pc inline76Template, stack := inline76Output q (inlineT (inline76Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline76Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline76Template

theorem run_inline76Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline76Template {s with pc := pc, stack := inline76Entry q rho} =
      some {s with pc := pcAfter pc inline76Template, stack := inline76WordStack q (PairedLaneWordRound.wordStep 4 11 15 (inline76Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline76Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 11 15 q.a q.b q.c q.d q.e
        (inline76Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline76Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline76Frame s.memory q) 4 11 15 hfactor hpair hupper rfl rfl))
  have hout : inline76Output q (inlineT (inline76Frame s.memory q) (inline4Boolean q)) rho =
      inline76WordStack q
        (PairedLaneWordRound.wordStep 4 11 15 (inline76Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline76Output, inline76WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline76Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline76Template, stack := vs}) hout)

#print axioms run_inline76Template_word

def inline77Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 19}

def inline77Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline77Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline77WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op .XOR,
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

theorem inline77Template_length : inline77Template.length = 47 := rfl

#print axioms inline77Template_length

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

#print axioms run_inline77Template_raw

theorem run_inline77Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline77Template {s with pc := pc, stack := inline77Entry q rho} =
      some {s with pc := pcAfter pc inline77Template, stack := inline77Output q (inlineT (inline77Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline77Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline77Template

theorem run_inline77Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline77Template {s with pc := pc, stack := inline77Entry q rho} =
      some {s with pc := pcAfter pc inline77Template, stack := inline77WordStack q (PairedLaneWordRound.wordStep 4 8 13 (inline77Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline77Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 8 13 q.a q.b q.c q.d q.e
        (inline77Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline77Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline77Frame s.memory q) 4 8 13 hfactor hpair hupper rfl rfl))
  have hout : inline77Output q (inlineT (inline77Frame s.memory q) (inline4Boolean q)) rho =
      inline77WordStack q
        (PairedLaneWordRound.wordStep 4 8 13 (inline77Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline77Output, inline77WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline77Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline77Template, stack := vs}) hout)

#print axioms run_inline77Template_word

def inline78Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 21}

def inline78Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline78Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline78WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, q.k, state.c, state.b, state.e, state.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline78Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
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

#print axioms inline78Template_length

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

#print axioms run_inline78Template_raw

theorem run_inline78Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline78Template {s with pc := pc, stack := inline78Entry q rho} =
      some {s with pc := pcAfter pc inline78Template, stack := inline78Output q (inlineT (inline78Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline78Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline78Template

theorem run_inline78Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline78Template {s with pc := pc, stack := inline78Entry q rho} =
      some {s with pc := pcAfter pc inline78Template, stack := inline78WordStack q (PairedLaneWordRound.wordStep 4 5 11 (inline78Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline78Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 5 11 q.a q.b q.c q.d q.e
        (inline78Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline78Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline78Frame s.memory q) 4 5 11 hfactor hpair hupper rfl rfl))
  have hout : inline78Output q (inlineT (inline78Frame s.memory q) (inline4Boolean q)) rho =
      inline78WordStack q
        (PairedLaneWordRound.wordStep 4 5 11 (inline78Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline78Output, inline78WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline78Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline78Template, stack := vs}) hout)

#print axioms run_inline78Template_word

def inline79Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 21}

def inline79Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline79Output (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline79WordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND]

theorem inline79Template_length : inline79Template.length = 46 := rfl

#print axioms inline79Template_length

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
  refine ⟨rfl, rfl, ?_⟩
  let post (v : UInt256) : UInt256 :=
    let product := UInt256.mul q.factor (UInt256.land q.pair v)
    UInt256.land q.pair (UInt256.add q.e
      (UInt256.xor
        (UInt256.land q.upper
          (UInt256.xor (UInt256.shiftRight product (UInt256.ofNat 26))
            (UInt256.shiftRight product (UInt256.ofNat 21))))
        (UInt256.shiftRight product (UInt256.ofNat 26))))
  let sum := UInt256.add (inline79Frame s.memory q).message0 (UInt256.add (fourRaw q) q.a)
  change post (UInt256.add sum q.k) = post (UInt256.add q.k sum)
  exact congrArg post (Challenge.EvmProof.Word.word_add_comm sum q.k)

#print axioms run_inline79Template_raw

theorem run_inline79Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline79Template {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc inline79Template, stack := inline79Output q (inlineT (inline79Frame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_inline79Template_raw s pc q rho hstack hrun hactive

#print axioms run_inline79Template

theorem run_inline79Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq inline79Template {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc inline79Template, stack := inline79WordStack q (PairedLaneWordRound.wordStep 4 6 11 (inline79Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline79Frame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 6 11 q.a q.b q.c q.d q.e
        (inline79Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline79Frame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (inline79Frame s.memory q) 4 6 11 hfactor hpair hupper rfl rfl))
  have hout : inline79Output q (inlineT (inline79Frame s.memory q) (inline4Boolean q)) rho =
      inline79WordStack q
        (PairedLaneWordRound.wordStep 4 6 11 (inline79Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline79Output, inline79WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline79Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline79Template, stack := vs}) hout)

#print axioms run_inline79Template_word



/- The all-inline core has no internal JUMP and needs no helper destination premise. -/

structure CoreBlock (start finish : Nat) (input output : List CoreReg) where
  code : List Instr
  eval : ByteArray → CoreFrame → CoreFrame
  run : ∀ (s : State) (f : CoreFrame) (rho : List UInt256),
    rho.length ≤ 1002 → s.halt = .Running → 23 ≤ s.activeWords.toNat →
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
    (hactive : 23 ≤ s.activeWords.toNat)  :
    runInstrSeq chain.code {s with pc := UInt256.ofNat a, stack := coreStack xs f rho} =
      some {s with pc := UInt256.ofNat b, stack := coreStack ys (chain.eval s.memory f) rho} := by
  induction chain generalizing f with
  | nil => rfl
  | cons block tail ih =>
    have h0 := block.run s f rho hstack hrun hactive
    have h1 := ih (block.eval s.memory f)
    exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1





#print axioms CoreChain.run

def group0Template : List Instr :=
  PairedFactoredGroupConstants.upperTemplate

def group0Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group0Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 460344169260758029377710773882198039553172832256, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group0Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group0Template {s with pc := pc, stack := group0Entry q rho} =
      some {s with pc := pcAfter pc group0Template, stack := group0Output q rho} := by
  have h := PairedFactoredGroupConstants.run_upperTemplate s pc (group0Entry q rho)
    (by simp only [group0Entry, List.length_append, List.length_cons, List.length_nil]; omega) hrun
  simpa only [group0Template, group0Entry, group0Output, List.cons_append, List.nil_append] using h


#print axioms run_group0Template

def group16Template : List Instr :=
  groupK_materialize16Template

def group16Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group16Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 526962527014005041256681316140890030896371104153, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group16Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group16Template {s with pc := pc, stack := group16Entry q rho} =
      some {s with pc := pcAfter pc group16Template, stack := group16Output q rho} := by
  have h := groupK_run_materialize16Template s pc (group16Entry q rho)
    (by simp only [group16Entry, List.length_append, List.length_cons, List.length_nil]; omega) hrun
  simpa only [group16Template, group16Entry, group16Output, List.cons_append, List.nil_append] using h

#print axioms run_group16Template

def group32Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .push ⟨21, by decide⟩ (UInt256.ofNat 2086284798122997420139349764661223671126594022305)]

def group32Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group32Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 2086284798122997420139349764661223671126594022305, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

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

def group48Template : List Instr :=
  groupK_materialize48Template

def group48Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group48Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 698938013802679700166637234969497128417458109660, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group48Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group48Template {s with pc := pc, stack := group48Entry q rho} =
      some {s with pc := pcAfter pc group48Template, stack := group48Output q rho} := by
  have h := groupK_run_materialize48Template s pc (group48Entry q rho)
    (by simp only [group48Entry, List.length_append, List.length_cons, List.length_nil]; omega) hrun
  simpa only [group48Template, group48Entry, group48Output, List.cons_append, List.nil_append] using h

#print axioms run_group48Template

def group64Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .push ⟨4, by decide⟩ (UInt256.ofNat 2840853838)]

def group64Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.k, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group64Output (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 2840853838, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group64Template (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group64Template {s with pc := pc, stack := group64Entry q rho} =
      some {s with pc := pcAfter pc group64Template, stack := group64Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group64Template, group64Entry, group64Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl

#print axioms run_group64Template



theorem group0Template_pc : pcAfter (UInt256.ofNat 769) group0Template = UInt256.ofNat 777 := rfl

#print axioms group0Template_pc

def group0Block : CoreBlock 769 777 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group0Template
  eval := fun _memory f => {f with k := UInt256.ofNat 460344169260758029377710773882198039553172832256}
  run := by
    intro s f rho hstack hrun _hactive
    have h := run_group0Template s (UInt256.ofNat 769) f.frame rho hstack hrun
    rw [group0Template_pc] at h
    exact h

theorem inline0Template_pc : pcAfter (UInt256.ofNat 777) PairedSynthCoreTrace.inline0Template = UInt256.ofNat 829 := rfl

#print axioms inline0Template_pc

def inline0Block : CoreBlock 777 829 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline0Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 11 8 (PairedHelperBooleanTrace.inline0Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline0Template_word s (UInt256.ofNat 777) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline0Template_pc] at h
    exact h

theorem inline1Template_pc : pcAfter (UInt256.ofNat 829) PairedSynthCoreTrace.inline1Template = UInt256.ofNat 881 := rfl

#print axioms inline1Template_pc

def inline1Block : CoreBlock 829 881 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline1Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 14 9 (PairedHelperBooleanTrace.inline1Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline1Template_word s (UInt256.ofNat 829) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline1Template_pc] at h
    exact h

theorem inline2Template_pc : pcAfter (UInt256.ofNat 881) PairedSynthCoreTrace.inline2Template = UInt256.ofNat 934 := rfl

#print axioms inline2Template_pc

def inline2Block : CoreBlock 881 934 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline2Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 15 9 (PairedHelperBooleanTrace.inline2Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline2Template_word s (UInt256.ofNat 881) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline2Template_pc] at h
    exact h

theorem inline3Template_pc : pcAfter (UInt256.ofNat 934) PairedSynthCoreTrace.inline3Template = UInt256.ofNat 986 := rfl

#print axioms inline3Template_pc

def inline3Block : CoreBlock 934 986 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline3Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 12 11 (PairedHelperBooleanTrace.inline3Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline3Template_word s (UInt256.ofNat 934) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline3Template_pc] at h
    exact h

theorem inline4Template_pc : pcAfter (UInt256.ofNat 986) PairedSynthCoreTrace.inline4Template = UInt256.ofNat 1040 := rfl

#print axioms inline4Template_pc

def inline4Block : CoreBlock 986 1040 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline4Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 5 13 (PairedHelperBooleanTrace.inline4Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline4Template_word s (UInt256.ofNat 986) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline4Template_pc] at h
    exact h

theorem inline5Template_pc : pcAfter (UInt256.ofNat 1040) PairedSynthCoreTrace.inline5Template = UInt256.ofNat 1094 := rfl

#print axioms inline5Template_pc

def inline5Block : CoreBlock 1040 1094 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline5Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 8 15 (PairedHelperBooleanTrace.inline5Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline5Template_word s (UInt256.ofNat 1040) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline5Template_pc] at h
    exact h

theorem inline6Template_pc : pcAfter (UInt256.ofNat 1094) PairedSynthCoreTrace.inline6Template = UInt256.ofNat 1148 := rfl

#print axioms inline6Template_pc

def inline6Block : CoreBlock 1094 1148 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline6Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 7 15 (PairedHelperBooleanTrace.inline6Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline6Template_word s (UInt256.ofNat 1094) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline6Template_pc] at h
    exact h

theorem inline7Template_pc : pcAfter (UInt256.ofNat 1148) PairedSynthCoreTrace.inline7Template = UInt256.ofNat 1201 := rfl

#print axioms inline7Template_pc

def inline7Block : CoreBlock 1148 1201 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline7Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 9 5 (PairedHelperBooleanTrace.inline7Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline7Template_word s (UInt256.ofNat 1148) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline7Template_pc] at h
    exact h

theorem inline8Template_pc : pcAfter (UInt256.ofNat 1201) PairedSynthCoreTrace.inline8Template = UInt256.ofNat 1254 := rfl

#print axioms inline8Template_pc

def inline8Block : CoreBlock 1201 1254 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline8Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 11 7 (PairedHelperBooleanTrace.inline8Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline8Template_word s (UInt256.ofNat 1201) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline8Template_pc] at h
    exact h

theorem inline9Template_pc : pcAfter (UInt256.ofNat 1254) PairedSynthCoreTrace.inline9Template = UInt256.ofNat 1307 := rfl

#print axioms inline9Template_pc

def inline9Block : CoreBlock 1254 1307 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline9Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 13 7 (PairedHelperBooleanTrace.inline9Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline9Template_word s (UInt256.ofNat 1254) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline9Template_pc] at h
    exact h

theorem inline10Template_pc : pcAfter (UInt256.ofNat 1307) PairedSynthCoreTrace.inline10Template = UInt256.ofNat 1360 := rfl

#print axioms inline10Template_pc

def inline10Block : CoreBlock 1307 1360 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline10Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 14 8 (PairedHelperBooleanTrace.inline10Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline10Template_word s (UInt256.ofNat 1307) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline10Template_pc] at h
    exact h

theorem inline11Template_pc : pcAfter (UInt256.ofNat 1360) PairedSynthCoreTrace.inline11Template = UInt256.ofNat 1413 := rfl

#print axioms inline11Template_pc

def inline11Block : CoreBlock 1360 1413 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline11Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 15 11 (PairedHelperBooleanTrace.inline11Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline11Template_word s (UInt256.ofNat 1360) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline11Template_pc] at h
    exact h

theorem inline12Template_pc : pcAfter (UInt256.ofNat 1413) PairedSynthCoreTrace.inline12Template = UInt256.ofNat 1466 := rfl

#print axioms inline12Template_pc

def inline12Block : CoreBlock 1413 1466 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline12Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 6 14 (PairedHelperBooleanTrace.inline12Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline12Template_word s (UInt256.ofNat 1413) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline12Template_pc] at h
    exact h

theorem inline13Template_pc : pcAfter (UInt256.ofNat 1466) PairedSynthCoreTrace.inline13Template = UInt256.ofNat 1520 := rfl

#print axioms inline13Template_pc

def inline13Block : CoreBlock 1466 1520 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline13Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 7 14 (PairedHelperBooleanTrace.inline13Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline13Template_word s (UInt256.ofNat 1466) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline13Template_pc] at h
    exact h

theorem inline14Template_pc : pcAfter (UInt256.ofNat 1520) PairedSynthCoreTrace.inline14Template = UInt256.ofNat 1574 := rfl

#print axioms inline14Template_pc

def inline14Block : CoreBlock 1520 1574 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline14Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 9 12 (PairedHelperBooleanTrace.inline14Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline14Template_word s (UInt256.ofNat 1520) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline14Template_pc] at h
    exact h

theorem inline15Template_pc : pcAfter (UInt256.ofNat 1574) groupK_consumed15Template = UInt256.ofNat 1626 := rfl

#print axioms inline15Template_pc

def inline15Block : CoreBlock 1574 1626 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := groupK_consumed15Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 8 6 (PairedHelperBooleanTrace.inline15Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := groupK_run_consumed15Template_word s (UInt256.ofNat 1574) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline15Template_pc] at h
    exact h

theorem group16Template_pc : pcAfter (UInt256.ofNat 1626) group16Template = UInt256.ofNat 1640 := rfl

#print axioms group16Template_pc

def group16Block : CoreBlock 1626 1640 [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := group16Template
  eval := fun _memory f => {f with k := UInt256.ofNat 526962527014005041256681316140890030896371104153}
  run := by
    intro s f rho hstack hrun _hactive
    have h := run_group16Template s (UInt256.ofNat 1626) f.frame rho hstack hrun
    rw [group16Template_pc] at h
    exact h

theorem inline16Template_pc : pcAfter (UInt256.ofNat 1640) PairedAllInlineNewPairs.inline16Template = UInt256.ofNat 1696 := rfl

#print axioms inline16Template_pc

def inline16Block : CoreBlock 1640 1696 [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline16Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 9 (PairedAllInlineNewPairs.inline16Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline16Template_word s (UInt256.ofNat 1640) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline16Template_pc] at h
    exact h

theorem inline17Template_pc : pcAfter (UInt256.ofNat 1696) PairedAllInlineNewPairs.inline17Template = UInt256.ofNat 1752 := rfl

#print axioms inline17Template_pc

def inline17Block : CoreBlock 1696 1752 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline17Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 6 13 (PairedAllInlineNewPairs.inline17Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline17Template_word s (UInt256.ofNat 1696) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline17Template_pc] at h
    exact h

theorem inline18Template_pc : pcAfter (UInt256.ofNat 1752) inline18Template = UInt256.ofNat 1808 := rfl

#print axioms inline18Template_pc

def inline18Block : CoreBlock 1752 1808 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline18Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 8 15 (inline18Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline18Template_word s (UInt256.ofNat 1752) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline18Template_pc] at h
    exact h

theorem inline19Template_pc : pcAfter (UInt256.ofNat 1808) inline19Template = UInt256.ofNat 1862 := rfl

#print axioms inline19Template_pc

def inline19Block : CoreBlock 1808 1862 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline19Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 13 7 (inline19Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline19Template_word s (UInt256.ofNat 1808) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline19Template_pc] at h
    exact h

theorem inline20Template_pc : pcAfter (UInt256.ofNat 1862) inline20Template = UInt256.ofNat 1917 := rfl

#print axioms inline20Template_pc

def inline20Block : CoreBlock 1862 1917 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline20Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 11 12 (inline20Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline20Template_word s (UInt256.ofNat 1862) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline20Template_pc] at h
    exact h

theorem inline21Template_pc : pcAfter (UInt256.ofNat 1917) inline21Template = UInt256.ofNat 1972 := rfl

#print axioms inline21Template_pc

def inline21Block : CoreBlock 1917 1972 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline21Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 9 8 (inline21Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline21Template_word s (UInt256.ofNat 1917) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline21Template_pc] at h
    exact h

theorem inline22Template_pc : pcAfter (UInt256.ofNat 1972) inline22Template = UInt256.ofNat 2028 := rfl

#print axioms inline22Template_pc

def inline22Block : CoreBlock 1972 2028 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline22Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 9 (inline22Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline22Template_word s (UInt256.ofNat 1972) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline22Template_pc] at h
    exact h

theorem inline23Template_pc : pcAfter (UInt256.ofNat 2028) inline23Template = UInt256.ofNat 2083 := rfl

#print axioms inline23Template_pc

def inline23Block : CoreBlock 2028 2083 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline23Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 15 11 (inline23Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline23Template_word s (UInt256.ofNat 2028) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline23Template_pc] at h
    exact h

theorem inline24Template_pc : pcAfter (UInt256.ofNat 2083) inline24Template = UInt256.ofNat 2129 := rfl

#print axioms inline24Template_pc

def inline24Block : CoreBlock 2083 2129 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline24Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 7 (inline24Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline24Template_word s (UInt256.ofNat 2083) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline24Template_pc] at h
    exact h

theorem inline25Template_pc : pcAfter (UInt256.ofNat 2129) inline25Template = UInt256.ofNat 2183 := rfl

#print axioms inline25Template_pc

def inline25Block : CoreBlock 2129 2183 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline25Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 12 7 (inline25Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline25Template_word s (UInt256.ofNat 2129) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline25Template_pc] at h
    exact h

theorem inline26Template_pc : pcAfter (UInt256.ofNat 2183) inline26Template = UInt256.ofNat 2238 := rfl

#print axioms inline26Template_pc

def inline26Block : CoreBlock 2183 2238 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline26Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 15 12 (inline26Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline26Template_word s (UInt256.ofNat 2183) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline26Template_pc] at h
    exact h

theorem inline27Template_pc : pcAfter (UInt256.ofNat 2238) inline27Template = UInt256.ofNat 2293 := rfl

#print axioms inline27Template_pc

def inline27Block : CoreBlock 2238 2293 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline27Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 9 7 (inline27Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline27Template_word s (UInt256.ofNat 2238) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline27Template_pc] at h
    exact h

theorem inline28Template_pc : pcAfter (UInt256.ofNat 2293) PairedAllInlineNewPairs.inline28Template = UInt256.ofNat 2348 := rfl

#print axioms inline28Template_pc

def inline28Block : CoreBlock 2293 2348 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline28Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 11 6 (PairedAllInlineNewPairs.inline28Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline28Template_word s (UInt256.ofNat 2293) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline28Template_pc] at h
    exact h

theorem inline29Template_pc : pcAfter (UInt256.ofNat 2348) PairedAllInlineNewPairs.inline29Template = UInt256.ofNat 2404 := rfl

#print axioms inline29Template_pc

def inline29Block : CoreBlock 2348 2404 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline29Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 15 (PairedAllInlineNewPairs.inline29Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline29Template_word s (UInt256.ofNat 2348) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline29Template_pc] at h
    exact h

theorem inline30Template_pc : pcAfter (UInt256.ofNat 2404) inline30Template = UInt256.ofNat 2449 := rfl

#print axioms inline30Template_pc

def inline30Block : CoreBlock 2404 2449 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline30Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 13 13 (inline30Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline30Template_word s (UInt256.ofNat 2404) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline30Template_pc] at h
    exact h

theorem inline31Template_pc : pcAfter (UInt256.ofNat 2449) inline31Template = UInt256.ofNat 2504 := rfl

#print axioms inline31Template_pc

def inline31Block : CoreBlock 2449 2504 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline31Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 12 11 (inline31Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline31Template_word s (UInt256.ofNat 2449) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline31Template_pc] at h
    exact h

theorem group32Template_pc : pcAfter (UInt256.ofNat 2504) group32Template = UInt256.ofNat 2528 := rfl

#print axioms group32Template_pc

def group32Block : CoreBlock 2504 2528 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group32Template
  eval := fun _memory f => {f with k := UInt256.ofNat 2086284798122997420139349764661223671126594022305}
  run := by
    intro s f rho hstack hrun _hactive
    have h := run_group32Template s (UInt256.ofNat 2504) f.frame rho hstack hrun
    rw [group32Template_pc] at h
    exact h

theorem inline32Template_pc : pcAfter (UInt256.ofNat 2528) inline32Template = UInt256.ofNat 2576 := rfl

#print axioms inline32Template_pc

def inline32Block : CoreBlock 2528 2576 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline32Template
  eval := fun memory f => {f with lane := rawWordStep2 11 9 (inline32Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline32Template_word s (UInt256.ofNat 2528) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline32Template_pc] at h
    exact h

theorem inline33Template_pc : pcAfter (UInt256.ofNat 2576) inline33Template = UInt256.ofNat 2624 := rfl

#print axioms inline33Template_pc

def inline33Block : CoreBlock 2576 2624 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline33Template
  eval := fun memory f => {f with lane := rawWordStep2 13 7 (inline33Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline33Template_word s (UInt256.ofNat 2576) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline33Template_pc] at h
    exact h

theorem inline34Template_pc : pcAfter (UInt256.ofNat 2624) inline34Template = UInt256.ofNat 2672 := rfl

#print axioms inline34Template_pc

def inline34Block : CoreBlock 2624 2672 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline34Template
  eval := fun memory f => {f with lane := rawWordStep2 6 15 (inline34Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline34Template_word s (UInt256.ofNat 2624) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline34Template_pc] at h
    exact h

theorem inline35Template_pc : pcAfter (UInt256.ofNat 2672) inline35Template = UInt256.ofNat 2721 := rfl

#print axioms inline35Template_pc

def inline35Block : CoreBlock 2672 2721 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline35Template
  eval := fun memory f => {f with lane := rawWordStep2 7 11 (inline35Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline35Template_word s (UInt256.ofNat 2672) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline35Template_pc] at h
    exact h

theorem inline36Template_pc : pcAfter (UInt256.ofNat 2721) inline36Template = UInt256.ofNat 2769 := rfl

#print axioms inline36Template_pc

def inline36Block : CoreBlock 2721 2769 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline36Template
  eval := fun memory f => {f with lane := rawWordStep2 14 8 (inline36Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline36Template_word s (UInt256.ofNat 2721) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline36Template_pc] at h
    exact h

theorem inline37Template_pc : pcAfter (UInt256.ofNat 2769) inline37Template = UInt256.ofNat 2817 := rfl

#print axioms inline37Template_pc

def inline37Block : CoreBlock 2769 2817 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline37Template
  eval := fun memory f => {f with lane := rawWordStep2 9 6 (inline37Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline37Template_word s (UInt256.ofNat 2769) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline37Template_pc] at h
    exact h

theorem inline38Template_pc : pcAfter (UInt256.ofNat 2817) inline38Template = UInt256.ofNat 2865 := rfl

#print axioms inline38Template_pc

def inline38Block : CoreBlock 2817 2865 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline38Template
  eval := fun memory f => {f with lane := rawWordStep2 13 6 (inline38Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline38Template_word s (UInt256.ofNat 2817) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline38Template_pc] at h
    exact h

theorem inline39Template_pc : pcAfter (UInt256.ofNat 2865) inline39Template = UInt256.ofNat 2912 := rfl

#print axioms inline39Template_pc

def inline39Block : CoreBlock 2865 2912 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline39Template
  eval := fun memory f => {f with lane := rawWordStep2 15 14 (inline39Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline39Template_word s (UInt256.ofNat 2865) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline39Template_pc] at h
    exact h

theorem inline40Template_pc : pcAfter (UInt256.ofNat 2912) inline40Template = UInt256.ofNat 2960 := rfl

#print axioms inline40Template_pc

def inline40Block : CoreBlock 2912 2960 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline40Template
  eval := fun memory f => {f with lane := rawWordStep2 14 12 (inline40Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline40Template_word s (UInt256.ofNat 2912) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline40Template_pc] at h
    exact h

theorem inline41Template_pc : pcAfter (UInt256.ofNat 2960) inline41Template = UInt256.ofNat 3009 := rfl

#print axioms inline41Template_pc

def inline41Block : CoreBlock 2960 3009 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline41Template
  eval := fun memory f => {f with lane := rawWordStep2 8 13 (inline41Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline41Template_word s (UInt256.ofNat 2960) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline41Template_pc] at h
    exact h

theorem inline42Template_pc : pcAfter (UInt256.ofNat 3009) inline42Template = UInt256.ofNat 3056 := rfl

#print axioms inline42Template_pc

def inline42Block : CoreBlock 3009 3056 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline42Template
  eval := fun memory f => {f with lane := rawWordStep2 13 5 (inline42Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline42Template_word s (UInt256.ofNat 3009) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline42Template_pc] at h
    exact h

theorem inline43Template_pc : pcAfter (UInt256.ofNat 3056) inline43Template = UInt256.ofNat 3105 := rfl

#print axioms inline43Template_pc

def inline43Block : CoreBlock 3056 3105 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline43Template
  eval := fun memory f => {f with lane := rawWordStep2 6 14 (inline43Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline43Template_word s (UInt256.ofNat 3056) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline43Template_pc] at h
    exact h

theorem inline44Template_pc : pcAfter (UInt256.ofNat 3105) inline44Template = UInt256.ofNat 3154 := rfl

#print axioms inline44Template_pc

def inline44Block : CoreBlock 3105 3154 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline44Template
  eval := fun memory f => {f with lane := rawWordStep2 5 13 (inline44Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline44Template_word s (UInt256.ofNat 3105) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline44Template_pc] at h
    exact h

theorem inline45Template_pc : pcAfter (UInt256.ofNat 3154) inline45Template = UInt256.ofNat 3202 := rfl

#print axioms inline45Template_pc

def inline45Block : CoreBlock 3154 3202 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline45Template
  eval := fun memory f => {f with lane := rawWordStep2 12 13 (inline45Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline45Template_word s (UInt256.ofNat 3154) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline45Template_pc] at h
    exact h

theorem inline46Template_pc : pcAfter (UInt256.ofNat 3202) inline46Template = UInt256.ofNat 3241 := rfl

#print axioms inline46Template_pc

def inline46Block : CoreBlock 3202 3241 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline46Template
  eval := fun memory f => {f with lane := rawWordStep2 7 7 (inline46Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline46Template_word s (UInt256.ofNat 3202) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline46Template_pc] at h
    exact h

theorem inline47Template_pc : pcAfter (UInt256.ofNat 3241) groupK_consumed47Template = UInt256.ofNat 3279 := rfl

#print axioms inline47Template_pc

def inline47Block : CoreBlock 3241 3279 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := groupK_consumed47Template
  eval := fun memory f => {f with lane := rawWordStep2 5 5 (inline47Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := groupK_run_consumed47Template_word s (UInt256.ofNat 3241) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline47Template_pc] at h
    exact h

theorem group48Template_pc : pcAfter (UInt256.ofNat 3279) group48Template = UInt256.ofNat 3300 := rfl

#print axioms group48Template_pc

def group48Block : CoreBlock 3279 3300 [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := group48Template
  eval := fun _memory f => {f with k := UInt256.ofNat 698938013802679700166637234969497128417458109660}
  run := by
    intro s f rho hstack hrun _hactive
    have h := run_group48Template s (UInt256.ofNat 3279) f.frame rho hstack hrun
    rw [group48Template_pc] at h
    exact h

theorem inline48Template_pc : pcAfter (UInt256.ofNat 3300) inline48Template = UInt256.ofNat 3355 := rfl

#print axioms inline48Template_pc

def inline48Block : CoreBlock 3300 3355 [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline48Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 11 15 (inline48Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline48Template_word s (UInt256.ofNat 3300) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline48Template_pc] at h
    exact h

theorem inline49Template_pc : pcAfter (UInt256.ofNat 3355) inline49Template = UInt256.ofNat 3410 := rfl

#print axioms inline49Template_pc

def inline49Block : CoreBlock 3355 3410 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline49Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 12 5 (inline49Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline49Template_word s (UInt256.ofNat 3355) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline49Template_pc] at h
    exact h

theorem inline50Template_pc : pcAfter (UInt256.ofNat 3410) inline50Template = UInt256.ofNat 3465 := rfl

#print axioms inline50Template_pc

def inline50Block : CoreBlock 3410 3465 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline50Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 8 (inline50Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline50Template_word s (UInt256.ofNat 3410) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline50Template_pc] at h
    exact h

theorem inline51Template_pc : pcAfter (UInt256.ofNat 3465) inline51Template = UInt256.ofNat 3519 := rfl

#print axioms inline51Template_pc

def inline51Block : CoreBlock 3465 3519 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline51Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 15 11 (inline51Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline51Template_word s (UInt256.ofNat 3465) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline51Template_pc] at h
    exact h

theorem inline52Template_pc : pcAfter (UInt256.ofNat 3519) inline52Template = UInt256.ofNat 3564 := rfl

#print axioms inline52Template_pc

def inline52Block : CoreBlock 3519 3564 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline52Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 14 (inline52Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline52Template_word s (UInt256.ofNat 3519) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline52Template_pc] at h
    exact h

theorem inline53Template_pc : pcAfter (UInt256.ofNat 3564) inline53Template = UInt256.ofNat 3619 := rfl

#print axioms inline53Template_pc

def inline53Block : CoreBlock 3564 3619 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline53Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 15 14 (inline53Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline53Template_word s (UInt256.ofNat 3564) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline53Template_pc] at h
    exact h

theorem inline54Template_pc : pcAfter (UInt256.ofNat 3619) inline54Template = UInt256.ofNat 3674 := rfl

#print axioms inline54Template_pc

def inline54Block : CoreBlock 3619 3674 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline54Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 9 6 (inline54Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline54Template_word s (UInt256.ofNat 3619) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline54Template_pc] at h
    exact h

theorem inline55Template_pc : pcAfter (UInt256.ofNat 3674) inline55Template = UInt256.ofNat 3729 := rfl

#print axioms inline55Template_pc

def inline55Block : CoreBlock 3674 3729 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline55Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 8 14 (inline55Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline55Template_word s (UInt256.ofNat 3674) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline55Template_pc] at h
    exact h

theorem inline56Template_pc : pcAfter (UInt256.ofNat 3729) inline56Template = UInt256.ofNat 3784 := rfl

#print axioms inline56Template_pc

def inline56Block : CoreBlock 3729 3784 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline56Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 9 6 (inline56Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline56Template_word s (UInt256.ofNat 3729) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline56Template_pc] at h
    exact h

theorem inline57Template_pc : pcAfter (UInt256.ofNat 3784) inline57Template = UInt256.ofNat 3839 := rfl

#print axioms inline57Template_pc

def inline57Block : CoreBlock 3784 3839 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline57Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 9 (inline57Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline57Template_word s (UInt256.ofNat 3784) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline57Template_pc] at h
    exact h

theorem inline58Template_pc : pcAfter (UInt256.ofNat 3839) inline58Template = UInt256.ofNat 3895 := rfl

#print axioms inline58Template_pc

def inline58Block : CoreBlock 3839 3895 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline58Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 5 12 (inline58Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline58Template_word s (UInt256.ofNat 3839) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline58Template_pc] at h
    exact h

theorem inline59Template_pc : pcAfter (UInt256.ofNat 3895) inline59Template = UInt256.ofNat 3951 := rfl

#print axioms inline59Template_pc

def inline59Block : CoreBlock 3895 3951 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline59Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 6 9 (inline59Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline59Template_word s (UInt256.ofNat 3895) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline59Template_pc] at h
    exact h

theorem inline60Template_pc : pcAfter (UInt256.ofNat 3951) inline60Template = UInt256.ofNat 4007 := rfl

#print axioms inline60Template_pc

def inline60Block : CoreBlock 3951 4007 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline60Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 8 12 (inline60Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline60Template_word s (UInt256.ofNat 3951) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline60Template_pc] at h
    exact h

theorem inline61Template_pc : pcAfter (UInt256.ofNat 4007) inline61Template = UInt256.ofNat 4062 := rfl

#print axioms inline61Template_pc

def inline61Block : CoreBlock 4007 4062 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline61Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 6 5 (inline61Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline61Template_word s (UInt256.ofNat 4007) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline61Template_pc] at h
    exact h

theorem inline62Template_pc : pcAfter (UInt256.ofNat 4062) inline62Template = UInt256.ofNat 4118 := rfl

#print axioms inline62Template_pc

def inline62Block : CoreBlock 4062 4118 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := inline62Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 5 15 (inline62Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline62Template_word s (UInt256.ofNat 4062) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline62Template_pc] at h
    exact h

theorem inline63Template_pc : pcAfter (UInt256.ofNat 4118) inline63Template = UInt256.ofNat 4173 := rfl

#print axioms inline63Template_pc

def inline63Block : CoreBlock 4118 4173 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := inline63Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 12 8 (inline63Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline63Template_word s (UInt256.ofNat 4118) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline63Template_pc] at h
    exact h

theorem group64Template_pc : pcAfter (UInt256.ofNat 4173) group64Template = UInt256.ofNat 4180 := rfl

#print axioms group64Template_pc

def group64Block : CoreBlock 4173 4180 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group64Template
  eval := fun _memory f => {f with k := UInt256.ofNat 2840853838}
  run := by
    intro s f rho hstack hrun _hactive
    have h := run_group64Template s (UInt256.ofNat 4173) f.frame rho hstack hrun
    rw [group64Template_pc] at h
    exact h

theorem inline64Template_pc : pcAfter (UInt256.ofNat 4180) inline64Template = UInt256.ofNat 4233 := rfl

#print axioms inline64Template_pc

def inline64Block : CoreBlock 4180 4233 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline64Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 9 8 (inline64Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline64Template_word s (UInt256.ofNat 4180) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline64Template_pc] at h
    exact h

theorem inline65Template_pc : pcAfter (UInt256.ofNat 4233) inline65Template = UInt256.ofNat 4285 := rfl

#print axioms inline65Template_pc

def inline65Block : CoreBlock 4233 4285 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline65Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 15 5 (inline65Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline65Template_word s (UInt256.ofNat 4233) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline65Template_pc] at h
    exact h

theorem inline66Template_pc : pcAfter (UInt256.ofNat 4285) inline66Template = UInt256.ofNat 4339 := rfl

#print axioms inline66Template_pc

def inline66Block : CoreBlock 4285 4339 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline66Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 12 (inline66Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline66Template_word s (UInt256.ofNat 4285) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline66Template_pc] at h
    exact h

theorem inline67Template_pc : pcAfter (UInt256.ofNat 4339) inline67Template = UInt256.ofNat 4392 := rfl

#print axioms inline67Template_pc

def inline67Block : CoreBlock 4339 4392 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline67Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 11 9 (inline67Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline67Template_word s (UInt256.ofNat 4339) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline67Template_pc] at h
    exact h

theorem inline68Template_pc : pcAfter (UInt256.ofNat 4392) inline68Template = UInt256.ofNat 4445 := rfl

#print axioms inline68Template_pc

def inline68Block : CoreBlock 4392 4445 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline68Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 6 12 (inline68Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline68Template_word s (UInt256.ofNat 4392) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline68Template_pc] at h
    exact h

theorem inline69Template_pc : pcAfter (UInt256.ofNat 4445) inline69Template = UInt256.ofNat 4498 := rfl

#print axioms inline69Template_pc

def inline69Block : CoreBlock 4445 4498 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline69Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 8 5 (inline69Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline69Template_word s (UInt256.ofNat 4445) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline69Template_pc] at h
    exact h

theorem inline70Template_pc : pcAfter (UInt256.ofNat 4498) inline70Template = UInt256.ofNat 4552 := rfl

#print axioms inline70Template_pc

def inline70Block : CoreBlock 4498 4552 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline70Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 13 14 (inline70Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline70Template_word s (UInt256.ofNat 4498) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline70Template_pc] at h
    exact h

theorem inline71Template_pc : pcAfter (UInt256.ofNat 4552) inline71Template = UInt256.ofNat 4605 := rfl

#print axioms inline71Template_pc

def inline71Block : CoreBlock 4552 4605 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline71Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 12 6 (inline71Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline71Template_word s (UInt256.ofNat 4552) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline71Template_pc] at h
    exact h

theorem inline72Template_pc : pcAfter (UInt256.ofNat 4605) inline72Template = UInt256.ofNat 4659 := rfl

#print axioms inline72Template_pc

def inline72Block : CoreBlock 4605 4659 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline72Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 8 (inline72Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline72Template_word s (UInt256.ofNat 4605) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline72Template_pc] at h
    exact h

theorem inline73Template_pc : pcAfter (UInt256.ofNat 4659) inline73Template = UInt256.ofNat 4712 := rfl

#print axioms inline73Template_pc

def inline73Block : CoreBlock 4659 4712 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline73Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 12 13 (inline73Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline73Template_word s (UInt256.ofNat 4659) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline73Template_pc] at h
    exact h

theorem inline74Template_pc : pcAfter (UInt256.ofNat 4712) inline74Template = UInt256.ofNat 4765 := rfl

#print axioms inline74Template_pc

def inline74Block : CoreBlock 4712 4765 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline74Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 13 6 (inline74Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline74Template_word s (UInt256.ofNat 4712) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline74Template_pc] at h
    exact h

theorem inline75Template_pc : pcAfter (UInt256.ofNat 4765) inline75Template = UInt256.ofNat 4818 := rfl

#print axioms inline75Template_pc

def inline75Block : CoreBlock 4765 4818 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline75Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 14 5 (inline75Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline75Template_word s (UInt256.ofNat 4765) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline75Template_pc] at h
    exact h

theorem inline76Template_pc : pcAfter (UInt256.ofNat 4818) inline76Template = UInt256.ofNat 4871 := rfl

#print axioms inline76Template_pc

def inline76Block : CoreBlock 4818 4871 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline76Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 11 15 (inline76Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline76Template_word s (UInt256.ofNat 4818) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline76Template_pc] at h
    exact h

theorem inline77Template_pc : pcAfter (UInt256.ofNat 4871) inline77Template = UInt256.ofNat 4925 := rfl

#print axioms inline77Template_pc

def inline77Block : CoreBlock 4871 4925 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline77Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 8 13 (inline77Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline77Template_word s (UInt256.ofNat 4871) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline77Template_pc] at h
    exact h

theorem inline78Template_pc : pcAfter (UInt256.ofNat 4925) inline78Template = UInt256.ofNat 4979 := rfl

#print axioms inline78Template_pc

def inline78Block : CoreBlock 4925 4979 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline78Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 11 (inline78Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline78Template_word s (UInt256.ofNat 4925) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline78Template_pc] at h
    exact h

theorem inline79Template_pc : pcAfter (UInt256.ofNat 4979) inline79Template = UInt256.ofNat 5032 := rfl

#print axioms inline79Template_pc

def inline79Block : CoreBlock 4979 5032 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline79Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 6 11 (inline79Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive
    have h := run_inline79Template_word s (UInt256.ofNat 4979) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline79Template_pc] at h
    exact h

def wholeCoreChain : CoreChain 769 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] 5032 [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] :=
  .cons group0Block (
  .cons inline0Block (
  .cons inline1Block (
  .cons inline2Block (
  .cons inline3Block (
  .cons inline4Block (
  .cons inline5Block (
  .cons inline6Block (
  .cons inline7Block (
  .cons inline8Block (
  .cons inline9Block (
  .cons inline10Block (
  .cons inline11Block (
  .cons inline12Block (
  .cons inline13Block (
  .cons inline14Block (
  .cons inline15Block (
  .cons group16Block (
  .cons inline16Block (
  .cons inline17Block (
  .cons inline18Block (
  .cons inline19Block (
  .cons inline20Block (
  .cons inline21Block (
  .cons inline22Block (
  .cons inline23Block (
  .cons inline24Block (
  .cons inline25Block (
  .cons inline26Block (
  .cons inline27Block (
  .cons inline28Block (
  .cons inline29Block (
  .cons inline30Block (
  .cons inline31Block (
  .cons group32Block (
  .cons inline32Block (
  .cons inline33Block (
  .cons inline34Block (
  .cons inline35Block (
  .cons inline36Block (
  .cons inline37Block (
  .cons inline38Block (
  .cons inline39Block (
  .cons inline40Block (
  .cons inline41Block (
  .cons inline42Block (
  .cons inline43Block (
  .cons inline44Block (
  .cons inline45Block (
  .cons inline46Block (
  .cons inline47Block (
  .cons group48Block (
  .cons inline48Block (
  .cons inline49Block (
  .cons inline50Block (
  .cons inline51Block (
  .cons inline52Block (
  .cons inline53Block (
  .cons inline54Block (
  .cons inline55Block (
  .cons inline56Block (
  .cons inline57Block (
  .cons inline58Block (
  .cons inline59Block (
  .cons inline60Block (
  .cons inline61Block (
  .cons inline62Block (
  .cons inline63Block (
  .cons group64Block (
  .cons inline64Block (
  .cons inline65Block (
  .cons inline66Block (
  .cons inline67Block (
  .cons inline68Block (
  .cons inline69Block (
  .cons inline70Block (
  .cons inline71Block (
  .cons inline72Block (
  .cons inline73Block (
  .cons inline74Block (
  .cons inline75Block (
  .cons inline76Block (
  .cons inline77Block (
  .cons inline78Block (
  .cons inline79Block (
  .nil 5032 [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem run_wholeCoreChain (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)  :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho} =
      some {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (wholeCoreChain.eval s.memory f) rho} :=
  wholeCoreChain.run s f rho hstack hrun hactive

#print axioms run_wholeCoreChain

theorem group0Block_eval (memory : ByteArray) (f : CoreFrame) :
    group0Block.eval memory f = ⟨f.lane, physicalKey 0⟩ := rfl

#print axioms group0Block_eval

theorem inline0Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline0Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 0 q, physicalKey 0⟩ := rfl

#print axioms inline0Block_eval

theorem inline1Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline1Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 1 q, physicalKey 0⟩ := rfl

#print axioms inline1Block_eval

theorem inline2Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline2Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 2 q, physicalKey 0⟩ := rfl

#print axioms inline2Block_eval

theorem inline3Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline3Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 3 q, physicalKey 0⟩ := rfl

#print axioms inline3Block_eval

theorem inline4Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline4Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 4 q, physicalKey 0⟩ := rfl

#print axioms inline4Block_eval

theorem inline5Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline5Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 5 q, physicalKey 0⟩ := rfl

#print axioms inline5Block_eval

theorem inline6Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline6Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 6 q, physicalKey 0⟩ := rfl

#print axioms inline6Block_eval

theorem inline7Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline7Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 7 q, physicalKey 0⟩ := rfl

#print axioms inline7Block_eval

theorem inline8Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline8Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 8 q, physicalKey 0⟩ := rfl

#print axioms inline8Block_eval

theorem inline9Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline9Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 9 q, physicalKey 0⟩ := rfl

#print axioms inline9Block_eval

theorem inline10Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline10Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 10 q, physicalKey 0⟩ := rfl

#print axioms inline10Block_eval

theorem inline11Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline11Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 11 q, physicalKey 0⟩ := rfl

#print axioms inline11Block_eval

theorem inline12Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline12Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 12 q, physicalKey 0⟩ := rfl

#print axioms inline12Block_eval

theorem inline13Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline13Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 13 q, physicalKey 0⟩ := rfl

#print axioms inline13Block_eval

theorem inline14Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline14Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 14 q, physicalKey 0⟩ := rfl

#print axioms inline14Block_eval

theorem inline15Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline15Block.eval memory ⟨q, physicalKey 0⟩ =
      ⟨hoistedAlgorithmStep memory 15 q, physicalKey 0⟩ := rfl

#print axioms inline15Block_eval

theorem group16Block_eval (memory : ByteArray) (f : CoreFrame) :
    group16Block.eval memory f = ⟨f.lane, physicalKey 1⟩ := rfl

#print axioms group16Block_eval

theorem inline16Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline16Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 16 q, physicalKey 1⟩ := rfl

#print axioms inline16Block_eval

theorem inline17Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline17Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 17 q, physicalKey 1⟩ := rfl

#print axioms inline17Block_eval

theorem inline18Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline18Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 18 q, physicalKey 1⟩ := rfl

#print axioms inline18Block_eval

theorem inline19Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline19Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 19 q, physicalKey 1⟩ := rfl

#print axioms inline19Block_eval

theorem inline20Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline20Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 20 q, physicalKey 1⟩ := rfl

#print axioms inline20Block_eval

theorem inline21Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline21Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 21 q, physicalKey 1⟩ := rfl

#print axioms inline21Block_eval

theorem inline22Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline22Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 22 q, physicalKey 1⟩ := rfl

#print axioms inline22Block_eval

theorem inline23Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline23Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 23 q, physicalKey 1⟩ := rfl

#print axioms inline23Block_eval

theorem inline24Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline24Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 24 q, physicalKey 1⟩ := rfl

#print axioms inline24Block_eval

theorem inline25Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline25Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 25 q, physicalKey 1⟩ := rfl

#print axioms inline25Block_eval

theorem inline26Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline26Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 26 q, physicalKey 1⟩ := rfl

#print axioms inline26Block_eval

theorem inline27Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline27Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 27 q, physicalKey 1⟩ := rfl

#print axioms inline27Block_eval

theorem inline28Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline28Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 28 q, physicalKey 1⟩ := rfl

#print axioms inline28Block_eval

theorem inline29Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline29Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 29 q, physicalKey 1⟩ := rfl

#print axioms inline29Block_eval

theorem inline30Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline30Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 30 q, physicalKey 1⟩ := rfl

#print axioms inline30Block_eval

theorem inline31Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline31Block.eval memory ⟨q, physicalKey 1⟩ =
      ⟨hoistedAlgorithmStep memory 31 q, physicalKey 1⟩ := rfl

#print axioms inline31Block_eval

theorem group32Block_eval (memory : ByteArray) (f : CoreFrame) :
    group32Block.eval memory f = ⟨f.lane, physicalKey 2⟩ := by
  exact congrArg (fun k => CoreFrame.mk f.lane k) PairedSynthCoreTrace.physicalKey_two.symm

#print axioms group32Block_eval

theorem inline32Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline32Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 32 q, physicalKey 2⟩ := rfl

#print axioms inline32Block_eval

theorem inline33Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline33Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 33 q, physicalKey 2⟩ := rfl

#print axioms inline33Block_eval

theorem inline34Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline34Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 34 q, physicalKey 2⟩ := rfl

#print axioms inline34Block_eval

theorem inline35Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline35Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 35 q, physicalKey 2⟩ := rfl

#print axioms inline35Block_eval

theorem inline36Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline36Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 36 q, physicalKey 2⟩ := rfl

#print axioms inline36Block_eval

theorem inline37Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline37Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 37 q, physicalKey 2⟩ := rfl

#print axioms inline37Block_eval

theorem inline38Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline38Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 38 q, physicalKey 2⟩ := rfl

#print axioms inline38Block_eval

theorem inline39Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline39Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 39 q, physicalKey 2⟩ := rfl

#print axioms inline39Block_eval

theorem inline40Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline40Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 40 q, physicalKey 2⟩ := rfl

#print axioms inline40Block_eval

theorem inline41Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline41Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 41 q, physicalKey 2⟩ := rfl

#print axioms inline41Block_eval

theorem inline42Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline42Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 42 q, physicalKey 2⟩ := rfl

#print axioms inline42Block_eval

theorem inline43Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline43Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 43 q, physicalKey 2⟩ := rfl

#print axioms inline43Block_eval

theorem inline44Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline44Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 44 q, physicalKey 2⟩ := rfl

#print axioms inline44Block_eval

theorem inline45Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline45Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 45 q, physicalKey 2⟩ := rfl

#print axioms inline45Block_eval

theorem inline46Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline46Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 46 q, physicalKey 2⟩ := rfl

#print axioms inline46Block_eval

theorem inline47Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline47Block.eval memory ⟨q, physicalKey 2⟩ =
      ⟨hoistedAlgorithmStep memory 47 q, physicalKey 2⟩ := rfl

#print axioms inline47Block_eval

theorem group48Block_eval (memory : ByteArray) (f : CoreFrame) :
    group48Block.eval memory f = ⟨f.lane, physicalKey 3⟩ := rfl

#print axioms group48Block_eval

theorem inline48Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline48Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 48 q, physicalKey 3⟩ := rfl

#print axioms inline48Block_eval

theorem inline49Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline49Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 49 q, physicalKey 3⟩ := rfl

#print axioms inline49Block_eval

theorem inline50Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline50Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 50 q, physicalKey 3⟩ := rfl

#print axioms inline50Block_eval

theorem inline51Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline51Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 51 q, physicalKey 3⟩ := rfl

#print axioms inline51Block_eval

theorem inline52Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline52Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 52 q, physicalKey 3⟩ := rfl

#print axioms inline52Block_eval

theorem inline53Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline53Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 53 q, physicalKey 3⟩ := rfl

#print axioms inline53Block_eval

theorem inline54Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline54Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 54 q, physicalKey 3⟩ := rfl

#print axioms inline54Block_eval

theorem inline55Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline55Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 55 q, physicalKey 3⟩ := rfl

#print axioms inline55Block_eval

theorem inline56Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline56Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 56 q, physicalKey 3⟩ := rfl

#print axioms inline56Block_eval

theorem inline57Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline57Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 57 q, physicalKey 3⟩ := rfl

#print axioms inline57Block_eval

theorem inline58Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline58Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 58 q, physicalKey 3⟩ := rfl

#print axioms inline58Block_eval

theorem inline59Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline59Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 59 q, physicalKey 3⟩ := rfl

#print axioms inline59Block_eval

theorem inline60Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline60Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 60 q, physicalKey 3⟩ := rfl

#print axioms inline60Block_eval

theorem inline61Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline61Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 61 q, physicalKey 3⟩ := rfl

#print axioms inline61Block_eval

theorem inline62Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline62Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 62 q, physicalKey 3⟩ := rfl

#print axioms inline62Block_eval

theorem inline63Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline63Block.eval memory ⟨q, physicalKey 3⟩ =
      ⟨hoistedAlgorithmStep memory 63 q, physicalKey 3⟩ := rfl

#print axioms inline63Block_eval

theorem group64Block_eval (memory : ByteArray) (f : CoreFrame) :
    group64Block.eval memory f = ⟨f.lane, physicalKey 4⟩ := rfl

#print axioms group64Block_eval

theorem inline64Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline64Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 64 q, physicalKey 4⟩ := rfl

#print axioms inline64Block_eval

theorem inline65Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline65Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 65 q, physicalKey 4⟩ := rfl

#print axioms inline65Block_eval

theorem inline66Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline66Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 66 q, physicalKey 4⟩ := rfl

#print axioms inline66Block_eval

theorem inline67Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline67Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 67 q, physicalKey 4⟩ := rfl

#print axioms inline67Block_eval

theorem inline68Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline68Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 68 q, physicalKey 4⟩ := rfl

#print axioms inline68Block_eval

theorem inline69Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline69Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 69 q, physicalKey 4⟩ := rfl

#print axioms inline69Block_eval

theorem inline70Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline70Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 70 q, physicalKey 4⟩ := rfl

#print axioms inline70Block_eval

theorem inline71Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline71Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 71 q, physicalKey 4⟩ := rfl

#print axioms inline71Block_eval

theorem inline72Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline72Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 72 q, physicalKey 4⟩ := rfl

#print axioms inline72Block_eval

theorem inline73Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline73Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 73 q, physicalKey 4⟩ := rfl

#print axioms inline73Block_eval

theorem inline74Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline74Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 74 q, physicalKey 4⟩ := rfl

#print axioms inline74Block_eval

theorem inline75Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline75Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 75 q, physicalKey 4⟩ := rfl

#print axioms inline75Block_eval

theorem inline76Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline76Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 76 q, physicalKey 4⟩ := rfl

#print axioms inline76Block_eval

theorem inline77Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline77Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 77 q, physicalKey 4⟩ := rfl

#print axioms inline77Block_eval

theorem inline78Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline78Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 78 q, physicalKey 4⟩ := rfl

#print axioms inline78Block_eval

theorem inline79Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline79Block.eval memory ⟨q, physicalKey 4⟩ =
      ⟨hoistedAlgorithmStep memory 79 q, physicalKey 4⟩ := rfl

#print axioms inline79Block_eval



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

theorem wholeCoreChain_eval (memory : ByteArray) (f : CoreFrame) :
    wholeCoreChain.eval memory f =
      ⟨hoistedAlgorithmFold memory 0 80 f.lane, physicalKey 4⟩ := by
  let f0 : CoreFrame := f
  let f1 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 0 f.lane, physicalKey 0⟩
  let f2 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 1 f.lane, physicalKey 0⟩
  let f3 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 2 f.lane, physicalKey 0⟩
  let f4 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 3 f.lane, physicalKey 0⟩
  let f5 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 4 f.lane, physicalKey 0⟩
  let f6 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 5 f.lane, physicalKey 0⟩
  let f7 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 6 f.lane, physicalKey 0⟩
  let f8 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 7 f.lane, physicalKey 0⟩
  let f9 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 8 f.lane, physicalKey 0⟩
  let f10 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 9 f.lane, physicalKey 0⟩
  let f11 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 10 f.lane, physicalKey 0⟩
  let f12 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 11 f.lane, physicalKey 0⟩
  let f13 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 12 f.lane, physicalKey 0⟩
  let f14 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 13 f.lane, physicalKey 0⟩
  let f15 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 14 f.lane, physicalKey 0⟩
  let f16 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 15 f.lane, physicalKey 0⟩
  let f17 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 16 f.lane, physicalKey 0⟩
  let f18 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 16 f.lane, physicalKey 1⟩
  let f19 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 17 f.lane, physicalKey 1⟩
  let f20 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 18 f.lane, physicalKey 1⟩
  let f21 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 19 f.lane, physicalKey 1⟩
  let f22 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 20 f.lane, physicalKey 1⟩
  let f23 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 21 f.lane, physicalKey 1⟩
  let f24 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 22 f.lane, physicalKey 1⟩
  let f25 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 23 f.lane, physicalKey 1⟩
  let f26 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 24 f.lane, physicalKey 1⟩
  let f27 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 25 f.lane, physicalKey 1⟩
  let f28 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 26 f.lane, physicalKey 1⟩
  let f29 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 27 f.lane, physicalKey 1⟩
  let f30 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 28 f.lane, physicalKey 1⟩
  let f31 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 29 f.lane, physicalKey 1⟩
  let f32 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 30 f.lane, physicalKey 1⟩
  let f33 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 31 f.lane, physicalKey 1⟩
  let f34 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 32 f.lane, physicalKey 1⟩
  let f35 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 32 f.lane, physicalKey 2⟩
  let f36 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 33 f.lane, physicalKey 2⟩
  let f37 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 34 f.lane, physicalKey 2⟩
  let f38 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 35 f.lane, physicalKey 2⟩
  let f39 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 36 f.lane, physicalKey 2⟩
  let f40 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 37 f.lane, physicalKey 2⟩
  let f41 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 38 f.lane, physicalKey 2⟩
  let f42 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 39 f.lane, physicalKey 2⟩
  let f43 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 40 f.lane, physicalKey 2⟩
  let f44 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 41 f.lane, physicalKey 2⟩
  let f45 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 42 f.lane, physicalKey 2⟩
  let f46 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 43 f.lane, physicalKey 2⟩
  let f47 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 44 f.lane, physicalKey 2⟩
  let f48 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 45 f.lane, physicalKey 2⟩
  let f49 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 46 f.lane, physicalKey 2⟩
  let f50 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 47 f.lane, physicalKey 2⟩
  let f51 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 48 f.lane, physicalKey 2⟩
  let f52 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 48 f.lane, physicalKey 3⟩
  let f53 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 49 f.lane, physicalKey 3⟩
  let f54 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 50 f.lane, physicalKey 3⟩
  let f55 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 51 f.lane, physicalKey 3⟩
  let f56 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 52 f.lane, physicalKey 3⟩
  let f57 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 53 f.lane, physicalKey 3⟩
  let f58 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 54 f.lane, physicalKey 3⟩
  let f59 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 55 f.lane, physicalKey 3⟩
  let f60 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 56 f.lane, physicalKey 3⟩
  let f61 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 57 f.lane, physicalKey 3⟩
  let f62 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 58 f.lane, physicalKey 3⟩
  let f63 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 59 f.lane, physicalKey 3⟩
  let f64 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 60 f.lane, physicalKey 3⟩
  let f65 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 61 f.lane, physicalKey 3⟩
  let f66 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 62 f.lane, physicalKey 3⟩
  let f67 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 63 f.lane, physicalKey 3⟩
  let f68 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 64 f.lane, physicalKey 3⟩
  let f69 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 64 f.lane, physicalKey 4⟩
  let f70 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 65 f.lane, physicalKey 4⟩
  let f71 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 66 f.lane, physicalKey 4⟩
  let f72 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 67 f.lane, physicalKey 4⟩
  let f73 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 68 f.lane, physicalKey 4⟩
  let f74 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 69 f.lane, physicalKey 4⟩
  let f75 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 70 f.lane, physicalKey 4⟩
  let f76 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 71 f.lane, physicalKey 4⟩
  let f77 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 72 f.lane, physicalKey 4⟩
  let f78 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 73 f.lane, physicalKey 4⟩
  let f79 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 74 f.lane, physicalKey 4⟩
  let f80 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 75 f.lane, physicalKey 4⟩
  let f81 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 76 f.lane, physicalKey 4⟩
  let f82 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 77 f.lane, physicalKey 4⟩
  let f83 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 78 f.lane, physicalKey 4⟩
  let f84 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 79 f.lane, physicalKey 4⟩
  let f85 : CoreFrame := ⟨hoistedAlgorithmFold memory 0 80 f.lane, physicalKey 4⟩
  have h0 : group0Block.eval memory f0 = f1 := by
    exact group0Block_eval memory f0
  have h1 : inline0Block.eval memory f1 = f2 := by
    exact inline0Block_eval memory (hoistedAlgorithmFold memory 0 0 f.lane)
  have h2 : inline1Block.eval memory f2 = f3 := by
    exact inline1Block_eval memory (hoistedAlgorithmFold memory 0 1 f.lane)
  have h3 : inline2Block.eval memory f3 = f4 := by
    exact inline2Block_eval memory (hoistedAlgorithmFold memory 0 2 f.lane)
  have h4 : inline3Block.eval memory f4 = f5 := by
    exact inline3Block_eval memory (hoistedAlgorithmFold memory 0 3 f.lane)
  have h5 : inline4Block.eval memory f5 = f6 := by
    exact inline4Block_eval memory (hoistedAlgorithmFold memory 0 4 f.lane)
  have h6 : inline5Block.eval memory f6 = f7 := by
    exact inline5Block_eval memory (hoistedAlgorithmFold memory 0 5 f.lane)
  have h7 : inline6Block.eval memory f7 = f8 := by
    exact inline6Block_eval memory (hoistedAlgorithmFold memory 0 6 f.lane)
  have h8 : inline7Block.eval memory f8 = f9 := by
    exact inline7Block_eval memory (hoistedAlgorithmFold memory 0 7 f.lane)
  have h9 : inline8Block.eval memory f9 = f10 := by
    exact inline8Block_eval memory (hoistedAlgorithmFold memory 0 8 f.lane)
  have h10 : inline9Block.eval memory f10 = f11 := by
    exact inline9Block_eval memory (hoistedAlgorithmFold memory 0 9 f.lane)
  have h11 : inline10Block.eval memory f11 = f12 := by
    exact inline10Block_eval memory (hoistedAlgorithmFold memory 0 10 f.lane)
  have h12 : inline11Block.eval memory f12 = f13 := by
    exact inline11Block_eval memory (hoistedAlgorithmFold memory 0 11 f.lane)
  have h13 : inline12Block.eval memory f13 = f14 := by
    exact inline12Block_eval memory (hoistedAlgorithmFold memory 0 12 f.lane)
  have h14 : inline13Block.eval memory f14 = f15 := by
    exact inline13Block_eval memory (hoistedAlgorithmFold memory 0 13 f.lane)
  have h15 : inline14Block.eval memory f15 = f16 := by
    exact inline14Block_eval memory (hoistedAlgorithmFold memory 0 14 f.lane)
  have h16 : inline15Block.eval memory f16 = f17 := by
    exact inline15Block_eval memory (hoistedAlgorithmFold memory 0 15 f.lane)
  have h17 : group16Block.eval memory f17 = f18 := by
    exact group16Block_eval memory f17
  have h18 : inline16Block.eval memory f18 = f19 := by
    exact inline16Block_eval memory (hoistedAlgorithmFold memory 0 16 f.lane)
  have h19 : inline17Block.eval memory f19 = f20 := by
    exact inline17Block_eval memory (hoistedAlgorithmFold memory 0 17 f.lane)
  have h20 : inline18Block.eval memory f20 = f21 := by
    exact inline18Block_eval memory (hoistedAlgorithmFold memory 0 18 f.lane)
  have h21 : inline19Block.eval memory f21 = f22 := by
    exact inline19Block_eval memory (hoistedAlgorithmFold memory 0 19 f.lane)
  have h22 : inline20Block.eval memory f22 = f23 := by
    exact inline20Block_eval memory (hoistedAlgorithmFold memory 0 20 f.lane)
  have h23 : inline21Block.eval memory f23 = f24 := by
    exact inline21Block_eval memory (hoistedAlgorithmFold memory 0 21 f.lane)
  have h24 : inline22Block.eval memory f24 = f25 := by
    exact inline22Block_eval memory (hoistedAlgorithmFold memory 0 22 f.lane)
  have h25 : inline23Block.eval memory f25 = f26 := by
    exact inline23Block_eval memory (hoistedAlgorithmFold memory 0 23 f.lane)
  have h26 : inline24Block.eval memory f26 = f27 := by
    exact inline24Block_eval memory (hoistedAlgorithmFold memory 0 24 f.lane)
  have h27 : inline25Block.eval memory f27 = f28 := by
    exact inline25Block_eval memory (hoistedAlgorithmFold memory 0 25 f.lane)
  have h28 : inline26Block.eval memory f28 = f29 := by
    exact inline26Block_eval memory (hoistedAlgorithmFold memory 0 26 f.lane)
  have h29 : inline27Block.eval memory f29 = f30 := by
    exact inline27Block_eval memory (hoistedAlgorithmFold memory 0 27 f.lane)
  have h30 : inline28Block.eval memory f30 = f31 := by
    exact inline28Block_eval memory (hoistedAlgorithmFold memory 0 28 f.lane)
  have h31 : inline29Block.eval memory f31 = f32 := by
    exact inline29Block_eval memory (hoistedAlgorithmFold memory 0 29 f.lane)
  have h32 : inline30Block.eval memory f32 = f33 := by
    exact inline30Block_eval memory (hoistedAlgorithmFold memory 0 30 f.lane)
  have h33 : inline31Block.eval memory f33 = f34 := by
    exact inline31Block_eval memory (hoistedAlgorithmFold memory 0 31 f.lane)
  have h34 : group32Block.eval memory f34 = f35 := by
    exact group32Block_eval memory f34
  have h35 : inline32Block.eval memory f35 = f36 := by
    exact inline32Block_eval memory (hoistedAlgorithmFold memory 0 32 f.lane)
  have h36 : inline33Block.eval memory f36 = f37 := by
    exact inline33Block_eval memory (hoistedAlgorithmFold memory 0 33 f.lane)
  have h37 : inline34Block.eval memory f37 = f38 := by
    exact inline34Block_eval memory (hoistedAlgorithmFold memory 0 34 f.lane)
  have h38 : inline35Block.eval memory f38 = f39 := by
    exact inline35Block_eval memory (hoistedAlgorithmFold memory 0 35 f.lane)
  have h39 : inline36Block.eval memory f39 = f40 := by
    exact inline36Block_eval memory (hoistedAlgorithmFold memory 0 36 f.lane)
  have h40 : inline37Block.eval memory f40 = f41 := by
    exact inline37Block_eval memory (hoistedAlgorithmFold memory 0 37 f.lane)
  have h41 : inline38Block.eval memory f41 = f42 := by
    exact inline38Block_eval memory (hoistedAlgorithmFold memory 0 38 f.lane)
  have h42 : inline39Block.eval memory f42 = f43 := by
    exact inline39Block_eval memory (hoistedAlgorithmFold memory 0 39 f.lane)
  have h43 : inline40Block.eval memory f43 = f44 := by
    exact inline40Block_eval memory (hoistedAlgorithmFold memory 0 40 f.lane)
  have h44 : inline41Block.eval memory f44 = f45 := by
    exact inline41Block_eval memory (hoistedAlgorithmFold memory 0 41 f.lane)
  have h45 : inline42Block.eval memory f45 = f46 := by
    exact inline42Block_eval memory (hoistedAlgorithmFold memory 0 42 f.lane)
  have h46 : inline43Block.eval memory f46 = f47 := by
    exact inline43Block_eval memory (hoistedAlgorithmFold memory 0 43 f.lane)
  have h47 : inline44Block.eval memory f47 = f48 := by
    exact inline44Block_eval memory (hoistedAlgorithmFold memory 0 44 f.lane)
  have h48 : inline45Block.eval memory f48 = f49 := by
    exact inline45Block_eval memory (hoistedAlgorithmFold memory 0 45 f.lane)
  have h49 : inline46Block.eval memory f49 = f50 := by
    exact inline46Block_eval memory (hoistedAlgorithmFold memory 0 46 f.lane)
  have h50 : inline47Block.eval memory f50 = f51 := by
    exact inline47Block_eval memory (hoistedAlgorithmFold memory 0 47 f.lane)
  have h51 : group48Block.eval memory f51 = f52 := by
    exact group48Block_eval memory f51
  have h52 : inline48Block.eval memory f52 = f53 := by
    exact inline48Block_eval memory (hoistedAlgorithmFold memory 0 48 f.lane)
  have h53 : inline49Block.eval memory f53 = f54 := by
    exact inline49Block_eval memory (hoistedAlgorithmFold memory 0 49 f.lane)
  have h54 : inline50Block.eval memory f54 = f55 := by
    exact inline50Block_eval memory (hoistedAlgorithmFold memory 0 50 f.lane)
  have h55 : inline51Block.eval memory f55 = f56 := by
    exact inline51Block_eval memory (hoistedAlgorithmFold memory 0 51 f.lane)
  have h56 : inline52Block.eval memory f56 = f57 := by
    exact inline52Block_eval memory (hoistedAlgorithmFold memory 0 52 f.lane)
  have h57 : inline53Block.eval memory f57 = f58 := by
    exact inline53Block_eval memory (hoistedAlgorithmFold memory 0 53 f.lane)
  have h58 : inline54Block.eval memory f58 = f59 := by
    exact inline54Block_eval memory (hoistedAlgorithmFold memory 0 54 f.lane)
  have h59 : inline55Block.eval memory f59 = f60 := by
    exact inline55Block_eval memory (hoistedAlgorithmFold memory 0 55 f.lane)
  have h60 : inline56Block.eval memory f60 = f61 := by
    exact inline56Block_eval memory (hoistedAlgorithmFold memory 0 56 f.lane)
  have h61 : inline57Block.eval memory f61 = f62 := by
    exact inline57Block_eval memory (hoistedAlgorithmFold memory 0 57 f.lane)
  have h62 : inline58Block.eval memory f62 = f63 := by
    exact inline58Block_eval memory (hoistedAlgorithmFold memory 0 58 f.lane)
  have h63 : inline59Block.eval memory f63 = f64 := by
    exact inline59Block_eval memory (hoistedAlgorithmFold memory 0 59 f.lane)
  have h64 : inline60Block.eval memory f64 = f65 := by
    exact inline60Block_eval memory (hoistedAlgorithmFold memory 0 60 f.lane)
  have h65 : inline61Block.eval memory f65 = f66 := by
    exact inline61Block_eval memory (hoistedAlgorithmFold memory 0 61 f.lane)
  have h66 : inline62Block.eval memory f66 = f67 := by
    exact inline62Block_eval memory (hoistedAlgorithmFold memory 0 62 f.lane)
  have h67 : inline63Block.eval memory f67 = f68 := by
    exact inline63Block_eval memory (hoistedAlgorithmFold memory 0 63 f.lane)
  have h68 : group64Block.eval memory f68 = f69 := by
    exact group64Block_eval memory f68
  have h69 : inline64Block.eval memory f69 = f70 := by
    exact inline64Block_eval memory (hoistedAlgorithmFold memory 0 64 f.lane)
  have h70 : inline65Block.eval memory f70 = f71 := by
    exact inline65Block_eval memory (hoistedAlgorithmFold memory 0 65 f.lane)
  have h71 : inline66Block.eval memory f71 = f72 := by
    exact inline66Block_eval memory (hoistedAlgorithmFold memory 0 66 f.lane)
  have h72 : inline67Block.eval memory f72 = f73 := by
    exact inline67Block_eval memory (hoistedAlgorithmFold memory 0 67 f.lane)
  have h73 : inline68Block.eval memory f73 = f74 := by
    exact inline68Block_eval memory (hoistedAlgorithmFold memory 0 68 f.lane)
  have h74 : inline69Block.eval memory f74 = f75 := by
    exact inline69Block_eval memory (hoistedAlgorithmFold memory 0 69 f.lane)
  have h75 : inline70Block.eval memory f75 = f76 := by
    exact inline70Block_eval memory (hoistedAlgorithmFold memory 0 70 f.lane)
  have h76 : inline71Block.eval memory f76 = f77 := by
    exact inline71Block_eval memory (hoistedAlgorithmFold memory 0 71 f.lane)
  have h77 : inline72Block.eval memory f77 = f78 := by
    exact inline72Block_eval memory (hoistedAlgorithmFold memory 0 72 f.lane)
  have h78 : inline73Block.eval memory f78 = f79 := by
    exact inline73Block_eval memory (hoistedAlgorithmFold memory 0 73 f.lane)
  have h79 : inline74Block.eval memory f79 = f80 := by
    exact inline74Block_eval memory (hoistedAlgorithmFold memory 0 74 f.lane)
  have h80 : inline75Block.eval memory f80 = f81 := by
    exact inline75Block_eval memory (hoistedAlgorithmFold memory 0 75 f.lane)
  have h81 : inline76Block.eval memory f81 = f82 := by
    exact inline76Block_eval memory (hoistedAlgorithmFold memory 0 76 f.lane)
  have h82 : inline77Block.eval memory f82 = f83 := by
    exact inline77Block_eval memory (hoistedAlgorithmFold memory 0 77 f.lane)
  have h83 : inline78Block.eval memory f83 = f84 := by
    exact inline78Block_eval memory (hoistedAlgorithmFold memory 0 78 f.lane)
  have h84 : inline79Block.eval memory f84 = f85 := by
    exact inline79Block_eval memory (hoistedAlgorithmFold memory 0 79 f.lane)
  have hc : CoreEvalCert wholeCoreChain memory f0 f85 :=
    .cons group0Block _ h0 (
    .cons inline0Block _ h1 (
    .cons inline1Block _ h2 (
    .cons inline2Block _ h3 (
    .cons inline3Block _ h4 (
    .cons inline4Block _ h5 (
    .cons inline5Block _ h6 (
    .cons inline6Block _ h7 (
    .cons inline7Block _ h8 (
    .cons inline8Block _ h9 (
    .cons inline9Block _ h10 (
    .cons inline10Block _ h11 (
    .cons inline11Block _ h12 (
    .cons inline12Block _ h13 (
    .cons inline13Block _ h14 (
    .cons inline14Block _ h15 (
    .cons inline15Block _ h16 (
    .cons group16Block _ h17 (
    .cons inline16Block _ h18 (
    .cons inline17Block _ h19 (
    .cons inline18Block _ h20 (
    .cons inline19Block _ h21 (
    .cons inline20Block _ h22 (
    .cons inline21Block _ h23 (
    .cons inline22Block _ h24 (
    .cons inline23Block _ h25 (
    .cons inline24Block _ h26 (
    .cons inline25Block _ h27 (
    .cons inline26Block _ h28 (
    .cons inline27Block _ h29 (
    .cons inline28Block _ h30 (
    .cons inline29Block _ h31 (
    .cons inline30Block _ h32 (
    .cons inline31Block _ h33 (
    .cons group32Block _ h34 (
    .cons inline32Block _ h35 (
    .cons inline33Block _ h36 (
    .cons inline34Block _ h37 (
    .cons inline35Block _ h38 (
    .cons inline36Block _ h39 (
    .cons inline37Block _ h40 (
    .cons inline38Block _ h41 (
    .cons inline39Block _ h42 (
    .cons inline40Block _ h43 (
    .cons inline41Block _ h44 (
    .cons inline42Block _ h45 (
    .cons inline43Block _ h46 (
    .cons inline44Block _ h47 (
    .cons inline45Block _ h48 (
    .cons inline46Block _ h49 (
    .cons inline47Block _ h50 (
    .cons group48Block _ h51 (
    .cons inline48Block _ h52 (
    .cons inline49Block _ h53 (
    .cons inline50Block _ h54 (
    .cons inline51Block _ h55 (
    .cons inline52Block _ h56 (
    .cons inline53Block _ h57 (
    .cons inline54Block _ h58 (
    .cons inline55Block _ h59 (
    .cons inline56Block _ h60 (
    .cons inline57Block _ h61 (
    .cons inline58Block _ h62 (
    .cons inline59Block _ h63 (
    .cons inline60Block _ h64 (
    .cons inline61Block _ h65 (
    .cons inline62Block _ h66 (
    .cons inline63Block _ h67 (
    .cons group64Block _ h68 (
    .cons inline64Block _ h69 (
    .cons inline65Block _ h70 (
    .cons inline66Block _ h71 (
    .cons inline67Block _ h72 (
    .cons inline68Block _ h73 (
    .cons inline69Block _ h74 (
    .cons inline70Block _ h75 (
    .cons inline71Block _ h76 (
    .cons inline72Block _ h77 (
    .cons inline73Block _ h78 (
    .cons inline74Block _ h79 (
    .cons inline75Block _ h80 (
    .cons inline76Block _ h81 (
    .cons inline77Block _ h82 (
    .cons inline78Block _ h83 (
    .cons inline79Block _ h84 (
    .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact hc.sound

#print axioms wholeCoreChain_eval

theorem run_wholeCore_crypto (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hmessage : ∀ i < 80, algorithmMessage s.memory i =
      packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho} =
      some {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} := by
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto left right, 0⟩
  have h0 := wholeCoreChain_eval s.memory f
  have h1 := hoistedAlgorithmFold_crypto s.memory words 80 (by decide) left right hmessage
  have he : wholeCoreChain.eval s.memory f = coreCryptoResult words left right :=
    h0.trans (congrArg (fun q => CoreFrame.mk q (algorithmKey 4)) h1)
  exact (run_wholeCoreChain s f rho hstack hrun hactive).trans
    (congrArg (fun q => some {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] q rho}) he)

#print axioms run_wholeCore_crypto

theorem run_wholeCore_normalized (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hready : NormalizedScheduleReady s.memory words) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho} =
      some {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} := by
  exact run_wholeCore_crypto s words left right rho hstack hrun hactive
    (algorithmMessage_of_normalized s.memory words hready)

#print axioms run_wholeCore_normalized




/- GasSteps lifting for the straightline core, with no internal jump-validity premise. -/

open Challenge.EvmProof StackRoundTemplate

structure CoreGasBlock {a b : Nat} {xs ys : List CoreReg}
    (block : CoreBlock a b xs ys) (artifact : ProgramArtifact) (fork : Fork) where
  run : ∀ (s : State) (f : CoreFrame) (rho : List UInt256),
    rho.length ≤ 1002 → s.halt = .Running → 23 ≤ s.activeWords.toNat →
    s.executionEnv.code = artifact.code → s.fork = fork →
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
    intro s f rho hstack hrun hactive hcode hfork hnp
    exact gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm hform
      (block.run s f rho hstack hrun hactive)

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
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat a, stack := coreStack xs f rho}
      {s with pc := UInt256.ofNat b, stack := coreStack ys (chain.eval s.memory f) rho} :=
  match steps with
  | .nil _ _ => GasSteps.refl _
  | .cons block _ first rest =>
      (first.run s f rho hstack hrun hactive hcode hfork hnp).trans
        (CoreGasChain.run rest s (block.eval s.memory f) rho
          hstack hrun hactive hcode hfork hnp)

#print axioms CoreGasBlock.of_site
#print axioms CoreGasChain.run

theorem group0Block_terminal_advances :
    ∀ instruction ∈ group0Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms group0Block_terminal_advances

theorem inline0Block_terminal_advances :
    ∀ instruction ∈ inline0Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline0Block_terminal_advances

theorem inline1Block_terminal_advances :
    ∀ instruction ∈ inline1Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline1Block_terminal_advances

theorem inline2Block_terminal_advances :
    ∀ instruction ∈ inline2Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline2Block_terminal_advances

theorem inline3Block_terminal_advances :
    ∀ instruction ∈ inline3Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline3Block_terminal_advances

theorem inline4Block_terminal_advances :
    ∀ instruction ∈ inline4Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline4Block_terminal_advances

theorem inline5Block_terminal_advances :
    ∀ instruction ∈ inline5Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline5Block_terminal_advances

theorem inline6Block_terminal_advances :
    ∀ instruction ∈ inline6Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline6Block_terminal_advances

theorem inline7Block_terminal_advances :
    ∀ instruction ∈ inline7Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline7Block_terminal_advances

theorem inline8Block_terminal_advances :
    ∀ instruction ∈ inline8Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline8Block_terminal_advances

theorem inline9Block_terminal_advances :
    ∀ instruction ∈ inline9Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline9Block_terminal_advances

theorem inline10Block_terminal_advances :
    ∀ instruction ∈ inline10Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline10Block_terminal_advances

theorem inline11Block_terminal_advances :
    ∀ instruction ∈ inline11Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline11Block_terminal_advances

theorem inline12Block_terminal_advances :
    ∀ instruction ∈ inline12Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline12Block_terminal_advances

theorem inline13Block_terminal_advances :
    ∀ instruction ∈ inline13Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline13Block_terminal_advances

theorem inline14Block_terminal_advances :
    ∀ instruction ∈ inline14Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline14Block_terminal_advances

theorem inline15Block_terminal_advances :
    ∀ instruction ∈ inline15Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline15Block_terminal_advances

theorem group16Block_terminal_advances :
    ∀ instruction ∈ group16Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms group16Block_terminal_advances

theorem inline16Block_terminal_advances :
    ∀ instruction ∈ inline16Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline16Block_terminal_advances

theorem inline17Block_terminal_advances :
    ∀ instruction ∈ inline17Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline17Block_terminal_advances

theorem inline18Block_terminal_advances :
    ∀ instruction ∈ inline18Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline18Block_terminal_advances

theorem inline19Block_terminal_advances :
    ∀ instruction ∈ inline19Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline19Block_terminal_advances

theorem inline20Block_terminal_advances :
    ∀ instruction ∈ inline20Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline20Block_terminal_advances

theorem inline21Block_terminal_advances :
    ∀ instruction ∈ inline21Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline21Block_terminal_advances

theorem inline22Block_terminal_advances :
    ∀ instruction ∈ inline22Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline22Block_terminal_advances

theorem inline23Block_terminal_advances :
    ∀ instruction ∈ inline23Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline23Block_terminal_advances

theorem inline24Block_terminal_advances :
    ∀ instruction ∈ inline24Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline24Block_terminal_advances

theorem inline25Block_terminal_advances :
    ∀ instruction ∈ inline25Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline25Block_terminal_advances

theorem inline26Block_terminal_advances :
    ∀ instruction ∈ inline26Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline26Block_terminal_advances

theorem inline27Block_terminal_advances :
    ∀ instruction ∈ inline27Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline27Block_terminal_advances

theorem inline28Block_terminal_advances :
    ∀ instruction ∈ inline28Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline28Block_terminal_advances

theorem inline29Block_terminal_advances :
    ∀ instruction ∈ inline29Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline29Block_terminal_advances

theorem inline30Block_terminal_advances :
    ∀ instruction ∈ inline30Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline30Block_terminal_advances

theorem inline31Block_terminal_advances :
    ∀ instruction ∈ inline31Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline31Block_terminal_advances

theorem group32Block_terminal_advances :
    ∀ instruction ∈ group32Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms group32Block_terminal_advances

theorem inline32Block_terminal_advances :
    ∀ instruction ∈ inline32Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline32Block_terminal_advances

theorem inline33Block_terminal_advances :
    ∀ instruction ∈ inline33Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline33Block_terminal_advances

theorem inline34Block_terminal_advances :
    ∀ instruction ∈ inline34Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline34Block_terminal_advances

theorem inline35Block_terminal_advances :
    ∀ instruction ∈ inline35Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline35Block_terminal_advances

theorem inline36Block_terminal_advances :
    ∀ instruction ∈ inline36Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline36Block_terminal_advances

theorem inline37Block_terminal_advances :
    ∀ instruction ∈ inline37Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline37Block_terminal_advances

theorem inline38Block_terminal_advances :
    ∀ instruction ∈ inline38Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline38Block_terminal_advances

theorem inline39Block_terminal_advances :
    ∀ instruction ∈ inline39Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline39Block_terminal_advances

theorem inline40Block_terminal_advances :
    ∀ instruction ∈ inline40Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline40Block_terminal_advances

theorem inline41Block_terminal_advances :
    ∀ instruction ∈ inline41Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline41Block_terminal_advances

theorem inline42Block_terminal_advances :
    ∀ instruction ∈ inline42Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline42Block_terminal_advances

theorem inline43Block_terminal_advances :
    ∀ instruction ∈ inline43Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline43Block_terminal_advances

theorem inline44Block_terminal_advances :
    ∀ instruction ∈ inline44Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline44Block_terminal_advances

theorem inline45Block_terminal_advances :
    ∀ instruction ∈ inline45Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline45Block_terminal_advances

theorem inline46Block_terminal_advances :
    ∀ instruction ∈ inline46Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline46Block_terminal_advances

theorem inline47Block_terminal_advances :
    ∀ instruction ∈ inline47Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline47Block_terminal_advances

theorem group48Block_terminal_advances :
    ∀ instruction ∈ group48Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms group48Block_terminal_advances

theorem inline48Block_terminal_advances :
    ∀ instruction ∈ inline48Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline48Block_terminal_advances

theorem inline49Block_terminal_advances :
    ∀ instruction ∈ inline49Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline49Block_terminal_advances

theorem inline50Block_terminal_advances :
    ∀ instruction ∈ inline50Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline50Block_terminal_advances

theorem inline51Block_terminal_advances :
    ∀ instruction ∈ inline51Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline51Block_terminal_advances

theorem inline52Block_terminal_advances :
    ∀ instruction ∈ inline52Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline52Block_terminal_advances

theorem inline53Block_terminal_advances :
    ∀ instruction ∈ inline53Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline53Block_terminal_advances

theorem inline54Block_terminal_advances :
    ∀ instruction ∈ inline54Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline54Block_terminal_advances

theorem inline55Block_terminal_advances :
    ∀ instruction ∈ inline55Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline55Block_terminal_advances

theorem inline56Block_terminal_advances :
    ∀ instruction ∈ inline56Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline56Block_terminal_advances

theorem inline57Block_terminal_advances :
    ∀ instruction ∈ inline57Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline57Block_terminal_advances

theorem inline58Block_terminal_advances :
    ∀ instruction ∈ inline58Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline58Block_terminal_advances

theorem inline59Block_terminal_advances :
    ∀ instruction ∈ inline59Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline59Block_terminal_advances

theorem inline60Block_terminal_advances :
    ∀ instruction ∈ inline60Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline60Block_terminal_advances

theorem inline61Block_terminal_advances :
    ∀ instruction ∈ inline61Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline61Block_terminal_advances

theorem inline62Block_terminal_advances :
    ∀ instruction ∈ inline62Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline62Block_terminal_advances

theorem inline63Block_terminal_advances :
    ∀ instruction ∈ inline63Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline63Block_terminal_advances

theorem group64Block_terminal_advances :
    ∀ instruction ∈ group64Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms group64Block_terminal_advances

theorem inline64Block_terminal_advances :
    ∀ instruction ∈ inline64Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline64Block_terminal_advances

theorem inline65Block_terminal_advances :
    ∀ instruction ∈ inline65Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline65Block_terminal_advances

theorem inline66Block_terminal_advances :
    ∀ instruction ∈ inline66Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline66Block_terminal_advances

theorem inline67Block_terminal_advances :
    ∀ instruction ∈ inline67Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline67Block_terminal_advances

theorem inline68Block_terminal_advances :
    ∀ instruction ∈ inline68Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline68Block_terminal_advances

theorem inline69Block_terminal_advances :
    ∀ instruction ∈ inline69Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline69Block_terminal_advances

theorem inline70Block_terminal_advances :
    ∀ instruction ∈ inline70Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline70Block_terminal_advances

theorem inline71Block_terminal_advances :
    ∀ instruction ∈ inline71Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline71Block_terminal_advances

theorem inline72Block_terminal_advances :
    ∀ instruction ∈ inline72Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline72Block_terminal_advances

theorem inline73Block_terminal_advances :
    ∀ instruction ∈ inline73Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline73Block_terminal_advances

theorem inline74Block_terminal_advances :
    ∀ instruction ∈ inline74Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline74Block_terminal_advances

theorem inline75Block_terminal_advances :
    ∀ instruction ∈ inline75Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline75Block_terminal_advances

theorem inline76Block_terminal_advances :
    ∀ instruction ∈ inline76Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline76Block_terminal_advances

theorem inline77Block_terminal_advances :
    ∀ instruction ∈ inline77Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline77Block_terminal_advances

theorem inline78Block_terminal_advances :
    ∀ instruction ∈ inline78Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline78Block_terminal_advances

theorem inline79Block_terminal_advances :
    ∀ instruction ∈ inline79Block.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline79Block_terminal_advances



structure WholeCoreSites (artifact : ProgramArtifact) (fork : Fork) where
  group0 : {site : GenericRoundSite artifact fork group0Block.code // site.startPC = UInt256.ofNat 769}
  inline0 : {site : GenericRoundSite artifact fork inline0Block.code // site.startPC = UInt256.ofNat 777}
  inline1 : {site : GenericRoundSite artifact fork inline1Block.code // site.startPC = UInt256.ofNat 829}
  inline2 : {site : GenericRoundSite artifact fork inline2Block.code // site.startPC = UInt256.ofNat 881}
  inline3 : {site : GenericRoundSite artifact fork inline3Block.code // site.startPC = UInt256.ofNat 934}
  inline4 : {site : GenericRoundSite artifact fork inline4Block.code // site.startPC = UInt256.ofNat 986}
  inline5 : {site : GenericRoundSite artifact fork inline5Block.code // site.startPC = UInt256.ofNat 1040}
  inline6 : {site : GenericRoundSite artifact fork inline6Block.code // site.startPC = UInt256.ofNat 1094}
  inline7 : {site : GenericRoundSite artifact fork inline7Block.code // site.startPC = UInt256.ofNat 1148}
  inline8 : {site : GenericRoundSite artifact fork inline8Block.code // site.startPC = UInt256.ofNat 1201}
  inline9 : {site : GenericRoundSite artifact fork inline9Block.code // site.startPC = UInt256.ofNat 1254}
  inline10 : {site : GenericRoundSite artifact fork inline10Block.code // site.startPC = UInt256.ofNat 1307}
  inline11 : {site : GenericRoundSite artifact fork inline11Block.code // site.startPC = UInt256.ofNat 1360}
  inline12 : {site : GenericRoundSite artifact fork inline12Block.code // site.startPC = UInt256.ofNat 1413}
  inline13 : {site : GenericRoundSite artifact fork inline13Block.code // site.startPC = UInt256.ofNat 1466}
  inline14 : {site : GenericRoundSite artifact fork inline14Block.code // site.startPC = UInt256.ofNat 1520}
  inline15 : {site : GenericRoundSite artifact fork inline15Block.code // site.startPC = UInt256.ofNat 1574}
  group16 : {site : GenericRoundSite artifact fork group16Block.code // site.startPC = UInt256.ofNat 1626}
  inline16 : {site : GenericRoundSite artifact fork inline16Block.code // site.startPC = UInt256.ofNat 1640}
  inline17 : {site : GenericRoundSite artifact fork inline17Block.code // site.startPC = UInt256.ofNat 1696}
  inline18 : {site : GenericRoundSite artifact fork inline18Block.code // site.startPC = UInt256.ofNat 1752}
  inline19 : {site : GenericRoundSite artifact fork inline19Block.code // site.startPC = UInt256.ofNat 1808}
  inline20 : {site : GenericRoundSite artifact fork inline20Block.code // site.startPC = UInt256.ofNat 1862}
  inline21 : {site : GenericRoundSite artifact fork inline21Block.code // site.startPC = UInt256.ofNat 1917}
  inline22 : {site : GenericRoundSite artifact fork inline22Block.code // site.startPC = UInt256.ofNat 1972}
  inline23 : {site : GenericRoundSite artifact fork inline23Block.code // site.startPC = UInt256.ofNat 2028}
  inline24 : {site : GenericRoundSite artifact fork inline24Block.code // site.startPC = UInt256.ofNat 2083}
  inline25 : {site : GenericRoundSite artifact fork inline25Block.code // site.startPC = UInt256.ofNat 2129}
  inline26 : {site : GenericRoundSite artifact fork inline26Block.code // site.startPC = UInt256.ofNat 2183}
  inline27 : {site : GenericRoundSite artifact fork inline27Block.code // site.startPC = UInt256.ofNat 2238}
  inline28 : {site : GenericRoundSite artifact fork inline28Block.code // site.startPC = UInt256.ofNat 2293}
  inline29 : {site : GenericRoundSite artifact fork inline29Block.code // site.startPC = UInt256.ofNat 2348}
  inline30 : {site : GenericRoundSite artifact fork inline30Block.code // site.startPC = UInt256.ofNat 2404}
  inline31 : {site : GenericRoundSite artifact fork inline31Block.code // site.startPC = UInt256.ofNat 2449}
  group32 : {site : GenericRoundSite artifact fork group32Block.code // site.startPC = UInt256.ofNat 2504}
  inline32 : {site : GenericRoundSite artifact fork inline32Block.code // site.startPC = UInt256.ofNat 2528}
  inline33 : {site : GenericRoundSite artifact fork inline33Block.code // site.startPC = UInt256.ofNat 2576}
  inline34 : {site : GenericRoundSite artifact fork inline34Block.code // site.startPC = UInt256.ofNat 2624}
  inline35 : {site : GenericRoundSite artifact fork inline35Block.code // site.startPC = UInt256.ofNat 2672}
  inline36 : {site : GenericRoundSite artifact fork inline36Block.code // site.startPC = UInt256.ofNat 2721}
  inline37 : {site : GenericRoundSite artifact fork inline37Block.code // site.startPC = UInt256.ofNat 2769}
  inline38 : {site : GenericRoundSite artifact fork inline38Block.code // site.startPC = UInt256.ofNat 2817}
  inline39 : {site : GenericRoundSite artifact fork inline39Block.code // site.startPC = UInt256.ofNat 2865}
  inline40 : {site : GenericRoundSite artifact fork inline40Block.code // site.startPC = UInt256.ofNat 2912}
  inline41 : {site : GenericRoundSite artifact fork inline41Block.code // site.startPC = UInt256.ofNat 2960}
  inline42 : {site : GenericRoundSite artifact fork inline42Block.code // site.startPC = UInt256.ofNat 3009}
  inline43 : {site : GenericRoundSite artifact fork inline43Block.code // site.startPC = UInt256.ofNat 3056}
  inline44 : {site : GenericRoundSite artifact fork inline44Block.code // site.startPC = UInt256.ofNat 3105}
  inline45 : {site : GenericRoundSite artifact fork inline45Block.code // site.startPC = UInt256.ofNat 3154}
  inline46 : {site : GenericRoundSite artifact fork inline46Block.code // site.startPC = UInt256.ofNat 3202}
  inline47 : {site : GenericRoundSite artifact fork inline47Block.code // site.startPC = UInt256.ofNat 3241}
  group48 : {site : GenericRoundSite artifact fork group48Block.code // site.startPC = UInt256.ofNat 3279}
  inline48 : {site : GenericRoundSite artifact fork inline48Block.code // site.startPC = UInt256.ofNat 3300}
  inline49 : {site : GenericRoundSite artifact fork inline49Block.code // site.startPC = UInt256.ofNat 3355}
  inline50 : {site : GenericRoundSite artifact fork inline50Block.code // site.startPC = UInt256.ofNat 3410}
  inline51 : {site : GenericRoundSite artifact fork inline51Block.code // site.startPC = UInt256.ofNat 3465}
  inline52 : {site : GenericRoundSite artifact fork inline52Block.code // site.startPC = UInt256.ofNat 3519}
  inline53 : {site : GenericRoundSite artifact fork inline53Block.code // site.startPC = UInt256.ofNat 3564}
  inline54 : {site : GenericRoundSite artifact fork inline54Block.code // site.startPC = UInt256.ofNat 3619}
  inline55 : {site : GenericRoundSite artifact fork inline55Block.code // site.startPC = UInt256.ofNat 3674}
  inline56 : {site : GenericRoundSite artifact fork inline56Block.code // site.startPC = UInt256.ofNat 3729}
  inline57 : {site : GenericRoundSite artifact fork inline57Block.code // site.startPC = UInt256.ofNat 3784}
  inline58 : {site : GenericRoundSite artifact fork inline58Block.code // site.startPC = UInt256.ofNat 3839}
  inline59 : {site : GenericRoundSite artifact fork inline59Block.code // site.startPC = UInt256.ofNat 3895}
  inline60 : {site : GenericRoundSite artifact fork inline60Block.code // site.startPC = UInt256.ofNat 3951}
  inline61 : {site : GenericRoundSite artifact fork inline61Block.code // site.startPC = UInt256.ofNat 4007}
  inline62 : {site : GenericRoundSite artifact fork inline62Block.code // site.startPC = UInt256.ofNat 4062}
  inline63 : {site : GenericRoundSite artifact fork inline63Block.code // site.startPC = UInt256.ofNat 4118}
  group64 : {site : GenericRoundSite artifact fork group64Block.code // site.startPC = UInt256.ofNat 4173}
  inline64 : {site : GenericRoundSite artifact fork inline64Block.code // site.startPC = UInt256.ofNat 4180}
  inline65 : {site : GenericRoundSite artifact fork inline65Block.code // site.startPC = UInt256.ofNat 4233}
  inline66 : {site : GenericRoundSite artifact fork inline66Block.code // site.startPC = UInt256.ofNat 4285}
  inline67 : {site : GenericRoundSite artifact fork inline67Block.code // site.startPC = UInt256.ofNat 4339}
  inline68 : {site : GenericRoundSite artifact fork inline68Block.code // site.startPC = UInt256.ofNat 4392}
  inline69 : {site : GenericRoundSite artifact fork inline69Block.code // site.startPC = UInt256.ofNat 4445}
  inline70 : {site : GenericRoundSite artifact fork inline70Block.code // site.startPC = UInt256.ofNat 4498}
  inline71 : {site : GenericRoundSite artifact fork inline71Block.code // site.startPC = UInt256.ofNat 4552}
  inline72 : {site : GenericRoundSite artifact fork inline72Block.code // site.startPC = UInt256.ofNat 4605}
  inline73 : {site : GenericRoundSite artifact fork inline73Block.code // site.startPC = UInt256.ofNat 4659}
  inline74 : {site : GenericRoundSite artifact fork inline74Block.code // site.startPC = UInt256.ofNat 4712}
  inline75 : {site : GenericRoundSite artifact fork inline75Block.code // site.startPC = UInt256.ofNat 4765}
  inline76 : {site : GenericRoundSite artifact fork inline76Block.code // site.startPC = UInt256.ofNat 4818}
  inline77 : {site : GenericRoundSite artifact fork inline77Block.code // site.startPC = UInt256.ofNat 4871}
  inline78 : {site : GenericRoundSite artifact fork inline78Block.code // site.startPC = UInt256.ofNat 4925}
  inline79 : {site : GenericRoundSite artifact fork inline79Block.code // site.startPC = UInt256.ofNat 4979}

def wholeCoreGasChain {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) : CoreGasChain artifact fork wholeCoreChain :=
  .cons group0Block _ (CoreGasBlock.of_site group0Block sites.group0.val sites.group0.property group0Block_terminal_advances) (
  .cons inline0Block _ (CoreGasBlock.of_site inline0Block sites.inline0.val sites.inline0.property inline0Block_terminal_advances) (
  .cons inline1Block _ (CoreGasBlock.of_site inline1Block sites.inline1.val sites.inline1.property inline1Block_terminal_advances) (
  .cons inline2Block _ (CoreGasBlock.of_site inline2Block sites.inline2.val sites.inline2.property inline2Block_terminal_advances) (
  .cons inline3Block _ (CoreGasBlock.of_site inline3Block sites.inline3.val sites.inline3.property inline3Block_terminal_advances) (
  .cons inline4Block _ (CoreGasBlock.of_site inline4Block sites.inline4.val sites.inline4.property inline4Block_terminal_advances) (
  .cons inline5Block _ (CoreGasBlock.of_site inline5Block sites.inline5.val sites.inline5.property inline5Block_terminal_advances) (
  .cons inline6Block _ (CoreGasBlock.of_site inline6Block sites.inline6.val sites.inline6.property inline6Block_terminal_advances) (
  .cons inline7Block _ (CoreGasBlock.of_site inline7Block sites.inline7.val sites.inline7.property inline7Block_terminal_advances) (
  .cons inline8Block _ (CoreGasBlock.of_site inline8Block sites.inline8.val sites.inline8.property inline8Block_terminal_advances) (
  .cons inline9Block _ (CoreGasBlock.of_site inline9Block sites.inline9.val sites.inline9.property inline9Block_terminal_advances) (
  .cons inline10Block _ (CoreGasBlock.of_site inline10Block sites.inline10.val sites.inline10.property inline10Block_terminal_advances) (
  .cons inline11Block _ (CoreGasBlock.of_site inline11Block sites.inline11.val sites.inline11.property inline11Block_terminal_advances) (
  .cons inline12Block _ (CoreGasBlock.of_site inline12Block sites.inline12.val sites.inline12.property inline12Block_terminal_advances) (
  .cons inline13Block _ (CoreGasBlock.of_site inline13Block sites.inline13.val sites.inline13.property inline13Block_terminal_advances) (
  .cons inline14Block _ (CoreGasBlock.of_site inline14Block sites.inline14.val sites.inline14.property inline14Block_terminal_advances) (
  .cons inline15Block _ (CoreGasBlock.of_site inline15Block sites.inline15.val sites.inline15.property inline15Block_terminal_advances) (
  .cons group16Block _ (CoreGasBlock.of_site group16Block sites.group16.val sites.group16.property group16Block_terminal_advances) (
  .cons inline16Block _ (CoreGasBlock.of_site inline16Block sites.inline16.val sites.inline16.property inline16Block_terminal_advances) (
  .cons inline17Block _ (CoreGasBlock.of_site inline17Block sites.inline17.val sites.inline17.property inline17Block_terminal_advances) (
  .cons inline18Block _ (CoreGasBlock.of_site inline18Block sites.inline18.val sites.inline18.property inline18Block_terminal_advances) (
  .cons inline19Block _ (CoreGasBlock.of_site inline19Block sites.inline19.val sites.inline19.property inline19Block_terminal_advances) (
  .cons inline20Block _ (CoreGasBlock.of_site inline20Block sites.inline20.val sites.inline20.property inline20Block_terminal_advances) (
  .cons inline21Block _ (CoreGasBlock.of_site inline21Block sites.inline21.val sites.inline21.property inline21Block_terminal_advances) (
  .cons inline22Block _ (CoreGasBlock.of_site inline22Block sites.inline22.val sites.inline22.property inline22Block_terminal_advances) (
  .cons inline23Block _ (CoreGasBlock.of_site inline23Block sites.inline23.val sites.inline23.property inline23Block_terminal_advances) (
  .cons inline24Block _ (CoreGasBlock.of_site inline24Block sites.inline24.val sites.inline24.property inline24Block_terminal_advances) (
  .cons inline25Block _ (CoreGasBlock.of_site inline25Block sites.inline25.val sites.inline25.property inline25Block_terminal_advances) (
  .cons inline26Block _ (CoreGasBlock.of_site inline26Block sites.inline26.val sites.inline26.property inline26Block_terminal_advances) (
  .cons inline27Block _ (CoreGasBlock.of_site inline27Block sites.inline27.val sites.inline27.property inline27Block_terminal_advances) (
  .cons inline28Block _ (CoreGasBlock.of_site inline28Block sites.inline28.val sites.inline28.property inline28Block_terminal_advances) (
  .cons inline29Block _ (CoreGasBlock.of_site inline29Block sites.inline29.val sites.inline29.property inline29Block_terminal_advances) (
  .cons inline30Block _ (CoreGasBlock.of_site inline30Block sites.inline30.val sites.inline30.property inline30Block_terminal_advances) (
  .cons inline31Block _ (CoreGasBlock.of_site inline31Block sites.inline31.val sites.inline31.property inline31Block_terminal_advances) (
  .cons group32Block _ (CoreGasBlock.of_site group32Block sites.group32.val sites.group32.property group32Block_terminal_advances) (
  .cons inline32Block _ (CoreGasBlock.of_site inline32Block sites.inline32.val sites.inline32.property inline32Block_terminal_advances) (
  .cons inline33Block _ (CoreGasBlock.of_site inline33Block sites.inline33.val sites.inline33.property inline33Block_terminal_advances) (
  .cons inline34Block _ (CoreGasBlock.of_site inline34Block sites.inline34.val sites.inline34.property inline34Block_terminal_advances) (
  .cons inline35Block _ (CoreGasBlock.of_site inline35Block sites.inline35.val sites.inline35.property inline35Block_terminal_advances) (
  .cons inline36Block _ (CoreGasBlock.of_site inline36Block sites.inline36.val sites.inline36.property inline36Block_terminal_advances) (
  .cons inline37Block _ (CoreGasBlock.of_site inline37Block sites.inline37.val sites.inline37.property inline37Block_terminal_advances) (
  .cons inline38Block _ (CoreGasBlock.of_site inline38Block sites.inline38.val sites.inline38.property inline38Block_terminal_advances) (
  .cons inline39Block _ (CoreGasBlock.of_site inline39Block sites.inline39.val sites.inline39.property inline39Block_terminal_advances) (
  .cons inline40Block _ (CoreGasBlock.of_site inline40Block sites.inline40.val sites.inline40.property inline40Block_terminal_advances) (
  .cons inline41Block _ (CoreGasBlock.of_site inline41Block sites.inline41.val sites.inline41.property inline41Block_terminal_advances) (
  .cons inline42Block _ (CoreGasBlock.of_site inline42Block sites.inline42.val sites.inline42.property inline42Block_terminal_advances) (
  .cons inline43Block _ (CoreGasBlock.of_site inline43Block sites.inline43.val sites.inline43.property inline43Block_terminal_advances) (
  .cons inline44Block _ (CoreGasBlock.of_site inline44Block sites.inline44.val sites.inline44.property inline44Block_terminal_advances) (
  .cons inline45Block _ (CoreGasBlock.of_site inline45Block sites.inline45.val sites.inline45.property inline45Block_terminal_advances) (
  .cons inline46Block _ (CoreGasBlock.of_site inline46Block sites.inline46.val sites.inline46.property inline46Block_terminal_advances) (
  .cons inline47Block _ (CoreGasBlock.of_site inline47Block sites.inline47.val sites.inline47.property inline47Block_terminal_advances) (
  .cons group48Block _ (CoreGasBlock.of_site group48Block sites.group48.val sites.group48.property group48Block_terminal_advances) (
  .cons inline48Block _ (CoreGasBlock.of_site inline48Block sites.inline48.val sites.inline48.property inline48Block_terminal_advances) (
  .cons inline49Block _ (CoreGasBlock.of_site inline49Block sites.inline49.val sites.inline49.property inline49Block_terminal_advances) (
  .cons inline50Block _ (CoreGasBlock.of_site inline50Block sites.inline50.val sites.inline50.property inline50Block_terminal_advances) (
  .cons inline51Block _ (CoreGasBlock.of_site inline51Block sites.inline51.val sites.inline51.property inline51Block_terminal_advances) (
  .cons inline52Block _ (CoreGasBlock.of_site inline52Block sites.inline52.val sites.inline52.property inline52Block_terminal_advances) (
  .cons inline53Block _ (CoreGasBlock.of_site inline53Block sites.inline53.val sites.inline53.property inline53Block_terminal_advances) (
  .cons inline54Block _ (CoreGasBlock.of_site inline54Block sites.inline54.val sites.inline54.property inline54Block_terminal_advances) (
  .cons inline55Block _ (CoreGasBlock.of_site inline55Block sites.inline55.val sites.inline55.property inline55Block_terminal_advances) (
  .cons inline56Block _ (CoreGasBlock.of_site inline56Block sites.inline56.val sites.inline56.property inline56Block_terminal_advances) (
  .cons inline57Block _ (CoreGasBlock.of_site inline57Block sites.inline57.val sites.inline57.property inline57Block_terminal_advances) (
  .cons inline58Block _ (CoreGasBlock.of_site inline58Block sites.inline58.val sites.inline58.property inline58Block_terminal_advances) (
  .cons inline59Block _ (CoreGasBlock.of_site inline59Block sites.inline59.val sites.inline59.property inline59Block_terminal_advances) (
  .cons inline60Block _ (CoreGasBlock.of_site inline60Block sites.inline60.val sites.inline60.property inline60Block_terminal_advances) (
  .cons inline61Block _ (CoreGasBlock.of_site inline61Block sites.inline61.val sites.inline61.property inline61Block_terminal_advances) (
  .cons inline62Block _ (CoreGasBlock.of_site inline62Block sites.inline62.val sites.inline62.property inline62Block_terminal_advances) (
  .cons inline63Block _ (CoreGasBlock.of_site inline63Block sites.inline63.val sites.inline63.property inline63Block_terminal_advances) (
  .cons group64Block _ (CoreGasBlock.of_site group64Block sites.group64.val sites.group64.property group64Block_terminal_advances) (
  .cons inline64Block _ (CoreGasBlock.of_site inline64Block sites.inline64.val sites.inline64.property inline64Block_terminal_advances) (
  .cons inline65Block _ (CoreGasBlock.of_site inline65Block sites.inline65.val sites.inline65.property inline65Block_terminal_advances) (
  .cons inline66Block _ (CoreGasBlock.of_site inline66Block sites.inline66.val sites.inline66.property inline66Block_terminal_advances) (
  .cons inline67Block _ (CoreGasBlock.of_site inline67Block sites.inline67.val sites.inline67.property inline67Block_terminal_advances) (
  .cons inline68Block _ (CoreGasBlock.of_site inline68Block sites.inline68.val sites.inline68.property inline68Block_terminal_advances) (
  .cons inline69Block _ (CoreGasBlock.of_site inline69Block sites.inline69.val sites.inline69.property inline69Block_terminal_advances) (
  .cons inline70Block _ (CoreGasBlock.of_site inline70Block sites.inline70.val sites.inline70.property inline70Block_terminal_advances) (
  .cons inline71Block _ (CoreGasBlock.of_site inline71Block sites.inline71.val sites.inline71.property inline71Block_terminal_advances) (
  .cons inline72Block _ (CoreGasBlock.of_site inline72Block sites.inline72.val sites.inline72.property inline72Block_terminal_advances) (
  .cons inline73Block _ (CoreGasBlock.of_site inline73Block sites.inline73.val sites.inline73.property inline73Block_terminal_advances) (
  .cons inline74Block _ (CoreGasBlock.of_site inline74Block sites.inline74.val sites.inline74.property inline74Block_terminal_advances) (
  .cons inline75Block _ (CoreGasBlock.of_site inline75Block sites.inline75.val sites.inline75.property inline75Block_terminal_advances) (
  .cons inline76Block _ (CoreGasBlock.of_site inline76Block sites.inline76.val sites.inline76.property inline76Block_terminal_advances) (
  .cons inline77Block _ (CoreGasBlock.of_site inline77Block sites.inline77.val sites.inline77.property inline77Block_terminal_advances) (
  .cons inline78Block _ (CoreGasBlock.of_site inline78Block sites.inline78.val sites.inline78.property inline78Block_terminal_advances) (
  .cons inline79Block _ (CoreGasBlock.of_site inline79Block sites.inline79.val sites.inline79.property inline79Block_terminal_advances) (
  .nil 5032 [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def gasSteps_wholeCore {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho}
      {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (wholeCoreChain.eval s.memory f) rho} :=
  (wholeCoreGasChain sites).run s f rho hstack hrun hactive hcode hfork hnp

#print axioms gasSteps_wholeCore

def gasSteps_wholeCore_normalized {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hready : NormalizedScheduleReady s.memory words) :
    GasSteps {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho}
      {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} := by
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto left right, 0⟩
  have h0 := wholeCoreChain_eval s.memory f
  have h1 := hoistedAlgorithmFold_crypto s.memory words 80 (by decide) left right
    (algorithmMessage_of_normalized s.memory words hready)
  have he : wholeCoreChain.eval s.memory f = coreCryptoResult words left right :=
    h0.trans (congrArg (fun q => CoreFrame.mk q (algorithmKey 4)) h1)
  exact (gasSteps_wholeCore sites s f rho hstack hrun hactive hcode hfork hnp).cast rfl
    (congrArg (fun q => {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] q rho}) he)

#print axioms gasSteps_wholeCore_normalized


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
