import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedFactoredGroupConstants

set_option warningAsError true

/-! Consume the old group constant in rounds 15 and 47 before materializing
the next independent literal. Raw execution retains arbitrary UInt256 cache
words, arbitrary memory, and the existing suffix/active-memory bounds. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedGroupKConsume

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist
open PairedSynthCoreTrace (zeroRaw zeroRaw_eq_inline0Boolean inlineHoistedBoolean rawT_hoisted)

def consumedOutput (q : PairedHelperBooleanTrace.Frame) (value : UInt256)
    (rho : List UInt256) : List UInt256 :=
  [rawC10 q, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def consumedWordStack (q : PairedHelperBooleanTrace.Frame)
    (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group47Frame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 27}

def group47Entry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def consumed15Template : List Instr :=
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

theorem consumed15Template_length : consumed15Template.length = 45 := rfl

#print axioms consumed15Template_length

theorem run_consumed15Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq consumed15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc consumed15Template, stack := consumedOutput q (inlineT (inline15Frame s.memory q) (zeroRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [PairedLaneSequentialShift.shr_word,
    consumed15Template, inline15Entry, consumedOutput,
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

#print axioms run_consumed15Template_raw

theorem run_consumed15Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq consumed15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc consumed15Template, stack := consumedWordStack q (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline15Frame s.memory q) (zeroRaw q) =
      PairedLaneWordRound.wordT 0 8 6 q.a q.b q.c q.d q.e
        (inline15Frame s.memory q).message0 q.k := by
    rw [zeroRaw_eq_inline0Boolean]
    exact (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline15Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline15Frame s.memory q) 0 8 6 hfactor hpair hupper rfl rfl))
  have hout : consumedOutput q (inlineT (inline15Frame s.memory q) (zeroRaw q)) rho =
      consumedWordStack q
        (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [consumedOutput, consumedWordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_consumed15Template_raw s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc consumed15Template, stack := vs}) hout)

#print axioms run_consumed15Template_word

theorem consumed15Template_bytes : (consumed15Template.map Instr.size).sum = 52 := rfl

#print axioms consumed15Template_bytes

def consumed47Template : List Instr :=
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

theorem consumed47Template_length : consumed47Template.length = 32 := rfl

#print axioms consumed47Template_length

theorem run_consumed47Template_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq consumed47Template {s with pc := pc, stack := group47Entry q rho} =
      some {s with pc := pcAfter pc consumed47Template, stack := consumedOutput q (singleT (group47Frame s.memory q) (inlineHoistedBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [consumed47Template, group47Entry, consumedOutput,
    singleT, group47Frame, inlineHoistedBoolean, rawHoistedBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  refine ⟨rfl, rfl, ?_⟩
  let post (v : UInt256) : UInt256 :=
    UInt256.land q.pair (UInt256.add q.e
      (UInt256.shiftRight (UInt256.mul q.factor (UInt256.land q.pair v)) (UInt256.ofNat 27)))
  let sum := UInt256.add (group47Frame s.memory q).message0
    (UInt256.add (inlineHoistedBoolean q) q.a)
  change post (UInt256.add sum q.k) = post (UInt256.add q.k sum)
  exact congrArg post (Challenge.EvmProof.Word.word_add_comm sum q.k)

#print axioms run_consumed47Template_raw

theorem run_consumed47Template_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq consumed47Template {s with pc := pc, stack := group47Entry q rho} =
      some {s with pc := pcAfter pc consumed47Template, stack := consumedWordStack q (rawWordStep2 5 5 (group47Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (group47Frame s.memory q) (inlineHoistedBoolean q) =
      hoistedT 5 5 q.a q.b q.c q.d q.e (group47Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      (rawT_hoisted (group47Frame s.memory q) 5 5 hfactor hpair hupper rfl rfl)
  have hout : consumedOutput q (singleT (group47Frame s.memory q) (inlineHoistedBoolean q)) rho =
      consumedWordStack q
        (rawWordStep2 5 5 (group47Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [consumedOutput, consumedWordStack, rawWordStep2, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_consumed47Template_raw s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc consumed47Template, stack := vs}) hout)

#print axioms run_consumed47Template_word

theorem consumed47Template_bytes : (consumed47Template.map Instr.size).sum = 38 := rfl

#print axioms consumed47Template_bytes

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

def materialize16Template : List Instr :=
  [.push ⟨20, by decide⟩ (UInt256.ofNat 526962527014005041256681316140890030896371104153),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128), .op .SHL,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x5a827999), .op .OR]

theorem run_materialize16Template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq materialize16Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc materialize16Template, stack := UInt256.ofNat 526962527014005041256681316140890030896371104153 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 2) : rho.length + n < 1024 := by omega
  have hzero : rho.length < 1024 := by omega
  simp [materialize16Template, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, Nat.add_assoc, UInt256.succ, hrun, hzero, hcap,
    PairedFactoredGroupConstants.mixed_value, word_add_ofNat_assoc]
  change (((pc + UInt256.ofNat 7) + UInt256.ofNat 1) + UInt256.ofNat 5) + UInt256.ofNat 1 = pc + UInt256.ofNat 14
  simp only [word_add_ofNat_assoc]

#print axioms run_materialize16Template

def materialize48Template : List Instr :=
  [.push ⟨20, by decide⟩ (UInt256.ofNat 698938013802679700166637234969497128417458109660)]

theorem run_materialize48Template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1024) (hrun : s.halt = .Running) :
    runInstrSeq materialize48Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc materialize48Template, stack := UInt256.ofNat 698938013802679700166637234969497128417458109660 :: rho} := by
  simp [materialize48Template, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, Instr.size, hrun, hstack]

#print axioms run_materialize48Template

theorem materialize_lengths :
    materialize16Template.length = 5 ∧ materialize48Template.length = 1 := by decide

#print axioms materialize_lengths

theorem materialize_bytes :
    (materialize16Template.map Instr.size).sum = 14 ∧
    (materialize48Template.map Instr.size).sum = 21 := by decide

#print axioms materialize_bytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedGroupKConsume
