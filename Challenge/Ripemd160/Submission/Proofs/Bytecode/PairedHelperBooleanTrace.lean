import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanDelta
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean PairedLaneBooleanDelta

/-- The exact helper entry frame; every word remains arbitrary here. -/
structure Frame where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256
  factor : UInt256
  pair : UInt256
  upper : UInt256
  lower : UInt256
  k : UInt256
  message0 : UInt256
  leftShift0 : UInt256
  rightShift0 : UInt256
  message1 : UInt256
  leftShift1 : UInt256
  rightShift1 : UInt256
  ret : UInt256

def entryStack (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.leftShift0, q.message0, q.rightShift0, q.a, q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho


/-- Physical105-byte helper prefix; generic pc, exact frozen be84 helper opcodes. -/
def template : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op .XOR]


def rawBoolean (q : Frame) : UInt256 :=
  UInt256.xor
    (UInt256.land q.upper
      (UInt256.xor q.d (UInt256.land q.c (UInt256.lnot (UInt256.xor q.d q.b)))))
    (UInt256.xor q.d (UInt256.land q.b (UInt256.xor q.d q.c)))

def resultStack (q : Frame) (rho : List UInt256) : List UInt256 :=
  [rawBoolean q, q.a, q.message0, q.rightShift0, q.leftShift0, q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho


theorem template_length : template.length = 20 := rfl

theorem run_template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := pcAfter pc template, stack := resultStack q rho} := by
  have h17 : rho.length + 17 < 1024 := by omega
  have h18 : rho.length + 18 < 1024 := by omega
  have h19 : rho.length + 19 < 1024 := by omega
  have h20 : rho.length + 20 < 1024 := by omega
  simp (discharger := omega) [template, entryStack, resultStack, rawBoolean,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, h17, h18, h19, h20]
  rfl

theorem rawBoolean_eq (q : Frame) (hupper : q.upper = upperWord) :
    rawBoolean q = booleanPair 1 q.b q.c q.d := by
  rw [booleanPair_one_delta]
  apply bits_injective
  simp only [rawBoolean, hupper, deltaWord, wordF, bits_xor, bits_land, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits upperWord).getLsbD i <;> rfl


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


def firstTEntry (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [value, q.a, q.message0, q.rightShift0, q.leftShift0, q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho


def rawSum (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.land q.pair
    (UInt256.add q.k (UInt256.add (UInt256.add value q.a) q.message0))


def rawProduct (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.mul q.factor (rawSum q value)

def rawRotation (q : Frame) (value : UInt256) : UInt256 :=
  let left := UInt256.shiftRight (rawProduct q value) q.leftShift0
  let right := UInt256.shiftRight (rawProduct q value) q.rightShift0
  UInt256.xor (UInt256.land q.upper (UInt256.xor left right)) left


def rawT (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.land q.pair (UInt256.add q.e (rawRotation q value))

def afterTStack (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [value, q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho


theorem firstTTemplate_length : firstTTemplate.length = 23 := rfl

theorem run_firstTTemplate (s : State) (pc value : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq firstTTemplate {s with pc := pc, stack := firstTEntry q value rho} =
      some {s with pc := pcAfter pc firstTTemplate, stack := afterTStack q (rawT q value) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [firstTTemplate, firstTEntry, afterTStack,
    rawT, rawRotation, rawProduct, rawSum, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩

def firstC10Template : List Instr :=
  [.op (.Swap ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND]


def rawC10 (q : Frame) : UInt256 :=
  UInt256.land q.pair
    (UInt256.shiftRight (UInt256.mul q.factor q.c) (UInt256.ofNat 22))

def afterC10Stack (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [(rawC10 q), q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho


theorem firstC10Template_length : firstC10Template.length = 7 := rfl

theorem run_firstC10Template (s : State) (pc value : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq firstC10Template {s with pc := pc, stack := afterTStack q value rho} =
      some {s with pc := pcAfter pc firstC10Template, stack := afterC10Stack q value rho} := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [firstC10Template, afterTStack, afterC10Stack,
    rawC10, runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩


def secondFrame (q : Frame) (value : UInt256) : Frame :=
  {q with a := q.e, b := value, c := q.b, d := rawC10 q, e := q.d, message0 := q.message1, leftShift0 := q.leftShift1, rightShift0 := q.rightShift1}

def secondBooleanTemplate : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Dup ⟨11, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR]


def secondTEntry (q : Frame) (first value : UInt256) (rho : List UInt256) : List UInt256 :=
  [value, q.e, q.message1, q.rightShift1, q.leftShift1, q.d, q.ret, q.b, first, q.upper, (rawC10 q), q.factor, q.pair, q.k, q.lower] ++ rho


theorem secondBooleanTemplate_length : secondBooleanTemplate.length = 19 := rfl

theorem run_secondBooleanTemplate (s : State) (pc first : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondBooleanTemplate {s with pc := pc, stack := afterC10Stack q first rho} =
      some {s with pc := pcAfter pc secondBooleanTemplate, stack := secondTEntry q first (rawBoolean (secondFrame q first)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 17) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [secondBooleanTemplate, afterC10Stack, secondTEntry,
    secondFrame, rawBoolean, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap]
  rfl

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


def secondTStack (q : Frame) (first value : UInt256) (rho : List UInt256) : List UInt256 :=
  [value, q.d, q.ret, q.b, first, q.upper, (rawC10 q), q.factor, q.pair, q.k, q.lower] ++ rho


theorem secondTTemplate_length : secondTTemplate.length = 23 := rfl

theorem run_secondTTemplate (s : State) (pc first value : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondTTemplate {s with pc := pc, stack := secondTEntry q first value rho} =
      some {s with pc := pcAfter pc secondTTemplate, stack := secondTStack q first (rawT (secondFrame q first) value) rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [secondTTemplate, secondTEntry, secondTStack,
    rawT, rawRotation, rawProduct, rawSum, secondFrame, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩

def secondC10Template : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .push ⟨1, by decide⟩ (UInt256.ofNat 22),
   .op .SHR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND]


def secondC10Stack (q : Frame) (first value : UInt256) (rho : List UInt256) : List UInt256 :=
  [(rawC10 (secondFrame q first)), q.d, q.ret, value, first, q.upper, (rawC10 q), q.factor, q.pair, q.k, q.lower] ++ rho


theorem secondC10Template_length : secondC10Template.length = 7 := rfl

theorem run_secondC10Template (s : State) (pc first value : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq secondC10Template {s with pc := pc, stack := secondTStack q first value rho} =
      some {s with pc := pcAfter pc secondC10Template, stack := secondC10Stack q first value rho} := by
  have hcap (n : Nat) (hn : n ≤ 13) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [secondC10Template, secondTStack, secondC10Stack,
    rawC10, secondFrame, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap]
  exact ⟨rfl, rfl⟩

def returnTemplate : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .JUMP]


def returnedStack (q : Frame) (first value : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, (rawC10 (secondFrame q first)), value, first, q.upper, (rawC10 q), q.factor, q.pair, q.k, q.lower] ++ rho


theorem run_returnTemplate (s : State) (pc first value : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code q.ret.toNat = true) :
    runInstrSeq returnTemplate {s with pc := pc, stack := secondC10Stack q first value rho} =
      some {s with pc := q.ret, stack := returnedStack q first value rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [returnTemplate, secondC10Stack, returnedStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hvalid]


/-- The seven exact contiguous chunks, including the indirect return. -/
def fullTemplate : List Instr :=
  (((((template ++ firstTTemplate) ++ firstC10Template) ++ secondBooleanTemplate) ++
    secondTTemplate) ++ secondC10Template) ++ returnTemplate

theorem fullTemplate_length : fullTemplate.length = 101 := by decide

theorem fullTemplate_byteLength : (fullTemplate.map Instr.size).sum = 103 := by decide

theorem run_fullTemplate (s : State) (pc : UInt256) (q : Frame)
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


/-- Arithmetic order differences in the physical stack do not change the word. -/
theorem uand_comm (x y : UInt256) : UInt256.land x y = UInt256.land y x := by
  apply bits_injective
  simp only [bits_land]
  exact BitVec.and_comm _ _

theorem umul_comm (x y : UInt256) : UInt256.mul x y = UInt256.mul y x := by
  apply bits_injective
  simp only [bits_mul]
  exact BitVec.mul_comm _ _

theorem wordBlend_self (x : UInt256) : PairedLaneWordBlend.wordBlend x x = x := by
  apply bits_injective
  simp only [PairedLaneWordBlend.wordBlend, bits_xor, bits_land,
    BitVec.xor_self, BitVec.zero_and, BitVec.xor_zero]

theorem wordRotate_eq_blend (x : UInt256) (r t : Nat) :
    PairedLaneWordRotate.wordRotate x r t =
      PairedLaneWordBlend.wordBlend
        (PairedLaneWordRotate.wordShift x (32 - r))
        (PairedLaneWordRotate.wordShift x (32 - t)) := by
  unfold PairedLaneWordRotate.wordRotate
  split
  · rename_i h
    subst t
    exact (wordBlend_self (PairedLaneWordRotate.wordShift x (32 - r))).symm
  · rfl


theorem rawSum_eq (q : Frame) (hpair : q.pair = pairWord) :
    rawSum q (booleanPair 1 q.b q.c q.d) =
      PairedLaneWordRound.wordSum 1 q.a q.b q.c q.d q.message0 q.k := by
  apply bits_injective
  simp only [rawSum, PairedLaneWordRound.wordSum, hpair, bits_land, bits_add]
  ac_rfl


theorem rawRotation_eq (q : Frame) (value : UInt256) (r t : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord) (hupper : q.upper = upperWord)
    (hleft : q.leftShift0 = UInt256.ofNat (32 - r))
    (hright : q.rightShift0 = UInt256.ofNat (32 - t)) :
    rawRotation q value = PairedLaneWordRotate.wordRotate (rawSum q value) r t := by
  have hp : rawProduct q value =
      UInt256.mul (rawSum q value) PairedLaneWordRotate.factorWord := by
    exact (congrArg (fun x => UInt256.mul x (rawSum q value)) hfactor).trans (umul_comm _ _)
  rw [wordRotate_eq_blend]
  simp only [rawRotation, hp, hleft, hright, hupper,
    PairedLaneWordBlend.wordBlend, PairedLaneWordRotate.wordShift]
  apply bits_injective
  simp only [bits_xor, bits_land]
  ac_rfl


theorem rawT_eq (q : Frame) (r t : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hleft : q.leftShift0 = UInt256.ofNat (32 - r))
    (hright : q.rightShift0 = UInt256.ofNat (32 - t)) :
    rawT q (rawBoolean q) =
      PairedLaneWordRound.wordT 1 r t q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [rawBoolean_eq q hupper, rawT, rawRotation_eq q _ r t hfactor hupper hleft hright,
    rawSum_eq q hpair]
  apply bits_injective
  simp only [PairedLaneWordRound.wordT, hpair, bits_land, bits_add]
  ac_rfl


theorem rawC10_eq (q : Frame)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord) (hpair : q.pair = pairWord) :
    rawC10 q = UInt256.land (PairedLaneWordRotate.wordShift q.c 22) pairWord := by
  simp only [rawC10, hfactor, hpair, PairedLaneWordRotate.wordShift]
  exact (congrArg (fun x => UInt256.land pairWord
    (UInt256.shiftRight x (UInt256.ofNat 22))) (umul_comm _ _)).trans (uand_comm _ _)


def frameLane (q : Frame) : PairedLaneWordRound.WordLane :=
  ⟨q.a, q.b, q.c, q.d, q.e⟩

theorem secondFrame_wordStep (q : Frame) (r t : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hleft : q.leftShift0 = UInt256.ofNat (32 - r))
    (hright : q.rightShift0 = UInt256.ofNat (32 - t)) :
    frameLane (secondFrame q (rawT q (rawBoolean q))) =
      PairedLaneWordRound.wordStep 1 r t q.message0 q.k (frameLane q) := by
  simp only [frameLane, secondFrame, PairedLaneWordRound.wordStep,
    rawT_eq q r t hfactor hpair hupper hleft hright, rawC10_eq q hfactor hpair]




/-- Independent literal transcription of the pinned helper bytes 5168..5271. -/
def frozenHelperInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op .XOR,
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
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Dup ⟨11, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .XOR,
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

def wordReturnStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.a, v.d, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho


theorem run_fullTemplate_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code q.ret.toNat = true)
    (r0 t0 r1 t1 : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hl0 : q.leftShift0 = UInt256.ofNat (32 - r0))
    (hr0 : q.rightShift0 = UInt256.ofNat (32 - t0))
    (hl1 : q.leftShift1 = UInt256.ofNat (32 - r1))
    (hr1 : q.rightShift1 = UInt256.ofNat (32 - t1)) :
    runInstrSeq fullTemplate {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := q.ret, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 r1 t1 q.message1 q.k (PairedLaneWordRound.wordStep 1 r0 t0 q.message0 q.k (frameLane q))) rho} := by
  let first := rawT q (rawBoolean q)
  let q1 := secondFrame q first
  let second := rawT q1 (rawBoolean q1)
  have h0 : frameLane q1 =
      PairedLaneWordRound.wordStep 1 r0 t0 q.message0 q.k (frameLane q) :=
    secondFrame_wordStep q r0 t0 hfactor hpair hupper hl0 hr0
  have h1 : frameLane (secondFrame q1 second) =
      PairedLaneWordRound.wordStep 1 r1 t1 q.message1 q.k (frameLane q1) :=
    secondFrame_wordStep q1 r1 t1 hfactor hpair hupper hl1 hr1
  have hout := h1.trans (congrArg
    (PairedLaneWordRound.wordStep 1 r1 t1 q.message1 q.k) h0)
  exact (run_fullTemplate s pc q rho hstack hrun hvalid).trans
    (congrArg (fun v => some {s with pc := q.ret, stack := wordReturnStack q v rho}) hout)




def packed32 (lo hi : UInt32) : UInt256 :=
  word (PairedLaneCore.pack lo.toBitVec hi.toBitVec)

theorem twoWordSteps_of_crypto
    (r0 t0 r1 t1 : Nat)
    (hr00 : 0 < r0) (hr0 : r0 < 32) (ht00 : 0 < t0) (ht0 : t0 < 32)
    (hr10 : 0 < r1) (hr1 : r1 < 32) (ht10 : 0 < t1) (ht1 : t1 < 32)
    (ml0 mr0 ml1 mr1 kl kr : UInt32) (l r : PairedLaneCryptoBridge.CryptoLane) :
    PairedLaneWordRound.wordStep 1 r1 t1 (packed32 ml1 mr1) (packed32 kl kr)
        (PairedLaneWordRound.wordStep 1 r0 t0 (packed32 ml0 mr0) (packed32 kl kr)
          (PairedLaneWordRound.packCrypto l r)) =
      PairedLaneWordRound.packCrypto
        (PairedLaneCryptoBridge.cryptoStep 1 r1 ml1 kl
          (PairedLaneCryptoBridge.cryptoStep 1 r0 ml0 kl l))
        (PairedLaneCryptoBridge.cryptoStep 3 t1 mr1 kr
          (PairedLaneCryptoBridge.cryptoStep 3 t0 mr0 kr r)) := by
  exact (congrArg
    (PairedLaneWordRound.wordStep 1 r1 t1 (packed32 ml1 mr1) (packed32 kl kr))
    (PairedLaneWordRound.wordStep_of_crypto 1 r0 t0 hr00 hr0 ht00 ht0 ml0 mr0 kl kr l r)).trans
    (PairedLaneWordRound.wordStep_of_crypto 1 r1 t1 hr10 hr1 ht10 ht1 ml1 mr1 kl kr _ _)

theorem run_fullTemplate_crypto (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code q.ret.toNat = true)
    (r0 t0 r1 t1 : Nat)
    (hr00 : 0 < r0) (hr0 : r0 < 32) (ht00 : 0 < t0) (ht0 : t0 < 32)
    (hr10 : 0 < r1) (hr1 : r1 < 32) (ht10 : 0 < t1) (ht1 : t1 < 32)
    (ml0 mr0 ml1 mr1 kl kr : UInt32) (l r : PairedLaneCryptoBridge.CryptoLane)
    (hframe : frameLane q = PairedLaneWordRound.packCrypto l r)
    (hm0 : q.message0 = packed32 ml0 mr0) (hm1 : q.message1 = packed32 ml1 mr1)
    (hk : q.k = packed32 kl kr)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hl0 : q.leftShift0 = UInt256.ofNat (32 - r0))
    (hh0 : q.rightShift0 = UInt256.ofNat (32 - t0))
    (hl1 : q.leftShift1 = UInt256.ofNat (32 - r1))
    (hh1 : q.rightShift1 = UInt256.ofNat (32 - t1)) :
    runInstrSeq fullTemplate {s with pc := pc, stack := entryStack q rho} =
      some {s with pc := q.ret, stack := wordReturnStack q (PairedLaneWordRound.packCrypto
        (PairedLaneCryptoBridge.cryptoStep 1 r1 ml1 kl (PairedLaneCryptoBridge.cryptoStep 1 r0 ml0 kl l))
        (PairedLaneCryptoBridge.cryptoStep 3 t1 mr1 kr (PairedLaneCryptoBridge.cryptoStep 3 t0 mr0 kr r))) rho} := by
  have hsteps :
      PairedLaneWordRound.wordStep 1 r1 t1 q.message1 q.k
          (PairedLaneWordRound.wordStep 1 r0 t0 q.message0 q.k (frameLane q)) =
        PairedLaneWordRound.packCrypto
          (PairedLaneCryptoBridge.cryptoStep 1 r1 ml1 kl (PairedLaneCryptoBridge.cryptoStep 1 r0 ml0 kl l))
          (PairedLaneCryptoBridge.cryptoStep 3 t1 mr1 kr (PairedLaneCryptoBridge.cryptoStep 3 t0 mr0 kr r)) := by
    rw [hframe, hm0, hm1, hk]
    exact twoWordSteps_of_crypto r0 t0 r1 t1 hr00 hr0 ht00 ht0 hr10 hr1 ht10 ht1
      ml0 mr0 ml1 mr1 kl kr l r
  exact (run_fullTemplate_word s pc q rho hstack hrun hvalid r0 t0 r1 t1
    hfactor hpair hupper hl0 hh0 hl1 hh1).trans
    (congrArg (fun v => some {s with pc := q.ret, stack := wordReturnStack q v rho}) hsteps)

theorem active_schedule_preserved (current : UInt256) (address : Nat)
    (hcurrent : 23 ≤ current.toNat) (haddress : address ≤ 704) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have hwords : (address + 32 - 1) / 32 + 1 ≤ current.toNat := by omega
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change UInt256.ofNat (max current.toNat ((address + 32 - 1) / 32 + 1)) = current
  rw [Nat.max_eq_left hwords]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat current).symm

theorem rawSum_of_boolean (q : Frame) (j : Nat) (hpair : q.pair = pairWord) :
    rawSum q (booleanPair j q.b q.c q.d) =
      PairedLaneWordRound.wordSum j q.a q.b q.c q.d q.message0 q.k := by
  apply bits_injective
  simp only [rawSum, PairedLaneWordRound.wordSum, hpair, bits_land, bits_add]
  ac_rfl

theorem rawT_of_boolean (q : Frame) (j r t : Nat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord)
    (hleft : q.leftShift0 = UInt256.ofNat (32 - r))
    (hright : q.rightShift0 = UInt256.ofNat (32 - t)) :
    rawT q (booleanPair j q.b q.c q.d) =
      PairedLaneWordRound.wordT j r t q.a q.b q.c q.d q.e q.message0 q.k := by
  rw [rawT, rawRotation_eq q _ r t hfactor hupper hleft hright,
    rawSum_of_boolean q j hpair]
  apply bits_injective
  simp only [PairedLaneWordRound.wordT, hpair, bits_land, bits_add]
  ac_rfl

def inline0Boolean (q : Frame) : UInt256 :=
  UInt256.xor (UInt256.land q.upper (UInt256.lor q.d (UInt256.lnot q.c)))
    (UInt256.xor q.d (UInt256.xor q.c q.b))

theorem inline0Boolean_eq (q : Frame) (hupper : q.upper = upperWord) :
    inline0Boolean q = booleanPair 0 q.b q.c q.d := by
  apply bits_injective
  simp only [inline0Boolean, booleanPair, wordF, hupper,
    bits_xor, bits_land, bits_lor, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits upperWord).getLsbD i <;> rfl

def inline2Boolean (q : Frame) : UInt256 :=
  (UInt256.xor q.d (UInt256.lor q.b (UInt256.xor q.pair q.c)))

theorem inline2Boolean_eq (q : Frame) (hmask : q.pair = pairWord) :
    inline2Boolean q = booleanPair 2 q.b q.c q.d := by
  apply bits_injective
  simp only [inline2Boolean, booleanPair, wordF, hmask,
    bits_xor, bits_lor]
  ac_rfl

def inline3Boolean (q : Frame) : UInt256 :=
  (UInt256.xor (UInt256.land q.upper (UInt256.xor q.d (UInt256.land q.c (UInt256.lnot (UInt256.xor q.d q.b))))) (UInt256.xor q.c (UInt256.land q.d (UInt256.xor q.c q.b))))

theorem inline3Boolean_eq (q : Frame) (hmask : q.upper = upperWord) :
    inline3Boolean q = booleanPair 3 q.b q.c q.d := by
  apply bits_injective
  simp only [inline3Boolean, booleanPair, wordF, hmask,
    bits_xor, bits_land, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits upperWord).getLsbD i <;> rfl

def inline4Boolean (q : Frame) : UInt256 :=
  (UInt256.xor (UInt256.land q.lower (UInt256.lor q.d (UInt256.lnot q.c))) (UInt256.xor q.d (UInt256.xor q.c q.b)))

theorem inline4Boolean_eq (q : Frame) (hmask : q.lower = lowerWord) :
    inline4Boolean q = booleanPair 4 q.b q.c q.d := by
  apply bits_injective
  simp only [inline4Boolean, booleanPair, wordF, hmask,
    bits_xor, bits_land, bits_lor, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases (bits q.b).getLsbD i <;> cases (bits q.c).getLsbD i <;>
    cases (bits q.d).getLsbD i <;> cases (bits lowerWord).getLsbD i <;> rfl

def inlineProduct (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.mul q.factor (UInt256.land q.pair
    (UInt256.add q.k (UInt256.add q.message0 (UInt256.add value q.a))))

theorem inlineProduct_eq (q : Frame) (value : UInt256) :
    inlineProduct q value = rawProduct q value := by
  apply bits_injective
  simp only [inlineProduct, rawProduct, rawSum, bits_mul, bits_land, bits_add]
  ac_rfl

def inlineRotation (q : Frame) (value : UInt256) : UInt256 :=
  let left := UInt256.shiftRight (inlineProduct q value) q.leftShift0
  let right := UInt256.shiftRight (inlineProduct q value) q.rightShift0
  UInt256.xor (UInt256.land q.upper (UInt256.xor left right)) left

def inlineT (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.land q.pair (UInt256.add q.e (inlineRotation q value))

theorem inlineT_eq_rawT (q : Frame) (value : UInt256) :
    inlineT q value = rawT q value := by
  simp only [inlineT, inlineRotation, rawT, rawRotation, inlineProduct_eq]

def singleT (q : Frame) (value : UInt256) : UInt256 :=
  UInt256.land q.pair (UInt256.add q.e
    (UInt256.shiftRight (inlineProduct q value) q.leftShift0))

theorem singleT_eq_rawT (q : Frame) (value : UInt256)
    (hshift : q.rightShift0 = q.leftShift0) : singleT q value = rawT q value := by
  have hr : rawRotation q value =
      UInt256.shiftRight (rawProduct q value) q.leftShift0 := by
    unfold rawRotation
    rw [hshift]
    apply bits_injective
    simp only [bits_xor, bits_land, BitVec.xor_self, BitVec.and_zero, BitVec.zero_xor]
  simp only [singleT, rawT, inlineProduct_eq, hr]



def inline0Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
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

def inline0Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 24}

def inline0Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline0Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline0Template_length : inline0Template.length = 48 := rfl

theorem run_inline0Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline0Template {s with pc := pc, stack := inline0Entry q rho} =
      some {s with pc := pcAfter pc inline0Template, stack := inline0Output q (inlineT (inline0Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline0Template, inline0Entry, inline0Output,
    inlineT, inlineRotation, inline0Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline0WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline0Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline0Template {s with pc := pc, stack := inline0Entry q rho} =
      some {s with pc := pcAfter pc inline0Template, stack := inline0WordStack q (PairedLaneWordRound.wordStep 0 11 8 (inline0Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline0Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 11 8 q.a q.b q.c q.d q.e
        (inline0Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline0Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline0Frame s.memory q) 0 11 8 hfactor hpair hupper rfl rfl))
  have hout : inline0Output q (inlineT (inline0Frame s.memory q) (inline0Boolean q)) rho =
      inline0WordStack q
        (PairedLaneWordRound.wordStep 0 11 8 (inline0Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline0Output, inline0WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline0Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline0Template, stack := vs}) hout)


def inline1Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
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

def inline1Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 23}

def inline1Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline1Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline1Template_length : inline1Template.length = 48 := rfl

theorem run_inline1Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline1Template {s with pc := pc, stack := inline1Entry q rho} =
      some {s with pc := pcAfter pc inline1Template, stack := inline1Output q (inlineT (inline1Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline1Template, inline1Entry, inline1Output,
    inlineT, inlineRotation, inline1Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline1WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline1Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline1Template {s with pc := pc, stack := inline1Entry q rho} =
      some {s with pc := pcAfter pc inline1Template, stack := inline1WordStack q (PairedLaneWordRound.wordStep 0 14 9 (inline1Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline1Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 14 9 q.a q.b q.c q.d q.e
        (inline1Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline1Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline1Frame s.memory q) 0 14 9 hfactor hpair hupper rfl rfl))
  have hout : inline1Output q (inlineT (inline1Frame s.memory q) (inline0Boolean q)) rho =
      inline1WordStack q
        (PairedLaneWordRound.wordStep 0 14 9 (inline1Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline1Output, inline1WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline1Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline1Template, stack := vs}) hout)


def inline2Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

def inline2Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 23}

def inline2Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline2Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline2Template_length : inline2Template.length = 48 := rfl

theorem run_inline2Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline2Template {s with pc := pc, stack := inline2Entry q rho} =
      some {s with pc := pcAfter pc inline2Template, stack := inline2Output q (inlineT (inline2Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline2Template, inline2Entry, inline2Output,
    inlineT, inlineRotation, inline2Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline2WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline2Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline2Template {s with pc := pc, stack := inline2Entry q rho} =
      some {s with pc := pcAfter pc inline2Template, stack := inline2WordStack q (PairedLaneWordRound.wordStep 0 15 9 (inline2Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline2Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 15 9 q.a q.b q.c q.d q.e
        (inline2Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline2Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline2Frame s.memory q) 0 15 9 hfactor hpair hupper rfl rfl))
  have hout : inline2Output q (inlineT (inline2Frame s.memory q) (inline0Boolean q)) rho =
      inline2WordStack q
        (PairedLaneWordRound.wordStep 0 15 9 (inline2Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline2Output, inline2WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline2Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline2Template, stack := vs}) hout)


def inline3Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
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

def inline3Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 21}

def inline3Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline3Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline3Template_length : inline3Template.length = 48 := rfl

theorem run_inline3Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline3Template {s with pc := pc, stack := inline3Entry q rho} =
      some {s with pc := pcAfter pc inline3Template, stack := inline3Output q (inlineT (inline3Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline3Template, inline3Entry, inline3Output,
    inlineT, inlineRotation, inline3Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline3WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline3Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline3Template {s with pc := pc, stack := inline3Entry q rho} =
      some {s with pc := pcAfter pc inline3Template, stack := inline3WordStack q (PairedLaneWordRound.wordStep 0 12 11 (inline3Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline3Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 12 11 q.a q.b q.c q.d q.e
        (inline3Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline3Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline3Frame s.memory q) 0 12 11 hfactor hpair hupper rfl rfl))
  have hout : inline3Output q (inlineT (inline3Frame s.memory q) (inline0Boolean q)) rho =
      inline3WordStack q
        (PairedLaneWordRound.wordStep 0 12 11 (inline3Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline3Output, inline3WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline3Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline3Template, stack := vs}) hout)


def inline4Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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

def inline4Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 19}

def inline4Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline4Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline4Template_length : inline4Template.length = 48 := rfl

theorem run_inline4Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline4Template {s with pc := pc, stack := inline4Entry q rho} =
      some {s with pc := pcAfter pc inline4Template, stack := inline4Output q (inlineT (inline4Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline4Template, inline4Entry, inline4Output,
    inlineT, inlineRotation, inline4Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline4WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline4Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline4Template {s with pc := pc, stack := inline4Entry q rho} =
      some {s with pc := pcAfter pc inline4Template, stack := inline4WordStack q (PairedLaneWordRound.wordStep 0 5 13 (inline4Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline4Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 5 13 q.a q.b q.c q.d q.e
        (inline4Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline4Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline4Frame s.memory q) 0 5 13 hfactor hpair hupper rfl rfl))
  have hout : inline4Output q (inlineT (inline4Frame s.memory q) (inline0Boolean q)) rho =
      inline4WordStack q
        (PairedLaneWordRound.wordStep 0 5 13 (inline4Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline4Output, inline4WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline4Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline4Template, stack := vs}) hout)


def inline5Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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

def inline5Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 17}

def inline5Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline5Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline5Template_length : inline5Template.length = 48 := rfl

theorem run_inline5Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline5Template {s with pc := pc, stack := inline5Entry q rho} =
      some {s with pc := pcAfter pc inline5Template, stack := inline5Output q (inlineT (inline5Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline5Template, inline5Entry, inline5Output,
    inlineT, inlineRotation, inline5Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline5WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline5Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline5Template {s with pc := pc, stack := inline5Entry q rho} =
      some {s with pc := pcAfter pc inline5Template, stack := inline5WordStack q (PairedLaneWordRound.wordStep 0 8 15 (inline5Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline5Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 8 15 q.a q.b q.c q.d q.e
        (inline5Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline5Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline5Frame s.memory q) 0 8 15 hfactor hpair hupper rfl rfl))
  have hout : inline5Output q (inlineT (inline5Frame s.memory q) (inline0Boolean q)) rho =
      inline5WordStack q
        (PairedLaneWordRound.wordStep 0 8 15 (inline5Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline5Output, inline5WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline5Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline5Template, stack := vs}) hout)


def inline6Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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

def inline6Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 17}

def inline6Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline6Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline6Template_length : inline6Template.length = 48 := rfl

theorem run_inline6Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline6Template {s with pc := pc, stack := inline6Entry q rho} =
      some {s with pc := pcAfter pc inline6Template, stack := inline6Output q (inlineT (inline6Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline6Template, inline6Entry, inline6Output,
    inlineT, inlineRotation, inline6Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline6WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline6Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline6Template {s with pc := pc, stack := inline6Entry q rho} =
      some {s with pc := pcAfter pc inline6Template, stack := inline6WordStack q (PairedLaneWordRound.wordStep 0 7 15 (inline6Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline6Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 7 15 q.a q.b q.c q.d q.e
        (inline6Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline6Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline6Frame s.memory q) 0 7 15 hfactor hpair hupper rfl rfl))
  have hout : inline6Output q (inlineT (inline6Frame s.memory q) (inline0Boolean q)) rho =
      inline6WordStack q
        (PairedLaneWordRound.wordStep 0 7 15 (inline6Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline6Output, inline6WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline6Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline6Template, stack := vs}) hout)


def inline7Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline7Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 27}

def inline7Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline7Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline7Template_length : inline7Template.length = 48 := rfl

theorem run_inline7Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline7Template {s with pc := pc, stack := inline7Entry q rho} =
      some {s with pc := pcAfter pc inline7Template, stack := inline7Output q (inlineT (inline7Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline7Template, inline7Entry, inline7Output,
    inlineT, inlineRotation, inline7Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline7WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline7Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline7Template {s with pc := pc, stack := inline7Entry q rho} =
      some {s with pc := pcAfter pc inline7Template, stack := inline7WordStack q (PairedLaneWordRound.wordStep 0 9 5 (inline7Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline7Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 9 5 q.a q.b q.c q.d q.e
        (inline7Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline7Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline7Frame s.memory q) 0 9 5 hfactor hpair hupper rfl rfl))
  have hout : inline7Output q (inlineT (inline7Frame s.memory q) (inline0Boolean q)) rho =
      inline7WordStack q
        (PairedLaneWordRound.wordStep 0 9 5 (inline7Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline7Output, inline7WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline7Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline7Template, stack := vs}) hout)


def inline8Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline8Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 25}

def inline8Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline8Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline8Template_length : inline8Template.length = 48 := rfl

theorem run_inline8Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline8Template {s with pc := pc, stack := inline8Entry q rho} =
      some {s with pc := pcAfter pc inline8Template, stack := inline8Output q (inlineT (inline8Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline8Template, inline8Entry, inline8Output,
    inlineT, inlineRotation, inline8Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline8WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline8Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline8Template {s with pc := pc, stack := inline8Entry q rho} =
      some {s with pc := pcAfter pc inline8Template, stack := inline8WordStack q (PairedLaneWordRound.wordStep 0 11 7 (inline8Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline8Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 11 7 q.a q.b q.c q.d q.e
        (inline8Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline8Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline8Frame s.memory q) 0 11 7 hfactor hpair hupper rfl rfl))
  have hout : inline8Output q (inlineT (inline8Frame s.memory q) (inline0Boolean q)) rho =
      inline8WordStack q
        (PairedLaneWordRound.wordStep 0 11 7 (inline8Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline8Output, inline8WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline8Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline8Template, stack := vs}) hout)


def inline9Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline9Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 25}

def inline9Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline9Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline9Template_length : inline9Template.length = 48 := rfl

theorem run_inline9Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline9Template {s with pc := pc, stack := inline9Entry q rho} =
      some {s with pc := pcAfter pc inline9Template, stack := inline9Output q (inlineT (inline9Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline9Template, inline9Entry, inline9Output,
    inlineT, inlineRotation, inline9Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline9WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline9Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline9Template {s with pc := pc, stack := inline9Entry q rho} =
      some {s with pc := pcAfter pc inline9Template, stack := inline9WordStack q (PairedLaneWordRound.wordStep 0 13 7 (inline9Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline9Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 13 7 q.a q.b q.c q.d q.e
        (inline9Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline9Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline9Frame s.memory q) 0 13 7 hfactor hpair hupper rfl rfl))
  have hout : inline9Output q (inlineT (inline9Frame s.memory q) (inline0Boolean q)) rho =
      inline9WordStack q
        (PairedLaneWordRound.wordStep 0 13 7 (inline9Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline9Output, inline9WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline9Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline9Template, stack := vs}) hout)


def inline10Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
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

def inline10Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 24}

def inline10Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline10Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline10Template_length : inline10Template.length = 48 := rfl

theorem run_inline10Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline10Template {s with pc := pc, stack := inline10Entry q rho} =
      some {s with pc := pcAfter pc inline10Template, stack := inline10Output q (inlineT (inline10Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline10Template, inline10Entry, inline10Output,
    inlineT, inlineRotation, inline10Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline10WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline10Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline10Template {s with pc := pc, stack := inline10Entry q rho} =
      some {s with pc := pcAfter pc inline10Template, stack := inline10WordStack q (PairedLaneWordRound.wordStep 0 14 8 (inline10Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline10Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 14 8 q.a q.b q.c q.d q.e
        (inline10Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline10Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline10Frame s.memory q) 0 14 8 hfactor hpair hupper rfl rfl))
  have hout : inline10Output q (inlineT (inline10Frame s.memory q) (inline0Boolean q)) rho =
      inline10WordStack q
        (PairedLaneWordRound.wordStep 0 14 8 (inline10Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline10Output, inline10WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline10Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline10Template, stack := vs}) hout)


def inline11Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

def inline11Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 21}

def inline11Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline11Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline11Template_length : inline11Template.length = 48 := rfl

theorem run_inline11Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline11Template {s with pc := pc, stack := inline11Entry q rho} =
      some {s with pc := pcAfter pc inline11Template, stack := inline11Output q (inlineT (inline11Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline11Template, inline11Entry, inline11Output,
    inlineT, inlineRotation, inline11Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline11WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline11Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline11Template {s with pc := pc, stack := inline11Entry q rho} =
      some {s with pc := pcAfter pc inline11Template, stack := inline11WordStack q (PairedLaneWordRound.wordStep 0 15 11 (inline11Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline11Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 15 11 q.a q.b q.c q.d q.e
        (inline11Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline11Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline11Frame s.memory q) 0 15 11 hfactor hpair hupper rfl rfl))
  have hout : inline11Output q (inlineT (inline11Frame s.memory q) (inline0Boolean q)) rho =
      inline11WordStack q
        (PairedLaneWordRound.wordStep 0 15 11 (inline11Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline11Output, inline11WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline11Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline11Template, stack := vs}) hout)


def inline12Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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

def inline12Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 18}

def inline12Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline12Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline12Template_length : inline12Template.length = 48 := rfl

theorem run_inline12Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline12Template {s with pc := pc, stack := inline12Entry q rho} =
      some {s with pc := pcAfter pc inline12Template, stack := inline12Output q (inlineT (inline12Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline12Template, inline12Entry, inline12Output,
    inlineT, inlineRotation, inline12Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline12WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline12Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline12Template {s with pc := pc, stack := inline12Entry q rho} =
      some {s with pc := pcAfter pc inline12Template, stack := inline12WordStack q (PairedLaneWordRound.wordStep 0 6 14 (inline12Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline12Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 6 14 q.a q.b q.c q.d q.e
        (inline12Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline12Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline12Frame s.memory q) 0 6 14 hfactor hpair hupper rfl rfl))
  have hout : inline12Output q (inlineT (inline12Frame s.memory q) (inline0Boolean q)) rho =
      inline12WordStack q
        (PairedLaneWordRound.wordStep 0 6 14 (inline12Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline12Output, inline12WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline12Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline12Template, stack := vs}) hout)


def inline13Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline13Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 18}

def inline13Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline13Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline13Template_length : inline13Template.length = 48 := rfl

theorem run_inline13Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline13Template {s with pc := pc, stack := inline13Entry q rho} =
      some {s with pc := pcAfter pc inline13Template, stack := inline13Output q (inlineT (inline13Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline13Template, inline13Entry, inline13Output,
    inlineT, inlineRotation, inline13Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline13WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline13Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline13Template {s with pc := pc, stack := inline13Entry q rho} =
      some {s with pc := pcAfter pc inline13Template, stack := inline13WordStack q (PairedLaneWordRound.wordStep 0 7 14 (inline13Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline13Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 7 14 q.a q.b q.c q.d q.e
        (inline13Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline13Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline13Frame s.memory q) 0 7 14 hfactor hpair hupper rfl rfl))
  have hout : inline13Output q (inlineT (inline13Frame s.memory q) (inline0Boolean q)) rho =
      inline13WordStack q
        (PairedLaneWordRound.wordStep 0 7 14 (inline13Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline13Output, inline13WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline13Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline13Template, stack := vs}) hout)


def inline14Template : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨5, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨6, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
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

def inline14Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 20}

def inline14Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline14Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline14Template_length : inline14Template.length = 48 := rfl

theorem run_inline14Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline14Template {s with pc := pc, stack := inline14Entry q rho} =
      some {s with pc := pcAfter pc inline14Template, stack := inline14Output q (inlineT (inline14Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline14Template, inline14Entry, inline14Output,
    inlineT, inlineRotation, inline14Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline14WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, v.e, v.a, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline14Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline14Template {s with pc := pc, stack := inline14Entry q rho} =
      some {s with pc := pcAfter pc inline14Template, stack := inline14WordStack q (PairedLaneWordRound.wordStep 0 9 12 (inline14Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline14Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 9 12 q.a q.b q.c q.d q.e
        (inline14Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline14Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline14Frame s.memory q) 0 9 12 hfactor hpair hupper rfl rfl))
  have hout : inline14Output q (inlineT (inline14Frame s.memory q) (inline0Boolean q)) rho =
      inline14WordStack q
        (PairedLaneWordRound.wordStep 0 9 12 (inline14Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline14Output, inline14WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline14Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline14Template, stack := vs}) hout)


def inline15Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline15Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 26}

def inline15Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def inline15Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem inline15Template_length : inline15Template.length = 48 := rfl

theorem run_inline15Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc inline15Template, stack := inline15Output q (inlineT (inline15Frame s.memory q) (inline0Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline15Template, inline15Entry, inline15Output,
    inlineT, inlineRotation, inline15Frame, inline0Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline15WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, v.a, v.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_inline15Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline15Template {s with pc := pc, stack := inline15Entry q rho} =
      some {s with pc := pcAfter pc inline15Template, stack := inline15WordStack q (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline15Frame s.memory q) (inline0Boolean q) =
      PairedLaneWordRound.wordT 0 8 6 q.a q.b q.c q.d q.e
        (inline15Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline15Frame s.memory q)) (inline0Boolean_eq q hupper)).trans
        (rawT_of_boolean (inline15Frame s.memory q) 0 8 6 hfactor hpair hupper rfl rfl))
  have hout : inline15Output q (inlineT (inline15Frame s.memory q) (inline0Boolean q)) rho =
      inline15WordStack q
        (PairedLaneWordRound.wordStep 0 8 6 (inline15Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline15Output, inline15WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline15Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline15Template, stack := vs}) hout)


def inline18Template : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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

def inline18Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 17}

def inline18Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline18Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline18Template_length : inline18Template.length = 53 := rfl

theorem run_inline18Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline18Template {s with pc := pc, stack := inline18Entry q rho} =
      some {s with pc := pcAfter pc inline18Template, stack := inline18Output q (inlineT (inline18Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline18Template, inline18Entry, inline18Output,
    inlineT, inlineRotation, inline18Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline18WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline18Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline19Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline19Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 25}

def inline19Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline19Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline19Template_length : inline19Template.length = 54 := rfl

theorem run_inline19Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline19Template {s with pc := pc, stack := inline19Entry q rho} =
      some {s with pc := pcAfter pc inline19Template, stack := inline19Output q (inlineT (inline19Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline19Template, inline19Entry, inline19Output,
    inlineT, inlineRotation, inline19Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline19WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline19Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline24Template : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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

def inline24Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 25}

def inline24Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline24Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline24Template_length : inline24Template.length = 44 := rfl

theorem run_inline24Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline24Template {s with pc := pc, stack := inline24Entry q rho} =
      some {s with pc := pcAfter pc inline24Template, stack := inline24Output q (singleT (inline24Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline24Template, inline24Entry, inline24Output,
    singleT, inline24Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline24WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline24Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline25Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline25Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 25}

def inline25Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline25Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline25Template_length : inline25Template.length = 54 := rfl

theorem run_inline25Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline25Template {s with pc := pc, stack := inline25Entry q rho} =
      some {s with pc := pcAfter pc inline25Template, stack := inline25Output q (inlineT (inline25Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline25Template, inline25Entry, inline25Output,
    inlineT, inlineRotation, inline25Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline25WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline25Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline30Template : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .op (.Dup ⟨2, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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

def inline30Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 19}

def inline30Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline30Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline30Template_length : inline30Template.length = 44 := rfl

theorem run_inline30Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline30Template {s with pc := pc, stack := inline30Entry q rho} =
      some {s with pc := pcAfter pc inline30Template, stack := inline30Output q (singleT (inline30Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline30Template, inline30Entry, inline30Output,
    singleT, inline30Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline30WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline30Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline31Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
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

def inline31Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 21}

def inline31Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline31Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline31Template_length : inline31Template.length = 54 := rfl

theorem run_inline31Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline31Template {s with pc := pc, stack := inline31Entry q rho} =
      some {s with pc := pcAfter pc inline31Template, stack := inline31Output q (inlineT (inline31Frame s.memory q) (rawBoolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline31Template, inline31Entry, inline31Output,
    inlineT, inlineRotation, inline31Frame, rawBoolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline31WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline31Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline32Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
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

def inline32Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 23}

def inline32Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

def inline32Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline32Template_length : inline32Template.length = 43 := rfl

theorem run_inline32Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline32Template {s with pc := pc, stack := inline32Entry q rho} =
      some {s with pc := pcAfter pc inline32Template, stack := inline32Output q (inlineT (inline32Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline32Template, inline32Entry, inline32Output,
    inlineT, inlineRotation, inline32Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline32WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline32Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline32Template {s with pc := pc, stack := inline32Entry q rho} =
      some {s with pc := pcAfter pc inline32Template, stack := inline32WordStack q (PairedLaneWordRound.wordStep 2 11 9 (inline32Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline32Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 11 9 q.a q.b q.c q.d q.e
        (inline32Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline32Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline32Frame s.memory q) 2 11 9 hfactor hpair hupper rfl rfl))
  have hout : inline32Output q (inlineT (inline32Frame s.memory q) (inline2Boolean q)) rho =
      inline32WordStack q
        (PairedLaneWordRound.wordStep 2 11 9 (inline32Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline32Output, inline32WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline32Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline32Template, stack := vs}) hout)


def inline33Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
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

def inline33Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 25}

def inline33Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline33Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline33Template_length : inline33Template.length = 43 := rfl

theorem run_inline33Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline33Template {s with pc := pc, stack := inline33Entry q rho} =
      some {s with pc := pcAfter pc inline33Template, stack := inline33Output q (inlineT (inline33Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline33Template, inline33Entry, inline33Output,
    inlineT, inlineRotation, inline33Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline33WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline33Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline33Template {s with pc := pc, stack := inline33Entry q rho} =
      some {s with pc := pcAfter pc inline33Template, stack := inline33WordStack q (PairedLaneWordRound.wordStep 2 13 7 (inline33Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline33Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 13 7 q.a q.b q.c q.d q.e
        (inline33Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline33Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline33Frame s.memory q) 2 13 7 hfactor hpair hupper rfl rfl))
  have hout : inline33Output q (inlineT (inline33Frame s.memory q) (inline2Boolean q)) rho =
      inline33WordStack q
        (PairedLaneWordRound.wordStep 2 13 7 (inline33Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline33Output, inline33WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline33Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline33Template, stack := vs}) hout)


def inline34Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline34Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 17}

def inline34Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline34Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline34Template_length : inline34Template.length = 43 := rfl

theorem run_inline34Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline34Template {s with pc := pc, stack := inline34Entry q rho} =
      some {s with pc := pcAfter pc inline34Template, stack := inline34Output q (inlineT (inline34Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline34Template, inline34Entry, inline34Output,
    inlineT, inlineRotation, inline34Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline34WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline34Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline34Template {s with pc := pc, stack := inline34Entry q rho} =
      some {s with pc := pcAfter pc inline34Template, stack := inline34WordStack q (PairedLaneWordRound.wordStep 2 6 15 (inline34Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline34Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 6 15 q.a q.b q.c q.d q.e
        (inline34Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline34Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline34Frame s.memory q) 2 6 15 hfactor hpair hupper rfl rfl))
  have hout : inline34Output q (inlineT (inline34Frame s.memory q) (inline2Boolean q)) rho =
      inline34WordStack q
        (PairedLaneWordRound.wordStep 2 6 15 (inline34Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline34Output, inline34WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline34Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline34Template, stack := vs}) hout)


def inline35Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline35Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 21}

def inline35Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline35Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline35Template_length : inline35Template.length = 43 := rfl

theorem run_inline35Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline35Template {s with pc := pc, stack := inline35Entry q rho} =
      some {s with pc := pcAfter pc inline35Template, stack := inline35Output q (inlineT (inline35Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline35Template, inline35Entry, inline35Output,
    inlineT, inlineRotation, inline35Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline35WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline35Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline35Template {s with pc := pc, stack := inline35Entry q rho} =
      some {s with pc := pcAfter pc inline35Template, stack := inline35WordStack q (PairedLaneWordRound.wordStep 2 7 11 (inline35Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline35Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 7 11 q.a q.b q.c q.d q.e
        (inline35Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline35Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline35Frame s.memory q) 2 7 11 hfactor hpair hupper rfl rfl))
  have hout : inline35Output q (inlineT (inline35Frame s.memory q) (inline2Boolean q)) rho =
      inline35WordStack q
        (PairedLaneWordRound.wordStep 2 7 11 (inline35Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline35Output, inline35WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline35Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline35Template, stack := vs}) hout)


def inline36Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
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

def inline36Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 24}

def inline36Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline36Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline36Template_length : inline36Template.length = 43 := rfl

theorem run_inline36Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline36Template {s with pc := pc, stack := inline36Entry q rho} =
      some {s with pc := pcAfter pc inline36Template, stack := inline36Output q (inlineT (inline36Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline36Template, inline36Entry, inline36Output,
    inlineT, inlineRotation, inline36Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline36WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline36Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline36Template {s with pc := pc, stack := inline36Entry q rho} =
      some {s with pc := pcAfter pc inline36Template, stack := inline36WordStack q (PairedLaneWordRound.wordStep 2 14 8 (inline36Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline36Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 14 8 q.a q.b q.c q.d q.e
        (inline36Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline36Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline36Frame s.memory q) 2 14 8 hfactor hpair hupper rfl rfl))
  have hout : inline36Output q (inlineT (inline36Frame s.memory q) (inline2Boolean q)) rho =
      inline36WordStack q
        (PairedLaneWordRound.wordStep 2 14 8 (inline36Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline36Output, inline36WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline36Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline36Template, stack := vs}) hout)


def inline37Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline37Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline37Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline37Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline37Template_length : inline37Template.length = 43 := rfl

theorem run_inline37Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline37Template {s with pc := pc, stack := inline37Entry q rho} =
      some {s with pc := pcAfter pc inline37Template, stack := inline37Output q (inlineT (inline37Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline37Template, inline37Entry, inline37Output,
    inlineT, inlineRotation, inline37Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline37WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline37Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline37Template {s with pc := pc, stack := inline37Entry q rho} =
      some {s with pc := pcAfter pc inline37Template, stack := inline37WordStack q (PairedLaneWordRound.wordStep 2 9 6 (inline37Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline37Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 9 6 q.a q.b q.c q.d q.e
        (inline37Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline37Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline37Frame s.memory q) 2 9 6 hfactor hpair hupper rfl rfl))
  have hout : inline37Output q (inlineT (inline37Frame s.memory q) (inline2Boolean q)) rho =
      inline37WordStack q
        (PairedLaneWordRound.wordStep 2 9 6 (inline37Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline37Output, inline37WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline37Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline37Template, stack := vs}) hout)


def inline38Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline38Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 26}

def inline38Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline38Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline38Template_length : inline38Template.length = 43 := rfl

theorem run_inline38Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline38Template {s with pc := pc, stack := inline38Entry q rho} =
      some {s with pc := pcAfter pc inline38Template, stack := inline38Output q (inlineT (inline38Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline38Template, inline38Entry, inline38Output,
    inlineT, inlineRotation, inline38Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline38WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline38Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline38Template {s with pc := pc, stack := inline38Entry q rho} =
      some {s with pc := pcAfter pc inline38Template, stack := inline38WordStack q (PairedLaneWordRound.wordStep 2 13 6 (inline38Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline38Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 13 6 q.a q.b q.c q.d q.e
        (inline38Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline38Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline38Frame s.memory q) 2 13 6 hfactor hpair hupper rfl rfl))
  have hout : inline38Output q (inlineT (inline38Frame s.memory q) (inline2Boolean q)) rho =
      inline38WordStack q
        (PairedLaneWordRound.wordStep 2 13 6 (inline38Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline38Output, inline38WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline38Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline38Template, stack := vs}) hout)


def inline39Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

def inline39Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 18}

def inline39Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline39Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline39Template_length : inline39Template.length = 43 := rfl

theorem run_inline39Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline39Template {s with pc := pc, stack := inline39Entry q rho} =
      some {s with pc := pcAfter pc inline39Template, stack := inline39Output q (inlineT (inline39Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline39Template, inline39Entry, inline39Output,
    inlineT, inlineRotation, inline39Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline39WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline39Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline39Template {s with pc := pc, stack := inline39Entry q rho} =
      some {s with pc := pcAfter pc inline39Template, stack := inline39WordStack q (PairedLaneWordRound.wordStep 2 15 14 (inline39Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline39Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 15 14 q.a q.b q.c q.d q.e
        (inline39Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline39Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline39Frame s.memory q) 2 15 14 hfactor hpair hupper rfl rfl))
  have hout : inline39Output q (inlineT (inline39Frame s.memory q) (inline2Boolean q)) rho =
      inline39WordStack q
        (PairedLaneWordRound.wordStep 2 15 14 (inline39Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline39Output, inline39WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline39Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline39Template, stack := vs}) hout)


def inline40Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
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

def inline40Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 20}

def inline40Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline40Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline40Template_length : inline40Template.length = 43 := rfl

theorem run_inline40Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline40Template {s with pc := pc, stack := inline40Entry q rho} =
      some {s with pc := pcAfter pc inline40Template, stack := inline40Output q (inlineT (inline40Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline40Template, inline40Entry, inline40Output,
    inlineT, inlineRotation, inline40Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline40WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline40Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline40Template {s with pc := pc, stack := inline40Entry q rho} =
      some {s with pc := pcAfter pc inline40Template, stack := inline40WordStack q (PairedLaneWordRound.wordStep 2 14 12 (inline40Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline40Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 14 12 q.a q.b q.c q.d q.e
        (inline40Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline40Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline40Frame s.memory q) 2 14 12 hfactor hpair hupper rfl rfl))
  have hout : inline40Output q (inlineT (inline40Frame s.memory q) (inline2Boolean q)) rho =
      inline40WordStack q
        (PairedLaneWordRound.wordStep 2 14 12 (inline40Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline40Output, inline40WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline40Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline40Template, stack := vs}) hout)


def inline41Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline41Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 19}

def inline41Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline41Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline41Template_length : inline41Template.length = 43 := rfl

theorem run_inline41Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline41Template {s with pc := pc, stack := inline41Entry q rho} =
      some {s with pc := pcAfter pc inline41Template, stack := inline41Output q (inlineT (inline41Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline41Template, inline41Entry, inline41Output,
    inlineT, inlineRotation, inline41Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline41WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline41Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline41Template {s with pc := pc, stack := inline41Entry q rho} =
      some {s with pc := pcAfter pc inline41Template, stack := inline41WordStack q (PairedLaneWordRound.wordStep 2 8 13 (inline41Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline41Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 8 13 q.a q.b q.c q.d q.e
        (inline41Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline41Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline41Frame s.memory q) 2 8 13 hfactor hpair hupper rfl rfl))
  have hout : inline41Output q (inlineT (inline41Frame s.memory q) (inline2Boolean q)) rho =
      inline41WordStack q
        (PairedLaneWordRound.wordStep 2 8 13 (inline41Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline41Output, inline41WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline41Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline41Template, stack := vs}) hout)


def inline42Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline42Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 27}

def inline42Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline42Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline42Template_length : inline42Template.length = 43 := rfl

theorem run_inline42Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline42Template {s with pc := pc, stack := inline42Entry q rho} =
      some {s with pc := pcAfter pc inline42Template, stack := inline42Output q (inlineT (inline42Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline42Template, inline42Entry, inline42Output,
    inlineT, inlineRotation, inline42Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline42WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline42Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline42Template {s with pc := pc, stack := inline42Entry q rho} =
      some {s with pc := pcAfter pc inline42Template, stack := inline42WordStack q (PairedLaneWordRound.wordStep 2 13 5 (inline42Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline42Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 13 5 q.a q.b q.c q.d q.e
        (inline42Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline42Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline42Frame s.memory q) 2 13 5 hfactor hpair hupper rfl rfl))
  have hout : inline42Output q (inlineT (inline42Frame s.memory q) (inline2Boolean q)) rho =
      inline42WordStack q
        (PairedLaneWordRound.wordStep 2 13 5 (inline42Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline42Output, inline42WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline42Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline42Template, stack := vs}) hout)


def inline43Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline43Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 18}

def inline43Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline43Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline43Template_length : inline43Template.length = 43 := rfl

theorem run_inline43Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline43Template {s with pc := pc, stack := inline43Entry q rho} =
      some {s with pc := pcAfter pc inline43Template, stack := inline43Output q (inlineT (inline43Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline43Template, inline43Entry, inline43Output,
    inlineT, inlineRotation, inline43Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline43WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline43Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline43Template {s with pc := pc, stack := inline43Entry q rho} =
      some {s with pc := pcAfter pc inline43Template, stack := inline43WordStack q (PairedLaneWordRound.wordStep 2 6 14 (inline43Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline43Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 6 14 q.a q.b q.c q.d q.e
        (inline43Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline43Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline43Frame s.memory q) 2 6 14 hfactor hpair hupper rfl rfl))
  have hout : inline43Output q (inlineT (inline43Frame s.memory q) (inline2Boolean q)) rho =
      inline43WordStack q
        (PairedLaneWordRound.wordStep 2 6 14 (inline43Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline43Output, inline43WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline43Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline43Template, stack := vs}) hout)


def inline44Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline44Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 19}

def inline44Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline44Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline44Template_length : inline44Template.length = 43 := rfl

theorem run_inline44Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline44Template {s with pc := pc, stack := inline44Entry q rho} =
      some {s with pc := pcAfter pc inline44Template, stack := inline44Output q (inlineT (inline44Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline44Template, inline44Entry, inline44Output,
    inlineT, inlineRotation, inline44Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline44WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline44Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline44Template {s with pc := pc, stack := inline44Entry q rho} =
      some {s with pc := pcAfter pc inline44Template, stack := inline44WordStack q (PairedLaneWordRound.wordStep 2 5 13 (inline44Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline44Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 5 13 q.a q.b q.c q.d q.e
        (inline44Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline44Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline44Frame s.memory q) 2 5 13 hfactor hpair hupper rfl rfl))
  have hout : inline44Output q (inlineT (inline44Frame s.memory q) (inline2Boolean q)) rho =
      inline44WordStack q
        (PairedLaneWordRound.wordStep 2 5 13 (inline44Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline44Output, inline44WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline44Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline44Template, stack := vs}) hout)


def inline45Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline45Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 19}

def inline45Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline45Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline45Template_length : inline45Template.length = 43 := rfl

theorem run_inline45Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline45Template {s with pc := pc, stack := inline45Entry q rho} =
      some {s with pc := pcAfter pc inline45Template, stack := inline45Output q (inlineT (inline45Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline45Template, inline45Entry, inline45Output,
    inlineT, inlineRotation, inline45Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline45WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline45Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline45Template {s with pc := pc, stack := inline45Entry q rho} =
      some {s with pc := pcAfter pc inline45Template, stack := inline45WordStack q (PairedLaneWordRound.wordStep 2 12 13 (inline45Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (inline45Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 12 13 q.a q.b q.c q.d q.e
        (inline45Frame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (inline45Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline45Frame s.memory q) 2 12 13 hfactor hpair hupper rfl rfl))
  have hout : inline45Output q (inlineT (inline45Frame s.memory q) (inline2Boolean q)) rho =
      inline45WordStack q
        (PairedLaneWordRound.wordStep 2 12 13 (inline45Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline45Output, inline45WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline45Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline45Template, stack := vs}) hout)


def inline46Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline46Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 25}

def inline46Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline46Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline46Template_length : inline46Template.length = 34 := rfl

theorem run_inline46Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline46Template {s with pc := pc, stack := inline46Entry q rho} =
      some {s with pc := pcAfter pc inline46Template, stack := inline46Output q (singleT (inline46Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline46Template, inline46Entry, inline46Output,
    singleT, inline46Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline46WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline46Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline46Template {s with pc := pc, stack := inline46Entry q rho} =
      some {s with pc := pcAfter pc inline46Template, stack := inline46WordStack q (PairedLaneWordRound.wordStep 2 7 7 (inline46Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline46Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 7 7 q.a q.b q.c q.d q.e
        (inline46Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      ((congrArg (rawT (inline46Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline46Frame s.memory q) 2 7 7 hfactor hpair hupper rfl rfl))
  have hout : inline46Output q (singleT (inline46Frame s.memory q) (inline2Boolean q)) rho =
      inline46WordStack q
        (PairedLaneWordRound.wordStep 2 7 7 (inline46Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline46Output, inline46WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline46Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline46Template, stack := vs}) hout)


def inline47Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .XOR,
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

def inline47Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 27}

def inline47Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline47Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline47Template_length : inline47Template.length = 34 := rfl

theorem run_inline47Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline47Template {s with pc := pc, stack := inline47Entry q rho} =
      some {s with pc := pcAfter pc inline47Template, stack := inline47Output q (singleT (inline47Frame s.memory q) (inline2Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline47Template, inline47Entry, inline47Output,
    singleT, inline47Frame, inline2Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline47WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline47Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq inline47Template {s with pc := pc, stack := inline47Entry q rho} =
      some {s with pc := pcAfter pc inline47Template, stack := inline47WordStack q (PairedLaneWordRound.wordStep 2 5 5 (inline47Frame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : singleT (inline47Frame s.memory q) (inline2Boolean q) =
      PairedLaneWordRound.wordT 2 5 5 q.a q.b q.c q.d q.e
        (inline47Frame s.memory q).message0 q.k :=
    (singleT_eq_rawT _ _ rfl).trans
      ((congrArg (rawT (inline47Frame s.memory q)) (inline2Boolean_eq q hpair)).trans
        (rawT_of_boolean (inline47Frame s.memory q) 2 5 5 hfactor hpair hupper rfl rfl))
  have hout : inline47Output q (singleT (inline47Frame s.memory q) (inline2Boolean q)) rho =
      inline47WordStack q
        (PairedLaneWordRound.wordStep 2 5 5 (inline47Frame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [inline47Output, inline47WordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_inline47Template s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc inline47Template, stack := vs}) hout)


def inline48Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline48Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 17}

def inline48Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline48Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline48Template_length : inline48Template.length = 54 := rfl

theorem run_inline48Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline48Template {s with pc := pc, stack := inline48Entry q rho} =
      some {s with pc := pcAfter pc inline48Template, stack := inline48Output q (inlineT (inline48Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline48Template, inline48Entry, inline48Output,
    inlineT, inlineRotation, inline48Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline48WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline48Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline49Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline49Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 27}

def inline49Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline49Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline49Template_length : inline49Template.length = 54 := rfl

theorem run_inline49Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline49Template {s with pc := pc, stack := inline49Entry q rho} =
      some {s with pc := pcAfter pc inline49Template, stack := inline49Output q (inlineT (inline49Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline49Template, inline49Entry, inline49Output,
    inlineT, inlineRotation, inline49Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline49WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline49Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline50Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
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

def inline50Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 24}

def inline50Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline50Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline50Template_length : inline50Template.length = 54 := rfl

theorem run_inline50Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline50Template {s with pc := pc, stack := inline50Entry q rho} =
      some {s with pc := pcAfter pc inline50Template, stack := inline50Output q (inlineT (inline50Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline50Template, inline50Entry, inline50Output,
    inlineT, inlineRotation, inline50Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline50WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline50Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline51Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
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

def inline51Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 21}

def inline51Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline51Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline51Template_length : inline51Template.length = 54 := rfl

theorem run_inline51Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline51Template {s with pc := pc, stack := inline51Entry q rho} =
      some {s with pc := pcAfter pc inline51Template, stack := inline51Output q (inlineT (inline51Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline51Template, inline51Entry, inline51Output,
    inlineT, inlineRotation, inline51Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline51WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline51Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline52Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline52Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 18}

def inline52Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline52Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline52Template_length : inline52Template.length = 45 := rfl

theorem run_inline52Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline52Template {s with pc := pc, stack := inline52Entry q rho} =
      some {s with pc := pcAfter pc inline52Template, stack := inline52Output q (singleT (inline52Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline52Template, inline52Entry, inline52Output,
    singleT, inline52Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline52WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline52Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline53Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
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

def inline53Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 18}

def inline53Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline53Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline53Template_length : inline53Template.length = 54 := rfl

theorem run_inline53Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline53Template {s with pc := pc, stack := inline53Entry q rho} =
      some {s with pc := pcAfter pc inline53Template, stack := inline53Output q (inlineT (inline53Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline53Template, inline53Entry, inline53Output,
    inlineT, inlineRotation, inline53Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline53WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline53Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline54Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline54Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline54Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline54Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline54Template_length : inline54Template.length = 54 := rfl

theorem run_inline54Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline54Template {s with pc := pc, stack := inline54Entry q rho} =
      some {s with pc := pcAfter pc inline54Template, stack := inline54Output q (inlineT (inline54Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline54Template, inline54Entry, inline54Output,
    inlineT, inlineRotation, inline54Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline54WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline54Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline55Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline55Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 18}

def inline55Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline55Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline55Template_length : inline55Template.length = 54 := rfl

theorem run_inline55Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline55Template {s with pc := pc, stack := inline55Entry q rho} =
      some {s with pc := pcAfter pc inline55Template, stack := inline55Output q (inlineT (inline55Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline55Template, inline55Entry, inline55Output,
    inlineT, inlineRotation, inline55Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline55WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline55Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline56Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline56Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 26}

def inline56Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline56Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline56Template_length : inline56Template.length = 54 := rfl

theorem run_inline56Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline56Template {s with pc := pc, stack := inline56Entry q rho} =
      some {s with pc := pcAfter pc inline56Template, stack := inline56Output q (inlineT (inline56Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline56Template, inline56Entry, inline56Output,
    inlineT, inlineRotation, inline56Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline56WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline56Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline57Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
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

def inline57Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 23}

def inline57Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline57Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline57Template_length : inline57Template.length = 54 := rfl

theorem run_inline57Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline57Template {s with pc := pc, stack := inline57Entry q rho} =
      some {s with pc := pcAfter pc inline57Template, stack := inline57Output q (inlineT (inline57Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline57Template, inline57Entry, inline57Output,
    inlineT, inlineRotation, inline57Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline57WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline57Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline58Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline58Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 20}

def inline58Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline58Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline58Template_length : inline58Template.length = 54 := rfl

theorem run_inline58Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline58Template {s with pc := pc, stack := inline58Entry q rho} =
      some {s with pc := pcAfter pc inline58Template, stack := inline58Output q (inlineT (inline58Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline58Template, inline58Entry, inline58Output,
    inlineT, inlineRotation, inline58Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline58WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline58Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline59Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline59Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 23}

def inline59Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline59Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline59Template_length : inline59Template.length = 54 := rfl

theorem run_inline59Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline59Template {s with pc := pc, stack := inline59Entry q rho} =
      some {s with pc := pcAfter pc inline59Template, stack := inline59Output q (inlineT (inline59Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline59Template, inline59Entry, inline59Output,
    inlineT, inlineRotation, inline59Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline59WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline59Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline60Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline60Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 20}

def inline60Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline60Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline60Template_length : inline60Template.length = 54 := rfl

theorem run_inline60Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline60Template {s with pc := pc, stack := inline60Entry q rho} =
      some {s with pc := pcAfter pc inline60Template, stack := inline60Output q (inlineT (inline60Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline60Template, inline60Entry, inline60Output,
    inlineT, inlineRotation, inline60Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline60WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline60Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline61Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline61Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 27}

def inline61Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline61Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline61Template_length : inline61Template.length = 54 := rfl

theorem run_inline61Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline61Template {s with pc := pc, stack := inline61Entry q rho} =
      some {s with pc := pcAfter pc inline61Template, stack := inline61Output q (inlineT (inline61Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline61Template, inline61Entry, inline61Output,
    inlineT, inlineRotation, inline61Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline61WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline61Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline62Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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

def inline62Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 17}

def inline62Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def inline62Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.d, q.b, value, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline62Template_length : inline62Template.length = 54 := rfl

theorem run_inline62Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline62Template {s with pc := pc, stack := inline62Entry q rho} =
      some {s with pc := pcAfter pc inline62Template, stack := inline62Output q (inlineT (inline62Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline62Template, inline62Entry, inline62Output,
    inlineT, inlineRotation, inline62Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline62WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.e, v.c, v.b, q.upper, v.a, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline62Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline63Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op .NOT,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨7, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
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

def inline63Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 24}

def inline63Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.e, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.k, q.lower] ++ rho

def inline63Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.e, value, q.b, q.upper, q.d, q.factor, q.pair, q.k, q.lower] ++ rho

theorem inline63Template_length : inline63Template.length = 54 := rfl

theorem run_inline63Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline63Template {s with pc := pc, stack := inline63Entry q rho} =
      some {s with pc := pcAfter pc inline63Template, stack := inline63Output q (inlineT (inline63Frame s.memory q) (inline3Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline63Template, inline63Entry, inline63Output,
    inlineT, inlineRotation, inline63Frame, inline3Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline63WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, v.a, v.b, v.c, q.upper, v.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_inline63Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline64Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
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

def inline64Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 320), leftShift0 := UInt256.ofNat 23, rightShift0 := UInt256.ofNat 24}

def inline64Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

def inline64Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline64Template_length : inline64Template.length = 48 := rfl

theorem run_inline64Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline64Template {s with pc := pc, stack := inline64Entry q rho} =
      some {s with pc := pcAfter pc inline64Template, stack := inline64Output q (inlineT (inline64Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline64Template, inline64Entry, inline64Output,
    inlineT, inlineRotation, inline64Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline64WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline64Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline65Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline65Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 688) (MachineState.readWord memory 192), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 27}

def inline65Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline65Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline65Template_length : inline65Template.length = 48 := rfl

theorem run_inline65Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline65Template {s with pc := pc, stack := inline65Entry q rho} =
      some {s with pc := pcAfter pc inline65Template, stack := inline65Output q (inlineT (inline65Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline65Template, inline65Entry, inline65Output,
    inlineT, inlineRotation, inline65Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline65WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline65Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline66Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline66Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 352), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 20}

def inline66Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline66Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline66Template_length : inline66Template.length = 48 := rfl

theorem run_inline66Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline66Template {s with pc := pc, stack := inline66Entry q rho} =
      some {s with pc := pcAfter pc inline66Template, stack := inline66Output q (inlineT (inline66Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline66Template, inline66Entry, inline66Output,
    inlineT, inlineRotation, inline66Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline66WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline66Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline67Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
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

def inline67Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 23}

def inline67Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline67Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline67Template_length : inline67Template.length = 48 := rfl

theorem run_inline67Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline67Template {s with pc := pc, stack := inline67Entry q rho} =
      some {s with pc := pcAfter pc inline67Template, stack := inline67Output q (inlineT (inline67Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline67Template, inline67Entry, inline67Output,
    inlineT, inlineRotation, inline67Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline67WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline67Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline68Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline68Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 240) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 20}

def inline68Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline68Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline68Template_length : inline68Template.length = 48 := rfl

theorem run_inline68Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline68Template {s with pc := pc, stack := inline68Entry q rho} =
      some {s with pc := pcAfter pc inline68Template, stack := inline68Output q (inlineT (inline68Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline68Template, inline68Entry, inline68Output,
    inlineT, inlineRotation, inline68Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline68WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline68Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline69Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline69Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 576), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 27}

def inline69Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline69Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline69Template_length : inline69Template.length = 48 := rfl

theorem run_inline69Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline69Template {s with pc := pc, stack := inline69Entry q rho} =
      some {s with pc := pcAfter pc inline69Template, stack := inline69Output q (inlineT (inline69Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline69Template, inline69Entry, inline69Output,
    inlineT, inlineRotation, inline69Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline69WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline69Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline70Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline70Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 18}

def inline70Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline70Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline70Template_length : inline70Template.length = 48 := rfl

theorem run_inline70Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline70Template {s with pc := pc, stack := inline70Entry q rho} =
      some {s with pc := pcAfter pc inline70Template, stack := inline70Output q (inlineT (inline70Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline70Template, inline70Entry, inline70Output,
    inlineT, inlineRotation, inline70Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline70WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline70Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline71Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline71Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 432) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 26}

def inline71Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline71Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline71Template_length : inline71Template.length = 48 := rfl

theorem run_inline71Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline71Template {s with pc := pc, stack := inline71Entry q rho} =
      some {s with pc := pcAfter pc inline71Template, stack := inline71Output q (inlineT (inline71Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline71Template, inline71Entry, inline71Output,
    inlineT, inlineRotation, inline71Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline71WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline71Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline72Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline72Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 640), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 24}

def inline72Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline72Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline72Template_length : inline72Template.length = 48 := rfl

theorem run_inline72Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline72Template {s with pc := pc, stack := inline72Entry q rho} =
      some {s with pc := pcAfter pc inline72Template, stack := inline72Output q (inlineT (inline72Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline72Template, inline72Entry, inline72Output,
    inlineT, inlineRotation, inline72Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline72WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline72Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline73Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline73Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 272) (MachineState.readWord memory 224), leftShift0 := UInt256.ofNat 20, rightShift0 := UInt256.ofNat 19}

def inline73Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline73Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline73Template_length : inline73Template.length = 48 := rfl

theorem run_inline73Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline73Template {s with pc := pc, stack := inline73Entry q rho} =
      some {s with pc := pcAfter pc inline73Template, stack := inline73Output q (inlineT (inline73Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline73Template, inline73Entry, inline73Output,
    inlineT, inlineRotation, inline73Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline73WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline73Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline74Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 19),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 26),
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

def inline74Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 288), leftShift0 := UInt256.ofNat 19, rightShift0 := UInt256.ofNat 26}

def inline74Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline74Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline74Template_length : inline74Template.length = 48 := rfl

theorem run_inline74Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline74Template {s with pc := pc, stack := inline74Entry q rho} =
      some {s with pc := pcAfter pc inline74Template, stack := inline74Output q (inlineT (inline74Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline74Template, inline74Entry, inline74Output,
    inlineT, inlineRotation, inline74Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline74WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline74Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline75Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 18),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 27),
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

def inline75Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 656) (MachineState.readWord memory 448), leftShift0 := UInt256.ofNat 18, rightShift0 := UInt256.ofNat 27}

def inline75Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline75Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline75Template_length : inline75Template.length = 48 := rfl

theorem run_inline75Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline75Template {s with pc := pc, stack := inline75Entry q rho} =
      some {s with pc := pcAfter pc inline75Template, stack := inline75Output q (inlineT (inline75Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline75Template, inline75Entry, inline75Output,
    inlineT, inlineRotation, inline75Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline75WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline75Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline76Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline76Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 544), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 17}

def inline76Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline76Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline76Template_length : inline76Template.length = 48 := rfl

theorem run_inline76Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline76Template {s with pc := pc, stack := inline76Entry q rho} =
      some {s with pc := pcAfter pc inline76Template, stack := inline76Output q (inlineT (inline76Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline76Template, inline76Entry, inline76Output,
    inlineT, inlineRotation, inline76Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline76WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline76Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline77Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline77Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 304) (MachineState.readWord memory 384), leftShift0 := UInt256.ofNat 24, rightShift0 := UInt256.ofNat 19}

def inline77Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline77Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline77Template_length : inline77Template.length = 48 := rfl

theorem run_inline77Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline77Template {s with pc := pc, stack := inline77Entry q rho} =
      some {s with pc := pcAfter pc inline77Template, stack := inline77Output q (inlineT (inline77Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline77Template, inline77Entry, inline77Output,
    inlineT, inlineRotation, inline77Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline77WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline77Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline78Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨9, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨4, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline78Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 27, rightShift0 := UInt256.ofNat 21}

def inline78Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def inline78Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, q.b, value, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem inline78Template_length : inline78Template.length = 48 := rfl

theorem run_inline78Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline78Template {s with pc := pc, stack := inline78Entry q rho} =
      some {s with pc := pcAfter pc inline78Template, stack := inline78Output q (inlineT (inline78Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline78Template, inline78Entry, inline78Output,
    inlineT, inlineRotation, inline78Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline78WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.c, v.b, q.upper, v.a, q.factor, q.pair, v.e, q.lower] ++ rho

theorem run_inline78Template_word (s : State) (pc : UInt256) (q : Frame)
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


def inline79Template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨6, by decide⟩),
   .op .XOR,
   .op (.Dup ⟨3, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨7, by decide⟩),
   .op .OR,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
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

def inline79Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 21}

def inline79Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.upper, q.a, q.factor, q.pair, q.e, q.lower] ++ rho

def inline79Output (q : Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, q.k, value, q.b, q.upper, q.d, q.factor, q.pair, q.e, q.lower] ++ rho

theorem inline79Template_length : inline79Template.length = 48 := rfl

theorem run_inline79Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq inline79Template {s with pc := pc, stack := inline79Entry q rho} =
      some {s with pc := pcAfter pc inline79Template, stack := inline79Output q (inlineT (inline79Frame s.memory q) (inline4Boolean q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [inline79Template, inline79Entry, inline79Output,
    inlineT, inlineRotation, inline79Frame, inline4Boolean, inlineProduct, rawC10,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl, rfl⟩

def inline79WordStack (q : Frame) (v : PairedLaneWordRound.WordLane)
    (rho : List UInt256) : List UInt256 :=
  [v.d, q.k, v.b, v.c, q.upper, v.e, q.factor, q.pair, v.a, q.lower] ++ rho

theorem run_inline79Template_word (s : State) (pc : UInt256) (q : Frame)
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

def call16Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 1920),
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
   .op .JUMP]

def call16Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 400) (MachineState.readWord memory 416), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23, message1 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 320), leftShift1 := UInt256.ofNat 26, rightShift1 := UInt256.ofNat 19, ret := UInt256.ofNat 1920}

def call16Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.k, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem call16Template_length : call16Template.length = 24 := rfl

theorem run_call16Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true) :
    runInstrSeq call16Template {s with pc := pc, stack := call16Entry q rho} =
      some {s with pc := UInt256.ofNat 5168, stack := entryStack (call16Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call16Template, call16Entry, call16Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

theorem run_call16Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true)
    (hreturn : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 1920).toNat = true)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq (call16Template ++ fullTemplate)
        {s with pc := pc, stack := call16Entry q rho} =
      some {s with pc := UInt256.ofNat 1920, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 6 13 (call16Frame s.memory q).message1 q.k (PairedLaneWordRound.wordStep 1 7 9 (call16Frame s.memory q).message0 q.k (frameLane q))) rho} := by
  have h0 := run_call16Template s pc q rho hstack hrun hactive hvalid
  have h1 := run_fullTemplate_word s (UInt256.ofNat 5168) (call16Frame s.memory q)
    rho hstack hrun hreturn 7 9 6 13 hfactor hpair hupper rfl rfl rfl rfl
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1


def call20Template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 2077),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 24),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 384),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 624),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .push ⟨2, by decide⟩ (UInt256.ofNat 512),
   .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 208),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
   .op .JUMP]

def call20Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 208) (MachineState.readWord memory 512), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 20, message1 := UInt256.lor (MachineState.readWord memory 624) (MachineState.readWord memory 384), leftShift1 := UInt256.ofNat 23, rightShift1 := UInt256.ofNat 24, ret := UInt256.ofNat 2077}

def call20Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem call20Template_length : call20Template.length = 21 := rfl

theorem run_call20Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true) :
    runInstrSeq call20Template {s with pc := pc, stack := call20Entry q rho} =
      some {s with pc := UInt256.ofNat 5168, stack := entryStack (call20Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call20Template, call20Entry, call20Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

theorem run_call20Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true)
    (hreturn : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 2077).toNat = true)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq (call20Template ++ fullTemplate)
        {s with pc := pc, stack := call20Entry q rho} =
      some {s with pc := UInt256.ofNat 2077, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 9 8 (call20Frame s.memory q).message1 q.k (PairedLaneWordRound.wordStep 1 11 12 (call20Frame s.memory q).message0 q.k (frameLane q))) rho} := by
  have h0 := run_call20Template s pc q rho hstack hrun hactive hvalid
  have h1 := run_fullTemplate_word s (UInt256.ofNat 5168) (call20Frame s.memory q)
    rho hstack hrun hreturn 11 12 9 8 hfactor hpair hupper rfl rfl rfl rfl
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1


def call22Template : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 2116),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 21),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 288),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 528),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .push ⟨2, by decide⟩ (UInt256.ofNat 672),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 368),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
   .op .JUMP]

def call22Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 368) (MachineState.readWord memory 672), leftShift0 := UInt256.ofNat 25, rightShift0 := UInt256.ofNat 23, message1 := UInt256.lor (MachineState.readWord memory 528) (MachineState.readWord memory 288), leftShift1 := UInt256.ofNat 17, rightShift1 := UInt256.ofNat 21, ret := UInt256.ofNat 2116}

def call22Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem call22Template_length : call22Template.length = 23 := rfl

theorem run_call22Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true) :
    runInstrSeq call22Template {s with pc := pc, stack := call22Entry q rho} =
      some {s with pc := UInt256.ofNat 5168, stack := entryStack (call22Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call22Template, call22Entry, call22Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

theorem run_call22Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true)
    (hreturn : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 2116).toNat = true)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq (call22Template ++ fullTemplate)
        {s with pc := pc, stack := call22Entry q rho} =
      some {s with pc := UInt256.ofNat 2116, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 15 11 (call22Frame s.memory q).message1 q.k (PairedLaneWordRound.wordStep 1 7 9 (call22Frame s.memory q).message0 q.k (frameLane q))) rho} := by
  have h0 := run_call22Template s pc q rho hstack hrun hactive hvalid
  have h1 := run_fullTemplate_word s (UInt256.ofNat 5168) (call22Frame s.memory q)
    rho hstack hrun hreturn 7 9 15 11 hfactor hpair hupper rfl rfl rfl rfl
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1


def call26Template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 2264),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 25),
   .push ⟨1, by decide⟩ (UInt256.ofNat 23),
   .op (.Swap ⟨1, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 352),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 592),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 20),
   .push ⟨1, by decide⟩ (UInt256.ofNat 17),
   .push ⟨2, by decide⟩ (UInt256.ofNat 480),
   .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 464),
   .op .MLOAD,
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
   .op .JUMP]

def call26Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 464) (MachineState.readWord memory 480), leftShift0 := UInt256.ofNat 17, rightShift0 := UInt256.ofNat 20, message1 := UInt256.lor (MachineState.readWord memory 592) (MachineState.readWord memory 352), leftShift1 := UInt256.ofNat 23, rightShift1 := UInt256.ofNat 25, ret := UInt256.ofNat 2264}

def call26Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem call26Template_length : call26Template.length = 21 := rfl

theorem run_call26Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true) :
    runInstrSeq call26Template {s with pc := pc, stack := call26Entry q rho} =
      some {s with pc := UInt256.ofNat 5168, stack := entryStack (call26Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call26Template, call26Entry, call26Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

theorem run_call26Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true)
    (hreturn : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 2264).toNat = true)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq (call26Template ++ fullTemplate)
        {s with pc := pc, stack := call26Entry q rho} =
      some {s with pc := UInt256.ofNat 2264, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 9 7 (call26Frame s.memory q).message1 q.k (PairedLaneWordRound.wordStep 1 15 12 (call26Frame s.memory q).message0 q.k (frameLane q))) rho} := by
  have h0 := run_call26Template s pc q rho hstack hrun hactive hvalid
  have h1 := run_fullTemplate_word s (UInt256.ofNat 5168) (call26Frame s.memory q)
    rho hstack hrun hreturn 15 12 9 7 hfactor hpair hupper rfl rfl rfl rfl
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1


def call28Template : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat 2303),
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
   .push ⟨2, by decide⟩ (UInt256.ofNat 5168),
   .op .JUMP]

def call28Frame (memory : ByteArray) (q : Frame) : Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 336) (MachineState.readWord memory 256), leftShift0 := UInt256.ofNat 21, rightShift0 := UInt256.ofNat 26, message1 := UInt256.lor (MachineState.readWord memory 496) (MachineState.readWord memory 640), leftShift1 := UInt256.ofNat 25, rightShift1 := UInt256.ofNat 17, ret := UInt256.ofNat 2303}

def call28Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem call28Template_length : call28Template.length = 23 := rfl

theorem run_call28Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true) :
    runInstrSeq call28Template {s with pc := pc, stack := call28Entry q rho} =
      some {s with pc := UInt256.ofNat 5168, stack := entryStack (call28Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 18) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [call28Template, call28Entry, call28Frame, entryStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, hvalid]

theorem run_call28Template_word (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 5168 = true)
    (hreturn : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 2303).toNat = true)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) :
    runInstrSeq (call28Template ++ fullTemplate)
        {s with pc := pc, stack := call28Entry q rho} =
      some {s with pc := UInt256.ofNat 2303, stack := wordReturnStack q (PairedLaneWordRound.wordStep 1 7 15 (call28Frame s.memory q).message1 q.k (PairedLaneWordRound.wordStep 1 11 6 (call28Frame s.memory q).message0 q.k (frameLane q))) rho} := by
  have h0 := run_call28Template s pc q rho hstack hrun hactive hvalid
  have h1 := run_fullTemplate_word s (UInt256.ofNat 5168) (call28Frame s.memory q)
    rho hstack hrun hreturn 11 6 7 15 hfactor hpair hupper rfl rfl rfl rfl
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1


def group0Template : List Instr :=
  [.push ⟨20, by decide⟩ (UInt256.ofNat 460344169260758029377710773882198039553172832256)]

def group0Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group0Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 460344169260758029377710773882198039553172832256, q.a, q.b, q.c, q.d, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group0Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group0Template {s with pc := pc, stack := group0Entry q rho} =
      some {s with pc := pcAfter pc group0Template, stack := group0Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group0Template, group0Entry, group0Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
    Instr.size, Nat.add_assoc, hrun, hcap]


def group16Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push ⟨20, by decide⟩ (UInt256.ofNat 526962527014005041256681316140890030896371104153)]

def group16Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def group16Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 526962527014005041256681316140890030896371104153, q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower] ++ rho

theorem run_group16Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group16Template {s with pc := pc, stack := group16Entry q rho} =
      some {s with pc := pcAfter pc group16Template, stack := group16Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group16Template, group16Entry, group16Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl


def return18Template : List Instr :=
  [.op .JUMPDEST]

def return18Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def return18Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_return18Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq return18Template {s with pc := pc, stack := return18Entry q rho} =
      some {s with pc := pcAfter pc return18Template, stack := return18Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [return18Template, return18Entry, return18Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, Nat.add_assoc, hrun, hcap]
  rfl


def return24Template : List Instr :=
  [.op .JUMPDEST]

def return24Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def return24Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_return24Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq return24Template {s with pc := pc, stack := return24Entry q rho} =
      some {s with pc := pcAfter pc return24Template, stack := return24Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [return24Template, return24Entry, return24Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, Nat.add_assoc, hrun, hcap]
  rfl


def return30Template : List Instr :=
  [.op .JUMPDEST]

def return30Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def return30Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.a, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

theorem run_return30Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq return30Template {s with pc := pc, stack := return30Entry q rho} =
      some {s with pc := pcAfter pc return30Template, stack := return30Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [return30Template, return30Entry, return30Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, Nat.add_assoc, hrun, hcap]
  rfl


def group32Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push ⟨20, by decide⟩ (UInt256.ofNat 624783161132376868856603395408315258898134723489)]

def group32Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def group32Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 624783161132376868856603395408315258898134723489, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem run_group32Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group32Template {s with pc := pc, stack := group32Entry q rho} =
      some {s with pc := pcAfter pc group32Template, stack := group32Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group32Template, group32Entry, group32Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl


def group48Template : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push ⟨20, by decide⟩ (UInt256.ofNat 698938013802679700166637234969497128417458109660)]

def group48Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def group48Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 698938013802679700166637234969497128417458109660, q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

theorem run_group48Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group48Template {s with pc := pc, stack := group48Entry q rho} =
      some {s with pc := pcAfter pc group48Template, stack := group48Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group48Template, group48Entry, group48Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl


def group64Template : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push ⟨4, by decide⟩ (UInt256.ofNat 2840853838)]

def group64Entry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.k, q.lower] ++ rho

def group64Output (q : Frame) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 2840853838, q.a, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.d, q.lower] ++ rho

theorem run_group64Template (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group64Template {s with pc := pc, stack := group64Entry q rho} =
      some {s with pc := pcAfter pc group64Template, stack := group64Output q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [group64Template, group64Entry, group64Output,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl


def coreExitTemplate : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .POP]

def coreExitEntry (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

def coreExitOutput (q : Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.upper, q.e, q.factor, q.pair, q.a, q.lower] ++ rho

theorem run_coreExitTemplate (s : State) (pc : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq coreExitTemplate {s with pc := pc, stack := coreExitEntry q rho} =
      some {s with pc := pcAfter pc coreExitTemplate, stack := coreExitOutput q rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [coreExitTemplate, coreExitEntry, coreExitOutput,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  rfl


structure CoreFrame where
  lane : PairedLaneWordRound.WordLane
  k : UInt256

def CoreFrame.frame (f : CoreFrame) : Frame :=
  ⟨f.lane.a, f.lane.b, f.lane.c, f.lane.d, f.lane.e,
    PairedLaneWordRotate.factorWord, pairWord, upperWord, lowerWord, f.k,
    0, 0, 0, 0, 0, 0, 0⟩

inductive CoreReg where
  | a | b | c | d | e | factor | pair | upper | lower | k
  deriving DecidableEq

def CoreReg.word (r : CoreReg) (f : CoreFrame) : UInt256 :=
  match r with
  | .a => f.lane.a | .b => f.lane.b | .c => f.lane.c
  | .d => f.lane.d | .e => f.lane.e
  | .factor => PairedLaneWordRotate.factorWord | .pair => pairWord
  | .upper => upperWord | .lower => lowerWord | .k => f.k

def coreStack (shape : List CoreReg) (f : CoreFrame) (rho : List UInt256) : List UInt256 :=
  shape.map (fun r => r.word f) ++ rho

def CoreJumpValid (s : State) : Prop :=
  ∀ dest ∈ [5168, 1920, 2077, 2116, 2264, 2303],
    Decode.isValidJumpDest s.executionEnv.code dest = true

/-- A small, exact instruction path with its generic frame transition. -/
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




theorem group0Template_pc : pcAfter (UInt256.ofNat 960) group0Template = UInt256.ofNat 981 := rfl

def group0Block : CoreBlock 960 981 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group0Template
  eval := fun _memory f => {f with k := UInt256.ofNat 460344169260758029377710773882198039553172832256}
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_group0Template s (UInt256.ofNat 960) f.frame rho hstack hrun
    rw [group0Template_pc] at h
    exact h


theorem inline0Template_pc : pcAfter (UInt256.ofNat 981) inline0Template = UInt256.ofNat 1035 := rfl

def inline0Block : CoreBlock 981 1035 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline0Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 11 8 (inline0Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline0Template_word s (UInt256.ofNat 981) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline0Template_pc] at h
    exact h


theorem inline1Template_pc : pcAfter (UInt256.ofNat 1035) inline1Template = UInt256.ofNat 1089 := rfl

def inline1Block : CoreBlock 1035 1089 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline1Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 14 9 (inline1Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline1Template_word s (UInt256.ofNat 1035) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline1Template_pc] at h
    exact h


theorem inline2Template_pc : pcAfter (UInt256.ofNat 1089) inline2Template = UInt256.ofNat 1144 := rfl

def inline2Block : CoreBlock 1089 1144 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline2Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 15 9 (inline2Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline2Template_word s (UInt256.ofNat 1089) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline2Template_pc] at h
    exact h


theorem inline3Template_pc : pcAfter (UInt256.ofNat 1144) inline3Template = UInt256.ofNat 1198 := rfl

def inline3Block : CoreBlock 1144 1198 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline3Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 12 11 (inline3Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline3Template_word s (UInt256.ofNat 1144) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline3Template_pc] at h
    exact h


theorem inline4Template_pc : pcAfter (UInt256.ofNat 1198) inline4Template = UInt256.ofNat 1253 := rfl

def inline4Block : CoreBlock 1198 1253 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline4Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 5 13 (inline4Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline4Template_word s (UInt256.ofNat 1198) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline4Template_pc] at h
    exact h


theorem inline5Template_pc : pcAfter (UInt256.ofNat 1253) inline5Template = UInt256.ofNat 1308 := rfl

def inline5Block : CoreBlock 1253 1308 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline5Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 8 15 (inline5Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline5Template_word s (UInt256.ofNat 1253) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline5Template_pc] at h
    exact h


theorem inline6Template_pc : pcAfter (UInt256.ofNat 1308) inline6Template = UInt256.ofNat 1363 := rfl

def inline6Block : CoreBlock 1308 1363 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline6Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 7 15 (inline6Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline6Template_word s (UInt256.ofNat 1308) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline6Template_pc] at h
    exact h


theorem inline7Template_pc : pcAfter (UInt256.ofNat 1363) inline7Template = UInt256.ofNat 1418 := rfl

def inline7Block : CoreBlock 1363 1418 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline7Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 9 5 (inline7Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline7Template_word s (UInt256.ofNat 1363) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline7Template_pc] at h
    exact h


theorem inline8Template_pc : pcAfter (UInt256.ofNat 1418) inline8Template = UInt256.ofNat 1473 := rfl

def inline8Block : CoreBlock 1418 1473 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline8Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 11 7 (inline8Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline8Template_word s (UInt256.ofNat 1418) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline8Template_pc] at h
    exact h


theorem inline9Template_pc : pcAfter (UInt256.ofNat 1473) inline9Template = UInt256.ofNat 1528 := rfl

def inline9Block : CoreBlock 1473 1528 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline9Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 13 7 (inline9Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline9Template_word s (UInt256.ofNat 1473) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline9Template_pc] at h
    exact h


theorem inline10Template_pc : pcAfter (UInt256.ofNat 1528) inline10Template = UInt256.ofNat 1583 := rfl

def inline10Block : CoreBlock 1528 1583 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline10Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 14 8 (inline10Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline10Template_word s (UInt256.ofNat 1528) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline10Template_pc] at h
    exact h


theorem inline11Template_pc : pcAfter (UInt256.ofNat 1583) inline11Template = UInt256.ofNat 1638 := rfl

def inline11Block : CoreBlock 1583 1638 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline11Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 15 11 (inline11Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline11Template_word s (UInt256.ofNat 1583) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline11Template_pc] at h
    exact h


theorem inline12Template_pc : pcAfter (UInt256.ofNat 1638) inline12Template = UInt256.ofNat 1692 := rfl

def inline12Block : CoreBlock 1638 1692 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline12Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 6 14 (inline12Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline12Template_word s (UInt256.ofNat 1638) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline12Template_pc] at h
    exact h


theorem inline13Template_pc : pcAfter (UInt256.ofNat 1692) inline13Template = UInt256.ofNat 1747 := rfl

def inline13Block : CoreBlock 1692 1747 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline13Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 7 14 (inline13Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline13Template_word s (UInt256.ofNat 1692) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline13Template_pc] at h
    exact h


theorem inline14Template_pc : pcAfter (UInt256.ofNat 1747) inline14Template = UInt256.ofNat 1802 := rfl

def inline14Block : CoreBlock 1747 1802 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := inline14Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 9 12 (inline14Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline14Template_word s (UInt256.ofNat 1747) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline14Template_pc] at h
    exact h


theorem inline15Template_pc : pcAfter (UInt256.ofNat 1802) inline15Template = UInt256.ofNat 1857 := rfl

def inline15Block : CoreBlock 1802 1857 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := inline15Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 0 8 6 (inline15Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline15Template_word s (UInt256.ofNat 1802) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline15Template_pc] at h
    exact h


theorem group16Template_pc : pcAfter (UInt256.ofNat 1857) group16Template = UInt256.ofNat 1880 := rfl

def group16Block : CoreBlock 1857 1880 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := group16Template
  eval := fun _memory f => {f with k := UInt256.ofNat 526962527014005041256681316140890030896371104153}
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_group16Template s (UInt256.ofNat 1857) f.frame rho hstack hrun
    rw [group16Template_pc] at h
    exact h


def call16Block : CoreBlock 1880 1920 [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := (call16Template ++ fullTemplate)
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 6 13 (call16Frame memory f.frame).message1 f.k (PairedLaneWordRound.wordStep 1 7 9 (call16Frame memory f.frame).message0 f.k f.lane)}
  run := by
    intro s f rho hstack hrun hactive hvalid
    have hh := hvalid 5168 (by decide)
    have hr := hvalid 1920 (by decide)
    have h := run_call16Template_word s (UInt256.ofNat 1880) f.frame rho
      hstack hrun hactive hh hr rfl rfl rfl
    exact h


theorem return18Template_pc : pcAfter (UInt256.ofNat 1920) return18Template = UInt256.ofNat 1921 := rfl

def return18Block : CoreBlock 1920 1921 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := return18Template
  eval := fun _memory f => f
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_return18Template s (UInt256.ofNat 1920) f.frame rho hstack hrun
    rw [return18Template_pc] at h
    exact h


theorem inline18Template_pc : pcAfter (UInt256.ofNat 1921) inline18Template = UInt256.ofNat 1981 := rfl

def inline18Block : CoreBlock 1921 1981 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline18Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 8 15 (inline18Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline18Template_word s (UInt256.ofNat 1921) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline18Template_pc] at h
    exact h


theorem inline19Template_pc : pcAfter (UInt256.ofNat 1981) inline19Template = UInt256.ofNat 2041 := rfl

def inline19Block : CoreBlock 1981 2041 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline19Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 13 7 (inline19Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline19Template_word s (UInt256.ofNat 1981) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline19Template_pc] at h
    exact h


def call20Block : CoreBlock 2041 2077 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := (call20Template ++ fullTemplate)
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 9 8 (call20Frame memory f.frame).message1 f.k (PairedLaneWordRound.wordStep 1 11 12 (call20Frame memory f.frame).message0 f.k f.lane)}
  run := by
    intro s f rho hstack hrun hactive hvalid
    have hh := hvalid 5168 (by decide)
    have hr := hvalid 2077 (by decide)
    have h := run_call20Template_word s (UInt256.ofNat 2041) f.frame rho
      hstack hrun hactive hh hr rfl rfl rfl
    exact h


def call22Block : CoreBlock 2077 2116 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := (call22Template ++ fullTemplate)
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 15 11 (call22Frame memory f.frame).message1 f.k (PairedLaneWordRound.wordStep 1 7 9 (call22Frame memory f.frame).message0 f.k f.lane)}
  run := by
    intro s f rho hstack hrun hactive hvalid
    have hh := hvalid 5168 (by decide)
    have hr := hvalid 2116 (by decide)
    have h := run_call22Template_word s (UInt256.ofNat 2077) f.frame rho
      hstack hrun hactive hh hr rfl rfl rfl
    exact h


theorem return24Template_pc : pcAfter (UInt256.ofNat 2116) return24Template = UInt256.ofNat 2117 := rfl

def return24Block : CoreBlock 2116 2117 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := return24Template
  eval := fun _memory f => f
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_return24Template s (UInt256.ofNat 2116) f.frame rho hstack hrun
    rw [return24Template_pc] at h
    exact h


theorem inline24Template_pc : pcAfter (UInt256.ofNat 2117) inline24Template = UInt256.ofNat 2167 := rfl

def inline24Block : CoreBlock 2117 2167 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline24Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 7 (inline24Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline24Template_word s (UInt256.ofNat 2117) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline24Template_pc] at h
    exact h


theorem inline25Template_pc : pcAfter (UInt256.ofNat 2167) inline25Template = UInt256.ofNat 2227 := rfl

def inline25Block : CoreBlock 2167 2227 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline25Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 12 7 (inline25Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline25Template_word s (UInt256.ofNat 2167) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline25Template_pc] at h
    exact h


def call26Block : CoreBlock 2227 2264 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := (call26Template ++ fullTemplate)
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 9 7 (call26Frame memory f.frame).message1 f.k (PairedLaneWordRound.wordStep 1 15 12 (call26Frame memory f.frame).message0 f.k f.lane)}
  run := by
    intro s f rho hstack hrun hactive hvalid
    have hh := hvalid 5168 (by decide)
    have hr := hvalid 2264 (by decide)
    have h := run_call26Template_word s (UInt256.ofNat 2227) f.frame rho
      hstack hrun hactive hh hr rfl rfl rfl
    exact h


def call28Block : CoreBlock 2264 2303 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := (call28Template ++ fullTemplate)
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 7 15 (call28Frame memory f.frame).message1 f.k (PairedLaneWordRound.wordStep 1 11 6 (call28Frame memory f.frame).message0 f.k f.lane)}
  run := by
    intro s f rho hstack hrun hactive hvalid
    have hh := hvalid 5168 (by decide)
    have hr := hvalid 2303 (by decide)
    have h := run_call28Template_word s (UInt256.ofNat 2264) f.frame rho
      hstack hrun hactive hh hr rfl rfl rfl
    exact h


theorem return30Template_pc : pcAfter (UInt256.ofNat 2303) return30Template = UInt256.ofNat 2304 := rfl

def return30Block : CoreBlock 2303 2304 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := return30Template
  eval := fun _memory f => f
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_return30Template s (UInt256.ofNat 2303) f.frame rho hstack hrun
    rw [return30Template_pc] at h
    exact h


theorem inline30Template_pc : pcAfter (UInt256.ofNat 2304) inline30Template = UInt256.ofNat 2353 := rfl

def inline30Block : CoreBlock 2304 2353 [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline30Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 13 13 (inline30Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline30Template_word s (UInt256.ofNat 2304) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline30Template_pc] at h
    exact h


theorem inline31Template_pc : pcAfter (UInt256.ofNat 2353) inline31Template = UInt256.ofNat 2414 := rfl

def inline31Block : CoreBlock 2353 2414 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline31Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 1 12 11 (inline31Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline31Template_word s (UInt256.ofNat 2353) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline31Template_pc] at h
    exact h


theorem group32Template_pc : pcAfter (UInt256.ofNat 2414) group32Template = UInt256.ofNat 2437 := rfl

def group32Block : CoreBlock 2414 2437 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.k, .a, .b, .c, .upper, .e, .factor, .pair, .d, .lower] where
  code := group32Template
  eval := fun _memory f => {f with k := UInt256.ofNat 624783161132376868856603395408315258898134723489}
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_group32Template s (UInt256.ofNat 2414) f.frame rho hstack hrun
    rw [group32Template_pc] at h
    exact h


theorem inline32Template_pc : pcAfter (UInt256.ofNat 2437) inline32Template = UInt256.ofNat 2487 := rfl

def inline32Block : CoreBlock 2437 2487 [.k, .a, .b, .c, .upper, .e, .factor, .pair, .d, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline32Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 11 9 (inline32Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline32Template_word s (UInt256.ofNat 2437) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline32Template_pc] at h
    exact h


theorem inline33Template_pc : pcAfter (UInt256.ofNat 2487) inline33Template = UInt256.ofNat 2537 := rfl

def inline33Block : CoreBlock 2487 2537 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline33Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 13 7 (inline33Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline33Template_word s (UInt256.ofNat 2487) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline33Template_pc] at h
    exact h


theorem inline34Template_pc : pcAfter (UInt256.ofNat 2537) inline34Template = UInt256.ofNat 2586 := rfl

def inline34Block : CoreBlock 2537 2586 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline34Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 6 15 (inline34Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline34Template_word s (UInt256.ofNat 2537) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline34Template_pc] at h
    exact h


theorem inline35Template_pc : pcAfter (UInt256.ofNat 2586) inline35Template = UInt256.ofNat 2636 := rfl

def inline35Block : CoreBlock 2586 2636 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline35Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 7 11 (inline35Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline35Template_word s (UInt256.ofNat 2586) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline35Template_pc] at h
    exact h


theorem inline36Template_pc : pcAfter (UInt256.ofNat 2636) inline36Template = UInt256.ofNat 2686 := rfl

def inline36Block : CoreBlock 2636 2686 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline36Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 14 8 (inline36Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline36Template_word s (UInt256.ofNat 2636) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline36Template_pc] at h
    exact h


theorem inline37Template_pc : pcAfter (UInt256.ofNat 2686) inline37Template = UInt256.ofNat 2736 := rfl

def inline37Block : CoreBlock 2686 2736 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline37Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 9 6 (inline37Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline37Template_word s (UInt256.ofNat 2686) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline37Template_pc] at h
    exact h


theorem inline38Template_pc : pcAfter (UInt256.ofNat 2736) inline38Template = UInt256.ofNat 2786 := rfl

def inline38Block : CoreBlock 2736 2786 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline38Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 13 6 (inline38Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline38Template_word s (UInt256.ofNat 2736) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline38Template_pc] at h
    exact h


theorem inline39Template_pc : pcAfter (UInt256.ofNat 2786) inline39Template = UInt256.ofNat 2835 := rfl

def inline39Block : CoreBlock 2786 2835 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline39Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 15 14 (inline39Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline39Template_word s (UInt256.ofNat 2786) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline39Template_pc] at h
    exact h


theorem inline40Template_pc : pcAfter (UInt256.ofNat 2835) inline40Template = UInt256.ofNat 2885 := rfl

def inline40Block : CoreBlock 2835 2885 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline40Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 14 12 (inline40Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline40Template_word s (UInt256.ofNat 2835) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline40Template_pc] at h
    exact h


theorem inline41Template_pc : pcAfter (UInt256.ofNat 2885) inline41Template = UInt256.ofNat 2935 := rfl

def inline41Block : CoreBlock 2885 2935 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline41Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 8 13 (inline41Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline41Template_word s (UInt256.ofNat 2885) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline41Template_pc] at h
    exact h


theorem inline42Template_pc : pcAfter (UInt256.ofNat 2935) inline42Template = UInt256.ofNat 2984 := rfl

def inline42Block : CoreBlock 2935 2984 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline42Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 13 5 (inline42Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline42Template_word s (UInt256.ofNat 2935) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline42Template_pc] at h
    exact h


theorem inline43Template_pc : pcAfter (UInt256.ofNat 2984) inline43Template = UInt256.ofNat 3034 := rfl

def inline43Block : CoreBlock 2984 3034 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline43Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 6 14 (inline43Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline43Template_word s (UInt256.ofNat 2984) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline43Template_pc] at h
    exact h


theorem inline44Template_pc : pcAfter (UInt256.ofNat 3034) inline44Template = UInt256.ofNat 3084 := rfl

def inline44Block : CoreBlock 3034 3084 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline44Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 5 13 (inline44Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline44Template_word s (UInt256.ofNat 3034) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline44Template_pc] at h
    exact h


theorem inline45Template_pc : pcAfter (UInt256.ofNat 3084) inline45Template = UInt256.ofNat 3133 := rfl

def inline45Block : CoreBlock 3084 3133 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline45Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 12 13 (inline45Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline45Template_word s (UInt256.ofNat 3084) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline45Template_pc] at h
    exact h


theorem inline46Template_pc : pcAfter (UInt256.ofNat 3133) inline46Template = UInt256.ofNat 3173 := rfl

def inline46Block : CoreBlock 3133 3173 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline46Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 7 7 (inline46Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline46Template_word s (UInt256.ofNat 3133) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline46Template_pc] at h
    exact h


theorem inline47Template_pc : pcAfter (UInt256.ofNat 3173) inline47Template = UInt256.ofNat 3213 := rfl

def inline47Block : CoreBlock 3173 3213 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline47Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 2 5 5 (inline47Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline47Template_word s (UInt256.ofNat 3173) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline47Template_pc] at h
    exact h


theorem group48Template_pc : pcAfter (UInt256.ofNat 3213) group48Template = UInt256.ofNat 3236 := rfl

def group48Block : CoreBlock 3213 3236 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.k, .d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := group48Template
  eval := fun _memory f => {f with k := UInt256.ofNat 698938013802679700166637234969497128417458109660}
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_group48Template s (UInt256.ofNat 3213) f.frame rho hstack hrun
    rw [group48Template_pc] at h
    exact h


theorem inline48Template_pc : pcAfter (UInt256.ofNat 3236) inline48Template = UInt256.ofNat 3296 := rfl

def inline48Block : CoreBlock 3236 3296 [.k, .d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline48Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 11 15 (inline48Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline48Template_word s (UInt256.ofNat 3236) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline48Template_pc] at h
    exact h


theorem inline49Template_pc : pcAfter (UInt256.ofNat 3296) inline49Template = UInt256.ofNat 3357 := rfl

def inline49Block : CoreBlock 3296 3357 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline49Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 12 5 (inline49Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline49Template_word s (UInt256.ofNat 3296) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline49Template_pc] at h
    exact h


theorem inline50Template_pc : pcAfter (UInt256.ofNat 3357) inline50Template = UInt256.ofNat 3418 := rfl

def inline50Block : CoreBlock 3357 3418 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline50Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 8 (inline50Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline50Template_word s (UInt256.ofNat 3357) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline50Template_pc] at h
    exact h


theorem inline51Template_pc : pcAfter (UInt256.ofNat 3418) inline51Template = UInt256.ofNat 3478 := rfl

def inline51Block : CoreBlock 3418 3478 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline51Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 15 11 (inline51Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline51Template_word s (UInt256.ofNat 3418) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline51Template_pc] at h
    exact h


theorem inline52Template_pc : pcAfter (UInt256.ofNat 3478) inline52Template = UInt256.ofNat 3528 := rfl

def inline52Block : CoreBlock 3478 3528 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline52Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 14 (inline52Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline52Template_word s (UInt256.ofNat 3478) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline52Template_pc] at h
    exact h


theorem inline53Template_pc : pcAfter (UInt256.ofNat 3528) inline53Template = UInt256.ofNat 3589 := rfl

def inline53Block : CoreBlock 3528 3589 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline53Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 15 14 (inline53Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline53Template_word s (UInt256.ofNat 3528) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline53Template_pc] at h
    exact h


theorem inline54Template_pc : pcAfter (UInt256.ofNat 3589) inline54Template = UInt256.ofNat 3650 := rfl

def inline54Block : CoreBlock 3589 3650 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline54Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 9 6 (inline54Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline54Template_word s (UInt256.ofNat 3589) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline54Template_pc] at h
    exact h


theorem inline55Template_pc : pcAfter (UInt256.ofNat 3650) inline55Template = UInt256.ofNat 3710 := rfl

def inline55Block : CoreBlock 3650 3710 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline55Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 8 14 (inline55Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline55Template_word s (UInt256.ofNat 3650) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline55Template_pc] at h
    exact h


theorem inline56Template_pc : pcAfter (UInt256.ofNat 3710) inline56Template = UInt256.ofNat 3771 := rfl

def inline56Block : CoreBlock 3710 3771 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline56Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 9 6 (inline56Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline56Template_word s (UInt256.ofNat 3710) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline56Template_pc] at h
    exact h


theorem inline57Template_pc : pcAfter (UInt256.ofNat 3771) inline57Template = UInt256.ofNat 3832 := rfl

def inline57Block : CoreBlock 3771 3832 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline57Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 14 9 (inline57Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline57Template_word s (UInt256.ofNat 3771) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline57Template_pc] at h
    exact h


theorem inline58Template_pc : pcAfter (UInt256.ofNat 3832) inline58Template = UInt256.ofNat 3893 := rfl

def inline58Block : CoreBlock 3832 3893 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline58Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 5 12 (inline58Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline58Template_word s (UInt256.ofNat 3832) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline58Template_pc] at h
    exact h


theorem inline59Template_pc : pcAfter (UInt256.ofNat 3893) inline59Template = UInt256.ofNat 3954 := rfl

def inline59Block : CoreBlock 3893 3954 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline59Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 6 9 (inline59Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline59Template_word s (UInt256.ofNat 3893) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline59Template_pc] at h
    exact h


theorem inline60Template_pc : pcAfter (UInt256.ofNat 3954) inline60Template = UInt256.ofNat 4015 := rfl

def inline60Block : CoreBlock 3954 4015 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline60Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 8 12 (inline60Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline60Template_word s (UInt256.ofNat 3954) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline60Template_pc] at h
    exact h


theorem inline61Template_pc : pcAfter (UInt256.ofNat 4015) inline61Template = UInt256.ofNat 4076 := rfl

def inline61Block : CoreBlock 4015 4076 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline61Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 6 5 (inline61Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline61Template_word s (UInt256.ofNat 4015) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline61Template_pc] at h
    exact h


theorem inline62Template_pc : pcAfter (UInt256.ofNat 4076) inline62Template = UInt256.ofNat 4137 := rfl

def inline62Block : CoreBlock 4076 4137 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] where
  code := inline62Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 5 15 (inline62Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline62Template_word s (UInt256.ofNat 4076) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline62Template_pc] at h
    exact h


theorem inline63Template_pc : pcAfter (UInt256.ofNat 4137) inline63Template = UInt256.ofNat 4198 := rfl

def inline63Block : CoreBlock 4137 4198 [.d, .e, .c, .b, .upper, .a, .factor, .pair, .k, .lower] [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] where
  code := inline63Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 3 12 8 (inline63Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline63Template_word s (UInt256.ofNat 4137) f.frame rho
      hstack hrun hactive rfl rfl rfl
    rw [inline63Template_pc] at h
    exact h


theorem group64Template_pc : pcAfter (UInt256.ofNat 4198) group64Template = UInt256.ofNat 4205 := rfl

def group64Block : CoreBlock 4198 4205 [.d, .a, .b, .c, .upper, .e, .factor, .pair, .k, .lower] [.k, .a, .b, .c, .upper, .e, .factor, .pair, .d, .lower] where
  code := group64Template
  eval := fun _memory f => {f with k := UInt256.ofNat 2840853838}
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_group64Template s (UInt256.ofNat 4198) f.frame rho hstack hrun
    rw [group64Template_pc] at h
    exact h


theorem inline64Template_pc : pcAfter (UInt256.ofNat 4205) inline64Template = UInt256.ofNat 4260 := rfl

def inline64Block : CoreBlock 4205 4260 [.k, .a, .b, .c, .upper, .e, .factor, .pair, .d, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline64Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 9 8 (inline64Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline64Template_word s (UInt256.ofNat 4205) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline64Template_pc] at h
    exact h


theorem inline65Template_pc : pcAfter (UInt256.ofNat 4260) inline65Template = UInt256.ofNat 4314 := rfl

def inline65Block : CoreBlock 4260 4314 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline65Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 15 5 (inline65Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline65Template_word s (UInt256.ofNat 4260) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline65Template_pc] at h
    exact h


theorem inline66Template_pc : pcAfter (UInt256.ofNat 4314) inline66Template = UInt256.ofNat 4369 := rfl

def inline66Block : CoreBlock 4314 4369 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline66Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 12 (inline66Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline66Template_word s (UInt256.ofNat 4314) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline66Template_pc] at h
    exact h


theorem inline67Template_pc : pcAfter (UInt256.ofNat 4369) inline67Template = UInt256.ofNat 4424 := rfl

def inline67Block : CoreBlock 4369 4424 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline67Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 11 9 (inline67Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline67Template_word s (UInt256.ofNat 4369) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline67Template_pc] at h
    exact h


theorem inline68Template_pc : pcAfter (UInt256.ofNat 4424) inline68Template = UInt256.ofNat 4478 := rfl

def inline68Block : CoreBlock 4424 4478 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline68Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 6 12 (inline68Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline68Template_word s (UInt256.ofNat 4424) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline68Template_pc] at h
    exact h


theorem inline69Template_pc : pcAfter (UInt256.ofNat 4478) inline69Template = UInt256.ofNat 4533 := rfl

def inline69Block : CoreBlock 4478 4533 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline69Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 8 5 (inline69Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline69Template_word s (UInt256.ofNat 4478) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline69Template_pc] at h
    exact h


theorem inline70Template_pc : pcAfter (UInt256.ofNat 4533) inline70Template = UInt256.ofNat 4588 := rfl

def inline70Block : CoreBlock 4533 4588 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline70Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 13 14 (inline70Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline70Template_word s (UInt256.ofNat 4533) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline70Template_pc] at h
    exact h


theorem inline71Template_pc : pcAfter (UInt256.ofNat 4588) inline71Template = UInt256.ofNat 4643 := rfl

def inline71Block : CoreBlock 4588 4643 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline71Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 12 6 (inline71Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline71Template_word s (UInt256.ofNat 4588) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline71Template_pc] at h
    exact h


theorem inline72Template_pc : pcAfter (UInt256.ofNat 4643) inline72Template = UInt256.ofNat 4698 := rfl

def inline72Block : CoreBlock 4643 4698 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline72Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 8 (inline72Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline72Template_word s (UInt256.ofNat 4643) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline72Template_pc] at h
    exact h


theorem inline73Template_pc : pcAfter (UInt256.ofNat 4698) inline73Template = UInt256.ofNat 4752 := rfl

def inline73Block : CoreBlock 4698 4752 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline73Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 12 13 (inline73Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline73Template_word s (UInt256.ofNat 4698) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline73Template_pc] at h
    exact h


theorem inline74Template_pc : pcAfter (UInt256.ofNat 4752) inline74Template = UInt256.ofNat 4807 := rfl

def inline74Block : CoreBlock 4752 4807 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline74Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 13 6 (inline74Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline74Template_word s (UInt256.ofNat 4752) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline74Template_pc] at h
    exact h


theorem inline75Template_pc : pcAfter (UInt256.ofNat 4807) inline75Template = UInt256.ofNat 4862 := rfl

def inline75Block : CoreBlock 4807 4862 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline75Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 14 5 (inline75Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline75Template_word s (UInt256.ofNat 4807) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline75Template_pc] at h
    exact h


theorem inline76Template_pc : pcAfter (UInt256.ofNat 4862) inline76Template = UInt256.ofNat 4916 := rfl

def inline76Block : CoreBlock 4862 4916 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline76Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 11 15 (inline76Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline76Template_word s (UInt256.ofNat 4862) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline76Template_pc] at h
    exact h


theorem inline77Template_pc : pcAfter (UInt256.ofNat 4916) inline77Template = UInt256.ofNat 4971 := rfl

def inline77Block : CoreBlock 4916 4971 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline77Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 8 13 (inline77Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline77Template_word s (UInt256.ofNat 4916) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline77Template_pc] at h
    exact h


theorem inline78Template_pc : pcAfter (UInt256.ofNat 4971) inline78Template = UInt256.ofNat 5026 := rfl

def inline78Block : CoreBlock 4971 5026 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] where
  code := inline78Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 5 11 (inline78Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline78Template_word s (UInt256.ofNat 4971) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline78Template_pc] at h
    exact h


theorem inline79Template_pc : pcAfter (UInt256.ofNat 5026) inline79Template = UInt256.ofNat 5081 := rfl

def inline79Block : CoreBlock 5026 5081 [.d, .k, .c, .b, .upper, .a, .factor, .pair, .e, .lower] [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := inline79Template
  eval := fun memory f => {f with lane := PairedLaneWordRound.wordStep 4 6 11 (inline79Frame memory f.frame).message0 f.k f.lane}
  run := by
    intro s f rho hstack hrun hactive _hvalid
    have h := run_inline79Template_word s (UInt256.ofNat 5026) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline79Template_pc] at h
    exact h


theorem coreExitTemplate_pc : pcAfter (UInt256.ofNat 5081) coreExitTemplate = UInt256.ofNat 5083 := rfl

def coreExitBlock : CoreBlock 5081 5083 [.d, .k, .b, .c, .upper, .e, .factor, .pair, .a, .lower] [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] where
  code := coreExitTemplate
  eval := fun _memory f => f
  run := by
    intro s f rho hstack hrun _hactive _hvalid
    have h := run_coreExitTemplate s (UInt256.ofNat 5081) f.frame rho hstack hrun
    rw [coreExitTemplate_pc] at h
    exact h


def wholeCoreChain : CoreChain 960 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] 5083 [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] :=
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
  .cons call16Block (
  .cons return18Block (
  .cons inline18Block (
  .cons inline19Block (
  .cons call20Block (
  .cons call22Block (
  .cons return24Block (
  .cons inline24Block (
  .cons inline25Block (
  .cons call26Block (
  .cons call28Block (
  .cons return30Block (
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
  .cons coreExitBlock (.nil 5083 [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem run_wholeCoreChain (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho} =
      some {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (wholeCoreChain.eval s.memory f) rho} :=
  wholeCoreChain.run s f rho hstack hrun hactive hvalid

def pairedWordFold (group leftRotation rightRotation : Nat → Nat)
    (message constant : Nat → UInt256) :
    Nat → PairedLaneWordRound.WordLane → PairedLaneWordRound.WordLane
  | 0, q => q
  | i + 1, q => PairedLaneWordRound.wordStep (group i) (leftRotation i) (rightRotation i)
      (message i) (constant i) (pairedWordFold group leftRotation rightRotation message constant i q)

def scalarLeftFold (group rotation : Nat → Nat) (message constant : Nat → UInt32) :
    Nat → PairedLaneCryptoBridge.CryptoLane → PairedLaneCryptoBridge.CryptoLane
  | 0, q => q
  | i + 1, q => PairedLaneCryptoBridge.cryptoStep (group i) (rotation i)
      (message i) (constant i) (scalarLeftFold group rotation message constant i q)

def scalarRightFold (group rotation : Nat → Nat) (message constant : Nat → UInt32) :
    Nat → PairedLaneCryptoBridge.CryptoLane → PairedLaneCryptoBridge.CryptoLane
  | 0, q => q
  | i + 1, q => PairedLaneCryptoBridge.cryptoStep (4 - group i) (rotation i)
      (message i) (constant i) (scalarRightFold group rotation message constant i q)

/-- Arbitrary scalar schedules and initial registers; no vector-specific premise. -/
theorem pairedWordFold_crypto
    (group leftRotation rightRotation : Nat → Nat)
    (leftMessage rightMessage leftConstant rightConstant : Nat → UInt32)
    (count : Nat) (left right : PairedLaneCryptoBridge.CryptoLane)
    (hrotation : ∀ i < count,
      0 < leftRotation i ∧ leftRotation i < 32 ∧
      0 < rightRotation i ∧ rightRotation i < 32) :
    pairedWordFold group leftRotation rightRotation
      (fun i => packed32 (leftMessage i) (rightMessage i))
      (fun i => packed32 (leftConstant i) (rightConstant i))
      count (PairedLaneWordRound.packCrypto left right) =
    PairedLaneWordRound.packCrypto
      (scalarLeftFold group leftRotation leftMessage leftConstant count left)
      (scalarRightFold group rightRotation rightMessage rightConstant count right) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hi := ih (fun j hj => hrotation j (by omega))
    rw [pairedWordFold, hi]
    rcases hrotation i (by omega) with ⟨hl0, hl, hr0, hr⟩
    exact PairedLaneWordRound.wordStep_of_crypto
      (group i) (leftRotation i) (rightRotation i) hl0 hl hr0 hr
      (leftMessage i) (rightMessage i) (leftConstant i) (rightConstant i)
      (scalarLeftFold group leftRotation leftMessage leftConstant i left)
      (scalarRightFold group rightRotation rightMessage rightConstant i right)



/-- Packed round constant for each fixed RIPEMD-160 group. -/
def algorithmKey (j : Nat) : UInt256 :=
  match j with
  | 0 => UInt256.ofNat 460344169260758029377710773882198039553172832256
  | 1 => UInt256.ofNat 526962527014005041256681316140890030896371104153
  | 2 => UInt256.ofNat 624783161132376868856603395408315258898134723489
  | 3 => UInt256.ofNat 698938013802679700166637234969497128417458109660
  | 4 => UInt256.ofNat 2840853838
  | _ => 0

def algorithmMessage (memory : ByteArray) (i : Nat) : UInt256 :=
  UInt256.lor
    (MachineState.readWord memory (208 + 32 * Crypto.Ripemd160.rP[i]!))
    (MachineState.readWord memory (192 + 32 * Crypto.Ripemd160.r[i]!))

def algorithmFold (memory : ByteArray) (start count : Nat)
    (q : PairedLaneWordRound.WordLane) : PairedLaneWordRound.WordLane :=
  pairedWordFold
    (fun i => (start + i) / 16)
    (fun i => Crypto.Ripemd160.s[start + i]!)
    (fun i => Crypto.Ripemd160.sP[start + i]!)
    (fun i => algorithmMessage memory (start + i))
    (fun i => algorithmKey ((start + i) / 16)) count q


def algorithmStep (memory : ByteArray) (i : Nat)
    (q : PairedLaneWordRound.WordLane) : PairedLaneWordRound.WordLane :=
  PairedLaneWordRound.wordStep (i / 16) (Crypto.Ripemd160.s[i]!)
    (Crypto.Ripemd160.sP[i]!) (algorithmMessage memory i) (algorithmKey (i / 16)) q


theorem pairedWordFold_add
    (group leftRotation rightRotation : Nat → Nat)
    (message constant : Nat → UInt256) (a b : Nat)
    (q : PairedLaneWordRound.WordLane) :
    pairedWordFold group leftRotation rightRotation message constant (a + b) q =
      pairedWordFold
        (fun i => group (a + i)) (fun i => leftRotation (a + i))
        (fun i => rightRotation (a + i)) (fun i => message (a + i))
        (fun i => constant (a + i)) b
        (pairedWordFold group leftRotation rightRotation message constant a q) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    exact congrArg
      (PairedLaneWordRound.wordStep (group (a + b)) (leftRotation (a + b))
        (rightRotation (a + b)) (message (a + b)) (constant (a + b))) ih


theorem group0Block_eval (memory : ByteArray) (f : CoreFrame) :
    group0Block.eval memory f = ⟨f.lane, algorithmKey 0⟩ := rfl

theorem inline0Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline0Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 0 q, algorithmKey 0⟩ := rfl

theorem inline1Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline1Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 1 q, algorithmKey 0⟩ := rfl

theorem inline2Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline2Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 2 q, algorithmKey 0⟩ := rfl

theorem inline3Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline3Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 3 q, algorithmKey 0⟩ := rfl

theorem inline4Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline4Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 4 q, algorithmKey 0⟩ := rfl

theorem inline5Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline5Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 5 q, algorithmKey 0⟩ := rfl

theorem inline6Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline6Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 6 q, algorithmKey 0⟩ := rfl

theorem inline7Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline7Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 7 q, algorithmKey 0⟩ := rfl

theorem inline8Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline8Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 8 q, algorithmKey 0⟩ := rfl

theorem inline9Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline9Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 9 q, algorithmKey 0⟩ := rfl

theorem inline10Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline10Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 10 q, algorithmKey 0⟩ := rfl

theorem inline11Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline11Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 11 q, algorithmKey 0⟩ := rfl

theorem inline12Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline12Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 12 q, algorithmKey 0⟩ := rfl

theorem inline13Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline13Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 13 q, algorithmKey 0⟩ := rfl

theorem inline14Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline14Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 14 q, algorithmKey 0⟩ := rfl

theorem inline15Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline15Block.eval memory ⟨q, algorithmKey 0⟩ =
      ⟨algorithmStep memory 15 q, algorithmKey 0⟩ := rfl

theorem group16Block_eval (memory : ByteArray) (f : CoreFrame) :
    group16Block.eval memory f = ⟨f.lane, algorithmKey 1⟩ := rfl

theorem call16Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    call16Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 17 (algorithmStep memory 16 q), algorithmKey 1⟩ := rfl

theorem return18Block_eval (memory : ByteArray) (f : CoreFrame) :
    return18Block.eval memory f = f := rfl

theorem inline18Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline18Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 18 q, algorithmKey 1⟩ := rfl

theorem inline19Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline19Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 19 q, algorithmKey 1⟩ := rfl

theorem call20Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    call20Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 21 (algorithmStep memory 20 q), algorithmKey 1⟩ := rfl

theorem call22Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    call22Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 23 (algorithmStep memory 22 q), algorithmKey 1⟩ := rfl

theorem return24Block_eval (memory : ByteArray) (f : CoreFrame) :
    return24Block.eval memory f = f := rfl

theorem inline24Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline24Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 24 q, algorithmKey 1⟩ := rfl

theorem inline25Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline25Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 25 q, algorithmKey 1⟩ := rfl

theorem call26Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    call26Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 27 (algorithmStep memory 26 q), algorithmKey 1⟩ := rfl

theorem call28Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    call28Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 29 (algorithmStep memory 28 q), algorithmKey 1⟩ := rfl

theorem return30Block_eval (memory : ByteArray) (f : CoreFrame) :
    return30Block.eval memory f = f := rfl

theorem inline30Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline30Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 30 q, algorithmKey 1⟩ := rfl

theorem inline31Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline31Block.eval memory ⟨q, algorithmKey 1⟩ =
      ⟨algorithmStep memory 31 q, algorithmKey 1⟩ := rfl

theorem group32Block_eval (memory : ByteArray) (f : CoreFrame) :
    group32Block.eval memory f = ⟨f.lane, algorithmKey 2⟩ := rfl

theorem inline32Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline32Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 32 q, algorithmKey 2⟩ := rfl

theorem inline33Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline33Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 33 q, algorithmKey 2⟩ := rfl

theorem inline34Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline34Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 34 q, algorithmKey 2⟩ := rfl

theorem inline35Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline35Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 35 q, algorithmKey 2⟩ := rfl

theorem inline36Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline36Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 36 q, algorithmKey 2⟩ := rfl

theorem inline37Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline37Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 37 q, algorithmKey 2⟩ := rfl

theorem inline38Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline38Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 38 q, algorithmKey 2⟩ := rfl

theorem inline39Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline39Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 39 q, algorithmKey 2⟩ := rfl

theorem inline40Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline40Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 40 q, algorithmKey 2⟩ := rfl

theorem inline41Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline41Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 41 q, algorithmKey 2⟩ := rfl

theorem inline42Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline42Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 42 q, algorithmKey 2⟩ := rfl

theorem inline43Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline43Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 43 q, algorithmKey 2⟩ := rfl

theorem inline44Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline44Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 44 q, algorithmKey 2⟩ := rfl

theorem inline45Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline45Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 45 q, algorithmKey 2⟩ := rfl

theorem inline46Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline46Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 46 q, algorithmKey 2⟩ := rfl

theorem inline47Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline47Block.eval memory ⟨q, algorithmKey 2⟩ =
      ⟨algorithmStep memory 47 q, algorithmKey 2⟩ := rfl

theorem group48Block_eval (memory : ByteArray) (f : CoreFrame) :
    group48Block.eval memory f = ⟨f.lane, algorithmKey 3⟩ := rfl

theorem inline48Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline48Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 48 q, algorithmKey 3⟩ := rfl

theorem inline49Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline49Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 49 q, algorithmKey 3⟩ := rfl

theorem inline50Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline50Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 50 q, algorithmKey 3⟩ := rfl

theorem inline51Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline51Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 51 q, algorithmKey 3⟩ := rfl

theorem inline52Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline52Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 52 q, algorithmKey 3⟩ := rfl

theorem inline53Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline53Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 53 q, algorithmKey 3⟩ := rfl

theorem inline54Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline54Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 54 q, algorithmKey 3⟩ := rfl

theorem inline55Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline55Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 55 q, algorithmKey 3⟩ := rfl

theorem inline56Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline56Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 56 q, algorithmKey 3⟩ := rfl

theorem inline57Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline57Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 57 q, algorithmKey 3⟩ := rfl

theorem inline58Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline58Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 58 q, algorithmKey 3⟩ := rfl

theorem inline59Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline59Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 59 q, algorithmKey 3⟩ := rfl

theorem inline60Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline60Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 60 q, algorithmKey 3⟩ := rfl

theorem inline61Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline61Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 61 q, algorithmKey 3⟩ := rfl

theorem inline62Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline62Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 62 q, algorithmKey 3⟩ := rfl

theorem inline63Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline63Block.eval memory ⟨q, algorithmKey 3⟩ =
      ⟨algorithmStep memory 63 q, algorithmKey 3⟩ := rfl

theorem group64Block_eval (memory : ByteArray) (f : CoreFrame) :
    group64Block.eval memory f = ⟨f.lane, algorithmKey 4⟩ := rfl

theorem inline64Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline64Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 64 q, algorithmKey 4⟩ := rfl

theorem inline65Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline65Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 65 q, algorithmKey 4⟩ := rfl

theorem inline66Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline66Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 66 q, algorithmKey 4⟩ := rfl

theorem inline67Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline67Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 67 q, algorithmKey 4⟩ := rfl

theorem inline68Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline68Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 68 q, algorithmKey 4⟩ := rfl

theorem inline69Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline69Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 69 q, algorithmKey 4⟩ := rfl

theorem inline70Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline70Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 70 q, algorithmKey 4⟩ := rfl

theorem inline71Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline71Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 71 q, algorithmKey 4⟩ := rfl

theorem inline72Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline72Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 72 q, algorithmKey 4⟩ := rfl

theorem inline73Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline73Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 73 q, algorithmKey 4⟩ := rfl

theorem inline74Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline74Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 74 q, algorithmKey 4⟩ := rfl

theorem inline75Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline75Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 75 q, algorithmKey 4⟩ := rfl

theorem inline76Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline76Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 76 q, algorithmKey 4⟩ := rfl

theorem inline77Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline77Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 77 q, algorithmKey 4⟩ := rfl

theorem inline78Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline78Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 78 q, algorithmKey 4⟩ := rfl

theorem inline79Block_eval (memory : ByteArray) (q : PairedLaneWordRound.WordLane) :
    inline79Block.eval memory ⟨q, algorithmKey 4⟩ =
      ⟨algorithmStep memory 79 q, algorithmKey 4⟩ := rfl

theorem coreExitBlock_eval (memory : ByteArray) (f : CoreFrame) :
    coreExitBlock.eval memory f = f := rfl

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


theorem algorithmFold_succ (memory : ByteArray) (start count : Nat)
    (q : PairedLaneWordRound.WordLane) :
    algorithmFold memory start (count + 1) q =
      algorithmStep memory (start + count) (algorithmFold memory start count q) := rfl



theorem wholeCoreChain_eval (memory : ByteArray) (f : CoreFrame) :
    wholeCoreChain.eval memory f =
      ⟨algorithmFold memory 0 80 f.lane, algorithmKey 4⟩ := by
  let f0 : CoreFrame := f
  let f1 : CoreFrame := ⟨algorithmFold memory 0 0 f.lane, algorithmKey 0⟩
  let f2 : CoreFrame := ⟨algorithmFold memory 0 1 f.lane, algorithmKey 0⟩
  let f3 : CoreFrame := ⟨algorithmFold memory 0 2 f.lane, algorithmKey 0⟩
  let f4 : CoreFrame := ⟨algorithmFold memory 0 3 f.lane, algorithmKey 0⟩
  let f5 : CoreFrame := ⟨algorithmFold memory 0 4 f.lane, algorithmKey 0⟩
  let f6 : CoreFrame := ⟨algorithmFold memory 0 5 f.lane, algorithmKey 0⟩
  let f7 : CoreFrame := ⟨algorithmFold memory 0 6 f.lane, algorithmKey 0⟩
  let f8 : CoreFrame := ⟨algorithmFold memory 0 7 f.lane, algorithmKey 0⟩
  let f9 : CoreFrame := ⟨algorithmFold memory 0 8 f.lane, algorithmKey 0⟩
  let f10 : CoreFrame := ⟨algorithmFold memory 0 9 f.lane, algorithmKey 0⟩
  let f11 : CoreFrame := ⟨algorithmFold memory 0 10 f.lane, algorithmKey 0⟩
  let f12 : CoreFrame := ⟨algorithmFold memory 0 11 f.lane, algorithmKey 0⟩
  let f13 : CoreFrame := ⟨algorithmFold memory 0 12 f.lane, algorithmKey 0⟩
  let f14 : CoreFrame := ⟨algorithmFold memory 0 13 f.lane, algorithmKey 0⟩
  let f15 : CoreFrame := ⟨algorithmFold memory 0 14 f.lane, algorithmKey 0⟩
  let f16 : CoreFrame := ⟨algorithmFold memory 0 15 f.lane, algorithmKey 0⟩
  let f17 : CoreFrame := ⟨algorithmFold memory 0 16 f.lane, algorithmKey 0⟩
  let f18 : CoreFrame := ⟨algorithmFold memory 0 16 f.lane, algorithmKey 1⟩
  let f19 : CoreFrame := ⟨algorithmFold memory 0 18 f.lane, algorithmKey 1⟩
  let f20 : CoreFrame := ⟨algorithmFold memory 0 18 f.lane, algorithmKey 1⟩
  let f21 : CoreFrame := ⟨algorithmFold memory 0 19 f.lane, algorithmKey 1⟩
  let f22 : CoreFrame := ⟨algorithmFold memory 0 20 f.lane, algorithmKey 1⟩
  let f23 : CoreFrame := ⟨algorithmFold memory 0 22 f.lane, algorithmKey 1⟩
  let f24 : CoreFrame := ⟨algorithmFold memory 0 24 f.lane, algorithmKey 1⟩
  let f25 : CoreFrame := ⟨algorithmFold memory 0 24 f.lane, algorithmKey 1⟩
  let f26 : CoreFrame := ⟨algorithmFold memory 0 25 f.lane, algorithmKey 1⟩
  let f27 : CoreFrame := ⟨algorithmFold memory 0 26 f.lane, algorithmKey 1⟩
  let f28 : CoreFrame := ⟨algorithmFold memory 0 28 f.lane, algorithmKey 1⟩
  let f29 : CoreFrame := ⟨algorithmFold memory 0 30 f.lane, algorithmKey 1⟩
  let f30 : CoreFrame := ⟨algorithmFold memory 0 30 f.lane, algorithmKey 1⟩
  let f31 : CoreFrame := ⟨algorithmFold memory 0 31 f.lane, algorithmKey 1⟩
  let f32 : CoreFrame := ⟨algorithmFold memory 0 32 f.lane, algorithmKey 1⟩
  let f33 : CoreFrame := ⟨algorithmFold memory 0 32 f.lane, algorithmKey 2⟩
  let f34 : CoreFrame := ⟨algorithmFold memory 0 33 f.lane, algorithmKey 2⟩
  let f35 : CoreFrame := ⟨algorithmFold memory 0 34 f.lane, algorithmKey 2⟩
  let f36 : CoreFrame := ⟨algorithmFold memory 0 35 f.lane, algorithmKey 2⟩
  let f37 : CoreFrame := ⟨algorithmFold memory 0 36 f.lane, algorithmKey 2⟩
  let f38 : CoreFrame := ⟨algorithmFold memory 0 37 f.lane, algorithmKey 2⟩
  let f39 : CoreFrame := ⟨algorithmFold memory 0 38 f.lane, algorithmKey 2⟩
  let f40 : CoreFrame := ⟨algorithmFold memory 0 39 f.lane, algorithmKey 2⟩
  let f41 : CoreFrame := ⟨algorithmFold memory 0 40 f.lane, algorithmKey 2⟩
  let f42 : CoreFrame := ⟨algorithmFold memory 0 41 f.lane, algorithmKey 2⟩
  let f43 : CoreFrame := ⟨algorithmFold memory 0 42 f.lane, algorithmKey 2⟩
  let f44 : CoreFrame := ⟨algorithmFold memory 0 43 f.lane, algorithmKey 2⟩
  let f45 : CoreFrame := ⟨algorithmFold memory 0 44 f.lane, algorithmKey 2⟩
  let f46 : CoreFrame := ⟨algorithmFold memory 0 45 f.lane, algorithmKey 2⟩
  let f47 : CoreFrame := ⟨algorithmFold memory 0 46 f.lane, algorithmKey 2⟩
  let f48 : CoreFrame := ⟨algorithmFold memory 0 47 f.lane, algorithmKey 2⟩
  let f49 : CoreFrame := ⟨algorithmFold memory 0 48 f.lane, algorithmKey 2⟩
  let f50 : CoreFrame := ⟨algorithmFold memory 0 48 f.lane, algorithmKey 3⟩
  let f51 : CoreFrame := ⟨algorithmFold memory 0 49 f.lane, algorithmKey 3⟩
  let f52 : CoreFrame := ⟨algorithmFold memory 0 50 f.lane, algorithmKey 3⟩
  let f53 : CoreFrame := ⟨algorithmFold memory 0 51 f.lane, algorithmKey 3⟩
  let f54 : CoreFrame := ⟨algorithmFold memory 0 52 f.lane, algorithmKey 3⟩
  let f55 : CoreFrame := ⟨algorithmFold memory 0 53 f.lane, algorithmKey 3⟩
  let f56 : CoreFrame := ⟨algorithmFold memory 0 54 f.lane, algorithmKey 3⟩
  let f57 : CoreFrame := ⟨algorithmFold memory 0 55 f.lane, algorithmKey 3⟩
  let f58 : CoreFrame := ⟨algorithmFold memory 0 56 f.lane, algorithmKey 3⟩
  let f59 : CoreFrame := ⟨algorithmFold memory 0 57 f.lane, algorithmKey 3⟩
  let f60 : CoreFrame := ⟨algorithmFold memory 0 58 f.lane, algorithmKey 3⟩
  let f61 : CoreFrame := ⟨algorithmFold memory 0 59 f.lane, algorithmKey 3⟩
  let f62 : CoreFrame := ⟨algorithmFold memory 0 60 f.lane, algorithmKey 3⟩
  let f63 : CoreFrame := ⟨algorithmFold memory 0 61 f.lane, algorithmKey 3⟩
  let f64 : CoreFrame := ⟨algorithmFold memory 0 62 f.lane, algorithmKey 3⟩
  let f65 : CoreFrame := ⟨algorithmFold memory 0 63 f.lane, algorithmKey 3⟩
  let f66 : CoreFrame := ⟨algorithmFold memory 0 64 f.lane, algorithmKey 3⟩
  let f67 : CoreFrame := ⟨algorithmFold memory 0 64 f.lane, algorithmKey 4⟩
  let f68 : CoreFrame := ⟨algorithmFold memory 0 65 f.lane, algorithmKey 4⟩
  let f69 : CoreFrame := ⟨algorithmFold memory 0 66 f.lane, algorithmKey 4⟩
  let f70 : CoreFrame := ⟨algorithmFold memory 0 67 f.lane, algorithmKey 4⟩
  let f71 : CoreFrame := ⟨algorithmFold memory 0 68 f.lane, algorithmKey 4⟩
  let f72 : CoreFrame := ⟨algorithmFold memory 0 69 f.lane, algorithmKey 4⟩
  let f73 : CoreFrame := ⟨algorithmFold memory 0 70 f.lane, algorithmKey 4⟩
  let f74 : CoreFrame := ⟨algorithmFold memory 0 71 f.lane, algorithmKey 4⟩
  let f75 : CoreFrame := ⟨algorithmFold memory 0 72 f.lane, algorithmKey 4⟩
  let f76 : CoreFrame := ⟨algorithmFold memory 0 73 f.lane, algorithmKey 4⟩
  let f77 : CoreFrame := ⟨algorithmFold memory 0 74 f.lane, algorithmKey 4⟩
  let f78 : CoreFrame := ⟨algorithmFold memory 0 75 f.lane, algorithmKey 4⟩
  let f79 : CoreFrame := ⟨algorithmFold memory 0 76 f.lane, algorithmKey 4⟩
  let f80 : CoreFrame := ⟨algorithmFold memory 0 77 f.lane, algorithmKey 4⟩
  let f81 : CoreFrame := ⟨algorithmFold memory 0 78 f.lane, algorithmKey 4⟩
  let f82 : CoreFrame := ⟨algorithmFold memory 0 79 f.lane, algorithmKey 4⟩
  let f83 : CoreFrame := ⟨algorithmFold memory 0 80 f.lane, algorithmKey 4⟩
  let f84 : CoreFrame := ⟨algorithmFold memory 0 80 f.lane, algorithmKey 4⟩
  have h0 : group0Block.eval memory f0 = f1 := by
    exact group0Block_eval memory f0
  have h1 : inline0Block.eval memory f1 = f2 := by
    exact inline0Block_eval memory (algorithmFold memory 0 0 f.lane)
  have h2 : inline1Block.eval memory f2 = f3 := by
    exact inline1Block_eval memory (algorithmFold memory 0 1 f.lane)
  have h3 : inline2Block.eval memory f3 = f4 := by
    exact inline2Block_eval memory (algorithmFold memory 0 2 f.lane)
  have h4 : inline3Block.eval memory f4 = f5 := by
    exact inline3Block_eval memory (algorithmFold memory 0 3 f.lane)
  have h5 : inline4Block.eval memory f5 = f6 := by
    exact inline4Block_eval memory (algorithmFold memory 0 4 f.lane)
  have h6 : inline5Block.eval memory f6 = f7 := by
    exact inline5Block_eval memory (algorithmFold memory 0 5 f.lane)
  have h7 : inline6Block.eval memory f7 = f8 := by
    exact inline6Block_eval memory (algorithmFold memory 0 6 f.lane)
  have h8 : inline7Block.eval memory f8 = f9 := by
    exact inline7Block_eval memory (algorithmFold memory 0 7 f.lane)
  have h9 : inline8Block.eval memory f9 = f10 := by
    exact inline8Block_eval memory (algorithmFold memory 0 8 f.lane)
  have h10 : inline9Block.eval memory f10 = f11 := by
    exact inline9Block_eval memory (algorithmFold memory 0 9 f.lane)
  have h11 : inline10Block.eval memory f11 = f12 := by
    exact inline10Block_eval memory (algorithmFold memory 0 10 f.lane)
  have h12 : inline11Block.eval memory f12 = f13 := by
    exact inline11Block_eval memory (algorithmFold memory 0 11 f.lane)
  have h13 : inline12Block.eval memory f13 = f14 := by
    exact inline12Block_eval memory (algorithmFold memory 0 12 f.lane)
  have h14 : inline13Block.eval memory f14 = f15 := by
    exact inline13Block_eval memory (algorithmFold memory 0 13 f.lane)
  have h15 : inline14Block.eval memory f15 = f16 := by
    exact inline14Block_eval memory (algorithmFold memory 0 14 f.lane)
  have h16 : inline15Block.eval memory f16 = f17 := by
    exact inline15Block_eval memory (algorithmFold memory 0 15 f.lane)
  have h17 : group16Block.eval memory f17 = f18 := by
    exact group16Block_eval memory f17
  have h18 : call16Block.eval memory f18 = f19 := by
    exact call16Block_eval memory (algorithmFold memory 0 16 f.lane)
  have h19 : return18Block.eval memory f19 = f20 := by
    exact return18Block_eval memory f19
  have h20 : inline18Block.eval memory f20 = f21 := by
    exact inline18Block_eval memory (algorithmFold memory 0 18 f.lane)
  have h21 : inline19Block.eval memory f21 = f22 := by
    exact inline19Block_eval memory (algorithmFold memory 0 19 f.lane)
  have h22 : call20Block.eval memory f22 = f23 := by
    exact call20Block_eval memory (algorithmFold memory 0 20 f.lane)
  have h23 : call22Block.eval memory f23 = f24 := by
    exact call22Block_eval memory (algorithmFold memory 0 22 f.lane)
  have h24 : return24Block.eval memory f24 = f25 := by
    exact return24Block_eval memory f24
  have h25 : inline24Block.eval memory f25 = f26 := by
    exact inline24Block_eval memory (algorithmFold memory 0 24 f.lane)
  have h26 : inline25Block.eval memory f26 = f27 := by
    exact inline25Block_eval memory (algorithmFold memory 0 25 f.lane)
  have h27 : call26Block.eval memory f27 = f28 := by
    exact call26Block_eval memory (algorithmFold memory 0 26 f.lane)
  have h28 : call28Block.eval memory f28 = f29 := by
    exact call28Block_eval memory (algorithmFold memory 0 28 f.lane)
  have h29 : return30Block.eval memory f29 = f30 := by
    exact return30Block_eval memory f29
  have h30 : inline30Block.eval memory f30 = f31 := by
    exact inline30Block_eval memory (algorithmFold memory 0 30 f.lane)
  have h31 : inline31Block.eval memory f31 = f32 := by
    exact inline31Block_eval memory (algorithmFold memory 0 31 f.lane)
  have h32 : group32Block.eval memory f32 = f33 := by
    exact group32Block_eval memory f32
  have h33 : inline32Block.eval memory f33 = f34 := by
    exact inline32Block_eval memory (algorithmFold memory 0 32 f.lane)
  have h34 : inline33Block.eval memory f34 = f35 := by
    exact inline33Block_eval memory (algorithmFold memory 0 33 f.lane)
  have h35 : inline34Block.eval memory f35 = f36 := by
    exact inline34Block_eval memory (algorithmFold memory 0 34 f.lane)
  have h36 : inline35Block.eval memory f36 = f37 := by
    exact inline35Block_eval memory (algorithmFold memory 0 35 f.lane)
  have h37 : inline36Block.eval memory f37 = f38 := by
    exact inline36Block_eval memory (algorithmFold memory 0 36 f.lane)
  have h38 : inline37Block.eval memory f38 = f39 := by
    exact inline37Block_eval memory (algorithmFold memory 0 37 f.lane)
  have h39 : inline38Block.eval memory f39 = f40 := by
    exact inline38Block_eval memory (algorithmFold memory 0 38 f.lane)
  have h40 : inline39Block.eval memory f40 = f41 := by
    exact inline39Block_eval memory (algorithmFold memory 0 39 f.lane)
  have h41 : inline40Block.eval memory f41 = f42 := by
    exact inline40Block_eval memory (algorithmFold memory 0 40 f.lane)
  have h42 : inline41Block.eval memory f42 = f43 := by
    exact inline41Block_eval memory (algorithmFold memory 0 41 f.lane)
  have h43 : inline42Block.eval memory f43 = f44 := by
    exact inline42Block_eval memory (algorithmFold memory 0 42 f.lane)
  have h44 : inline43Block.eval memory f44 = f45 := by
    exact inline43Block_eval memory (algorithmFold memory 0 43 f.lane)
  have h45 : inline44Block.eval memory f45 = f46 := by
    exact inline44Block_eval memory (algorithmFold memory 0 44 f.lane)
  have h46 : inline45Block.eval memory f46 = f47 := by
    exact inline45Block_eval memory (algorithmFold memory 0 45 f.lane)
  have h47 : inline46Block.eval memory f47 = f48 := by
    exact inline46Block_eval memory (algorithmFold memory 0 46 f.lane)
  have h48 : inline47Block.eval memory f48 = f49 := by
    exact inline47Block_eval memory (algorithmFold memory 0 47 f.lane)
  have h49 : group48Block.eval memory f49 = f50 := by
    exact group48Block_eval memory f49
  have h50 : inline48Block.eval memory f50 = f51 := by
    exact inline48Block_eval memory (algorithmFold memory 0 48 f.lane)
  have h51 : inline49Block.eval memory f51 = f52 := by
    exact inline49Block_eval memory (algorithmFold memory 0 49 f.lane)
  have h52 : inline50Block.eval memory f52 = f53 := by
    exact inline50Block_eval memory (algorithmFold memory 0 50 f.lane)
  have h53 : inline51Block.eval memory f53 = f54 := by
    exact inline51Block_eval memory (algorithmFold memory 0 51 f.lane)
  have h54 : inline52Block.eval memory f54 = f55 := by
    exact inline52Block_eval memory (algorithmFold memory 0 52 f.lane)
  have h55 : inline53Block.eval memory f55 = f56 := by
    exact inline53Block_eval memory (algorithmFold memory 0 53 f.lane)
  have h56 : inline54Block.eval memory f56 = f57 := by
    exact inline54Block_eval memory (algorithmFold memory 0 54 f.lane)
  have h57 : inline55Block.eval memory f57 = f58 := by
    exact inline55Block_eval memory (algorithmFold memory 0 55 f.lane)
  have h58 : inline56Block.eval memory f58 = f59 := by
    exact inline56Block_eval memory (algorithmFold memory 0 56 f.lane)
  have h59 : inline57Block.eval memory f59 = f60 := by
    exact inline57Block_eval memory (algorithmFold memory 0 57 f.lane)
  have h60 : inline58Block.eval memory f60 = f61 := by
    exact inline58Block_eval memory (algorithmFold memory 0 58 f.lane)
  have h61 : inline59Block.eval memory f61 = f62 := by
    exact inline59Block_eval memory (algorithmFold memory 0 59 f.lane)
  have h62 : inline60Block.eval memory f62 = f63 := by
    exact inline60Block_eval memory (algorithmFold memory 0 60 f.lane)
  have h63 : inline61Block.eval memory f63 = f64 := by
    exact inline61Block_eval memory (algorithmFold memory 0 61 f.lane)
  have h64 : inline62Block.eval memory f64 = f65 := by
    exact inline62Block_eval memory (algorithmFold memory 0 62 f.lane)
  have h65 : inline63Block.eval memory f65 = f66 := by
    exact inline63Block_eval memory (algorithmFold memory 0 63 f.lane)
  have h66 : group64Block.eval memory f66 = f67 := by
    exact group64Block_eval memory f66
  have h67 : inline64Block.eval memory f67 = f68 := by
    exact inline64Block_eval memory (algorithmFold memory 0 64 f.lane)
  have h68 : inline65Block.eval memory f68 = f69 := by
    exact inline65Block_eval memory (algorithmFold memory 0 65 f.lane)
  have h69 : inline66Block.eval memory f69 = f70 := by
    exact inline66Block_eval memory (algorithmFold memory 0 66 f.lane)
  have h70 : inline67Block.eval memory f70 = f71 := by
    exact inline67Block_eval memory (algorithmFold memory 0 67 f.lane)
  have h71 : inline68Block.eval memory f71 = f72 := by
    exact inline68Block_eval memory (algorithmFold memory 0 68 f.lane)
  have h72 : inline69Block.eval memory f72 = f73 := by
    exact inline69Block_eval memory (algorithmFold memory 0 69 f.lane)
  have h73 : inline70Block.eval memory f73 = f74 := by
    exact inline70Block_eval memory (algorithmFold memory 0 70 f.lane)
  have h74 : inline71Block.eval memory f74 = f75 := by
    exact inline71Block_eval memory (algorithmFold memory 0 71 f.lane)
  have h75 : inline72Block.eval memory f75 = f76 := by
    exact inline72Block_eval memory (algorithmFold memory 0 72 f.lane)
  have h76 : inline73Block.eval memory f76 = f77 := by
    exact inline73Block_eval memory (algorithmFold memory 0 73 f.lane)
  have h77 : inline74Block.eval memory f77 = f78 := by
    exact inline74Block_eval memory (algorithmFold memory 0 74 f.lane)
  have h78 : inline75Block.eval memory f78 = f79 := by
    exact inline75Block_eval memory (algorithmFold memory 0 75 f.lane)
  have h79 : inline76Block.eval memory f79 = f80 := by
    exact inline76Block_eval memory (algorithmFold memory 0 76 f.lane)
  have h80 : inline77Block.eval memory f80 = f81 := by
    exact inline77Block_eval memory (algorithmFold memory 0 77 f.lane)
  have h81 : inline78Block.eval memory f81 = f82 := by
    exact inline78Block_eval memory (algorithmFold memory 0 78 f.lane)
  have h82 : inline79Block.eval memory f82 = f83 := by
    exact inline79Block_eval memory (algorithmFold memory 0 79 f.lane)
  have h83 : coreExitBlock.eval memory f83 = f84 := by
    exact coreExitBlock_eval memory f83
  have hc : CoreEvalCert wholeCoreChain memory f0 f84 :=
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
    .cons call16Block _ h18 (
    .cons return18Block _ h19 (
    .cons inline18Block _ h20 (
    .cons inline19Block _ h21 (
    .cons call20Block _ h22 (
    .cons call22Block _ h23 (
    .cons return24Block _ h24 (
    .cons inline24Block _ h25 (
    .cons inline25Block _ h26 (
    .cons call26Block _ h27 (
    .cons call28Block _ h28 (
    .cons return30Block _ h29 (
    .cons inline30Block _ h30 (
    .cons inline31Block _ h31 (
    .cons group32Block _ h32 (
    .cons inline32Block _ h33 (
    .cons inline33Block _ h34 (
    .cons inline34Block _ h35 (
    .cons inline35Block _ h36 (
    .cons inline36Block _ h37 (
    .cons inline37Block _ h38 (
    .cons inline38Block _ h39 (
    .cons inline39Block _ h40 (
    .cons inline40Block _ h41 (
    .cons inline41Block _ h42 (
    .cons inline42Block _ h43 (
    .cons inline43Block _ h44 (
    .cons inline44Block _ h45 (
    .cons inline45Block _ h46 (
    .cons inline46Block _ h47 (
    .cons inline47Block _ h48 (
    .cons group48Block _ h49 (
    .cons inline48Block _ h50 (
    .cons inline49Block _ h51 (
    .cons inline50Block _ h52 (
    .cons inline51Block _ h53 (
    .cons inline52Block _ h54 (
    .cons inline53Block _ h55 (
    .cons inline54Block _ h56 (
    .cons inline55Block _ h57 (
    .cons inline56Block _ h58 (
    .cons inline57Block _ h59 (
    .cons inline58Block _ h60 (
    .cons inline59Block _ h61 (
    .cons inline60Block _ h62 (
    .cons inline61Block _ h63 (
    .cons inline62Block _ h64 (
    .cons inline63Block _ h65 (
    .cons group64Block _ h66 (
    .cons inline64Block _ h67 (
    .cons inline65Block _ h68 (
    .cons inline66Block _ h69 (
    .cons inline67Block _ h70 (
    .cons inline68Block _ h71 (
    .cons inline69Block _ h72 (
    .cons inline70Block _ h73 (
    .cons inline71Block _ h74 (
    .cons inline72Block _ h75 (
    .cons inline73Block _ h76 (
    .cons inline74Block _ h77 (
    .cons inline75Block _ h78 (
    .cons inline76Block _ h79 (
    .cons inline77Block _ h80 (
    .cons inline78Block _ h81 (
    .cons inline79Block _ h82 (
    .cons coreExitBlock _ h83 (.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact hc.sound

theorem algorithmKey_packed (j : Fin 5) :
    algorithmKey j.val =
      packed32 Crypto.Ripemd160.K[j.val]! Crypto.Ripemd160.KP[j.val]! := by
  have h : ∀ j : Fin 5, algorithmKey j.val =
      packed32 Crypto.Ripemd160.K[j.val]! Crypto.Ripemd160.KP[j.val]! := by decide
  exact h j


theorem algorithmRotation_group0 (i : Fin 16) :
    0 < Crypto.Ripemd160.s[0 + i.val]! ∧ Crypto.Ripemd160.s[0 + i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[0 + i.val]! ∧ Crypto.Ripemd160.sP[0 + i.val]! < 32 := by
  have h : ∀ i : Fin 16,
      0 < Crypto.Ripemd160.s[0 + i.val]! ∧ Crypto.Ripemd160.s[0 + i.val]! < 32 ∧
      0 < Crypto.Ripemd160.sP[0 + i.val]! ∧ Crypto.Ripemd160.sP[0 + i.val]! < 32 := by decide
  exact h i


theorem algorithmRotation_group1 (i : Fin 16) :
    0 < Crypto.Ripemd160.s[16 + i.val]! ∧ Crypto.Ripemd160.s[16 + i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[16 + i.val]! ∧ Crypto.Ripemd160.sP[16 + i.val]! < 32 := by
  have h : ∀ i : Fin 16,
      0 < Crypto.Ripemd160.s[16 + i.val]! ∧ Crypto.Ripemd160.s[16 + i.val]! < 32 ∧
      0 < Crypto.Ripemd160.sP[16 + i.val]! ∧ Crypto.Ripemd160.sP[16 + i.val]! < 32 := by decide
  exact h i


theorem algorithmRotation_group2 (i : Fin 16) :
    0 < Crypto.Ripemd160.s[32 + i.val]! ∧ Crypto.Ripemd160.s[32 + i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[32 + i.val]! ∧ Crypto.Ripemd160.sP[32 + i.val]! < 32 := by
  have h : ∀ i : Fin 16,
      0 < Crypto.Ripemd160.s[32 + i.val]! ∧ Crypto.Ripemd160.s[32 + i.val]! < 32 ∧
      0 < Crypto.Ripemd160.sP[32 + i.val]! ∧ Crypto.Ripemd160.sP[32 + i.val]! < 32 := by decide
  exact h i


theorem algorithmRotation_group3 (i : Fin 16) :
    0 < Crypto.Ripemd160.s[48 + i.val]! ∧ Crypto.Ripemd160.s[48 + i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[48 + i.val]! ∧ Crypto.Ripemd160.sP[48 + i.val]! < 32 := by
  have h : ∀ i : Fin 16,
      0 < Crypto.Ripemd160.s[48 + i.val]! ∧ Crypto.Ripemd160.s[48 + i.val]! < 32 ∧
      0 < Crypto.Ripemd160.sP[48 + i.val]! ∧ Crypto.Ripemd160.sP[48 + i.val]! < 32 := by decide
  exact h i


theorem algorithmRotation_group4 (i : Fin 16) :
    0 < Crypto.Ripemd160.s[64 + i.val]! ∧ Crypto.Ripemd160.s[64 + i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[64 + i.val]! ∧ Crypto.Ripemd160.sP[64 + i.val]! < 32 := by
  have h : ∀ i : Fin 16,
      0 < Crypto.Ripemd160.s[64 + i.val]! ∧ Crypto.Ripemd160.s[64 + i.val]! < 32 ∧
      0 < Crypto.Ripemd160.sP[64 + i.val]! ∧ Crypto.Ripemd160.sP[64 + i.val]! < 32 := by decide
  exact h i


theorem algorithmRotation_bounds (i : Fin 80) :
    0 < Crypto.Ripemd160.s[i.val]! ∧ Crypto.Ripemd160.s[i.val]! < 32 ∧
    0 < Crypto.Ripemd160.sP[i.val]! ∧ Crypto.Ripemd160.sP[i.val]! < 32 := by
  by_cases h0 : i.val < 16
  · have h := algorithmRotation_group0 ⟨i.val, h0⟩
    simpa only [Nat.zero_add] using h
  by_cases h1 : i.val < 32
  · have h := algorithmRotation_group1 ⟨i.val - 16, by omega⟩
    have he : 16 + (i.val - 16) = i.val := by omega
    simpa only [he] using h
  by_cases h2 : i.val < 48
  · have h := algorithmRotation_group2 ⟨i.val - 32, by omega⟩
    have he : 32 + (i.val - 32) = i.val := by omega
    simpa only [he] using h
  by_cases h3 : i.val < 64
  · have h := algorithmRotation_group3 ⟨i.val - 48, by omega⟩
    have he : 48 + (i.val - 48) = i.val := by omega
    simpa only [he] using h
  · have h := algorithmRotation_group4 ⟨i.val - 64, by omega⟩
    have he : 64 + (i.val - 64) = i.val := by omega
    simpa only [he] using h

theorem pairedWordFold_congr
    (group leftRotation rightRotation : Nat → Nat)
    (message0 constant0 message1 constant1 : Nat → UInt256)
    (count : Nat) (q : PairedLaneWordRound.WordLane)
    (hmessage : ∀ i < count, message0 i = message1 i)
    (hconstant : ∀ i < count, constant0 i = constant1 i) :
    pairedWordFold group leftRotation rightRotation message0 constant0 count q =
      pairedWordFold group leftRotation rightRotation message1 constant1 count q := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hprev := ih (fun j hj => hmessage j (by omega)) (fun j hj => hconstant j (by omega))
    change PairedLaneWordRound.wordStep (group i) (leftRotation i) (rightRotation i)
        (message0 i) (constant0 i)
        (pairedWordFold group leftRotation rightRotation message0 constant0 i q) =
      PairedLaneWordRound.wordStep (group i) (leftRotation i) (rightRotation i)
        (message1 i) (constant1 i)
        (pairedWordFold group leftRotation rightRotation message1 constant1 i q)
    rw [hmessage i (by omega), hconstant i (by omega), hprev]

theorem algorithmFold_crypto (memory : ByteArray) (words : Nat → UInt32)
    (count : Nat) (hcount : count ≤ 80)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hmessage : ∀ i < count, algorithmMessage memory i =
      packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)) :
    algorithmFold memory 0 count (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
          (fun i => words Crypto.Ripemd160.r[i]!) (fun i => Crypto.Ripemd160.K[i / 16]!) count left)
        (scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
          (fun i => words Crypto.Ripemd160.rP[i]!) (fun i => Crypto.Ripemd160.KP[i / 16]!) count right) := by
  simp only [algorithmFold, Nat.zero_add]
  have hconstant (i : Nat) (hi : i < count) :
      algorithmKey (i / 16) =
        packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]! :=
    algorithmKey_packed ⟨i / 16, by omega⟩
  have hrotation (i : Nat) (hi : i < count) :
      0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 ∧
      0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 :=
    algorithmRotation_bounds ⟨i, by omega⟩
  have h0 := pairedWordFold_congr
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (algorithmMessage memory) (fun i => algorithmKey (i / 16))
    (fun i => packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
    (fun i => packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!)
    count (PairedLaneWordRound.packCrypto left right) hmessage hconstant
  exact h0.trans (pairedWordFold_crypto
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (fun i => words Crypto.Ripemd160.r[i]!) (fun i => words Crypto.Ripemd160.rP[i]!)
    (fun i => Crypto.Ripemd160.K[i / 16]!) (fun i => Crypto.Ripemd160.KP[i / 16]!)
    count left right hrotation)



def coreCryptoResult (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) : CoreFrame :=
  ⟨PairedLaneWordRound.packCrypto
    (scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
      (fun i => words Crypto.Ripemd160.r[i]!) (fun i => Crypto.Ripemd160.K[i / 16]!) 80 left)
    (scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
      (fun i => words Crypto.Ripemd160.rP[i]!) (fun i => Crypto.Ripemd160.KP[i / 16]!) 80 right),
    algorithmKey 4⟩

theorem run_wholeCore_crypto (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s)
    (hmessage : ∀ i < 80, algorithmMessage s.memory i =
      packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho} =
      some {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} := by
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto left right, 0⟩
  have h0 := wholeCoreChain_eval s.memory f
  have h1 := algorithmFold_crypto s.memory words 80 (by decide) left right hmessage
  have he : wholeCoreChain.eval s.memory f = coreCryptoResult words left right :=
    h0.trans (congrArg (fun q => CoreFrame.mk q (algorithmKey 4)) h1)
  exact (run_wholeCoreChain s f rho hstack hrun hactive hvalid).trans
    (congrArg (fun q => some {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] q rho}) he)



/-- Normalized 32-bit words occupy disjoint low/high 128-bit lanes. -/
theorem packed32_eq_or (lo hi : UInt32) :
    packed32 lo hi =
      UInt256.lor (UInt256.shiftLeft (UInt256.ofNat hi.toNat) (UInt256.ofNat 128))
        (UInt256.ofNat lo.toNat) := by
  have hb (x : UInt32) : bits (UInt256.ofNat x.toNat) = x.toBitVec.setWidth 256 := by
    apply BitVec.eq_of_toNat_eq
    simp only [bits_ofNat, BitVec.toNat_ofNat, BitVec.toNat_setWidth, UInt32.toNat_toBitVec]
  apply bits_injective
  rw [packed32, bits_word, PairedLaneCore.pack, bits_lor,
    bits_shl _ 128 (by decide), hb hi, hb lo]
  have h := BitVec.setWidth_append_eq_shiftLeft_setWidth_or
    (b := hi.toBitVec.setWidth 128) (b' := lo.toBitVec.setWidth 128) (w'' := 256)
  simpa only [BitVec.setWidth_eq,
    BitVec.setWidth_setWidth (by decide : ¬ (128 < 32 ∧ 128 < 256))] using h


theorem algorithmIndex_group0 (i : Fin 16) :
    Crypto.Ripemd160.r[0 + i.val]! < 16 ∧
    Crypto.Ripemd160.rP[0 + i.val]! < 16 := by
  have h : ∀ i : Fin 16, Crypto.Ripemd160.r[0 + i.val]! < 16 ∧
      Crypto.Ripemd160.rP[0 + i.val]! < 16 := by decide
  exact h i


theorem algorithmIndex_group1 (i : Fin 16) :
    Crypto.Ripemd160.r[16 + i.val]! < 16 ∧
    Crypto.Ripemd160.rP[16 + i.val]! < 16 := by
  have h : ∀ i : Fin 16, Crypto.Ripemd160.r[16 + i.val]! < 16 ∧
      Crypto.Ripemd160.rP[16 + i.val]! < 16 := by decide
  exact h i


theorem algorithmIndex_group2 (i : Fin 16) :
    Crypto.Ripemd160.r[32 + i.val]! < 16 ∧
    Crypto.Ripemd160.rP[32 + i.val]! < 16 := by
  have h : ∀ i : Fin 16, Crypto.Ripemd160.r[32 + i.val]! < 16 ∧
      Crypto.Ripemd160.rP[32 + i.val]! < 16 := by decide
  exact h i


theorem algorithmIndex_group3 (i : Fin 16) :
    Crypto.Ripemd160.r[48 + i.val]! < 16 ∧
    Crypto.Ripemd160.rP[48 + i.val]! < 16 := by
  have h : ∀ i : Fin 16, Crypto.Ripemd160.r[48 + i.val]! < 16 ∧
      Crypto.Ripemd160.rP[48 + i.val]! < 16 := by decide
  exact h i


theorem algorithmIndex_group4 (i : Fin 16) :
    Crypto.Ripemd160.r[64 + i.val]! < 16 ∧
    Crypto.Ripemd160.rP[64 + i.val]! < 16 := by
  have h : ∀ i : Fin 16, Crypto.Ripemd160.r[64 + i.val]! < 16 ∧
      Crypto.Ripemd160.rP[64 + i.val]! < 16 := by decide
  exact h i


theorem algorithmIndex_bounds (i : Fin 80) :
    Crypto.Ripemd160.r[i.val]! < 16 ∧ Crypto.Ripemd160.rP[i.val]! < 16 := by
  by_cases h0 : i.val < 16
  · have h := algorithmIndex_group0 ⟨i.val, h0⟩
    simpa only [Nat.zero_add] using h
  by_cases h1 : i.val < 32
  · have h := algorithmIndex_group1 ⟨i.val - 16, by omega⟩
    have he : 16 + (i.val - 16) = i.val := by omega
    simpa only [he] using h
  by_cases h2 : i.val < 48
  · have h := algorithmIndex_group2 ⟨i.val - 32, by omega⟩
    have he : 32 + (i.val - 32) = i.val := by omega
    simpa only [he] using h
  by_cases h3 : i.val < 64
  · have h := algorithmIndex_group3 ⟨i.val - 48, by omega⟩
    have he : 48 + (i.val - 48) = i.val := by omega
    simpa only [he] using h
  · have h := algorithmIndex_group4 ⟨i.val - 64, by omega⟩
    have he : 64 + (i.val - 64) = i.val := by omega
    simpa only [he] using h


def NormalizedScheduleReady (memory : ByteArray) (words : Nat → UInt32) : Prop :=
  (∀ i < 16, MachineState.readWord memory (192 + 32 * i) = UInt256.ofNat (words i).toNat) ∧
  (∀ i < 16, MachineState.readWord memory (208 + 32 * i) =
    UInt256.shiftLeft (UInt256.ofNat (words i).toNat) (UInt256.ofNat 128))

theorem algorithmMessage_of_normalized (memory : ByteArray) (words : Nat → UInt32)
    (hready : NormalizedScheduleReady memory words) (i : Nat) (hi : i < 80) :
    algorithmMessage memory i =
      packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!) := by
  have hb := algorithmIndex_bounds ⟨i, hi⟩
  unfold algorithmMessage
  rw [hready.1 _ hb.1, hready.2 _ hb.2]
  exact (packed32_eq_or _ _).symm


theorem run_wholeCore_normalized (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s)
    (hready : NormalizedScheduleReady s.memory words) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho} =
      some {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} := by
  exact run_wholeCore_crypto s words left right rho hstack hrun hactive hvalid
    (algorithmMessage_of_normalized s.memory words hready)




open Challenge.EvmProof StackRoundTemplate

/-- Contiguous fetch only requires advancement before the last instruction. -/
theorem runLocatedBlock_eq_raw_terminal_sites
    {artifact : ProgramArtifact} {fork : Fork}
    (sites : List (LocatedSite artifact fork)) (template : List Instr)
    (hinst : sites.map (fun site => site.located.instruction) = template)
    (hcont : Contiguous sites) (s : State)
    (hhead : headPC sites = some s.pc)
    (hadvance : ∀ site, site ∈ sites.dropLast →
      ∀ {u v : State},
        Challenge.EvmProof.Stepper.runInstr site.located.instruction u = some v →
          v.pc = u.pc + UInt256.ofNat site.located.instruction.size) :
    Challenge.EvmProof.Stepper.runLocatedBlock (LocatedSite.path sites) s =
      runInstrSeq template s := by
  induction sites generalizing template s with
  | nil =>
      simp [headPC] at hhead
  | cons first rest ih =>
      cases rest with
      | nil =>
          have hpc : s.pc = first.pc := by
            simpa [headPC] using hhead.symm
          have htemplate : template = [first.located.instruction] := by
            simpa [LocatedSite.path] using hinst.symm
          subst template
          have hrun : Challenge.EvmProof.Stepper.runLocated first.located s =
              Challenge.EvmProof.Stepper.runInstr first.located.instruction s := by
            simp [Challenge.EvmProof.Stepper.runLocated, first.pc_eq, hpc]
          change (match Challenge.EvmProof.Stepper.runLocated first.located s with
            | none => none
            | some next => some next) =
            (match Challenge.EvmProof.Stepper.runInstr first.located.instruction s with
            | none => none
            | some next => some next)
          rw [hrun]
      | cons second tail =>
          have hpc : s.pc = first.pc := by
            simpa [headPC] using hhead.symm
          have hrun : ∀ {u v : State},
              Challenge.EvmProof.Stepper.runInstr first.located.instruction u = some v →
                v.pc = u.pc + UInt256.ofNat first.located.instruction.size := by
            intro u v hresult
            exact hadvance first (by simp) hresult
          rcases hcont with ⟨hnextPC, htailCont⟩
          have htemplate : template = first.located.instruction ::
              (second :: tail).map (fun site => site.located.instruction) := by
            simpa using hinst.symm
          subst template
          have hadvanceTail : ∀ site, site ∈ (second :: tail).dropLast →
              ∀ {u v : State},
                Challenge.EvmProof.Stepper.runInstr site.located.instruction u = some v →
                  v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
            intro site hmem u v hresult
            exact hadvance site (by simp only [List.dropLast_cons_cons]; exact List.mem_cons_of_mem first hmem) hresult
          cases hrunFirst :
              Challenge.EvmProof.Stepper.runInstr first.located.instruction s with
          | none =>
              simp [LocatedSite.path, Challenge.EvmProof.Stepper.runLocatedBlock,
                runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                first.pc_eq, hpc, hrunFirst]
          | some next =>
              have hnextPC' : next.pc = second.pc := by
                calc
                  next.pc = s.pc + UInt256.ofNat first.located.instruction.size :=
                    hrun hrunFirst
                  _ = first.pc + UInt256.ofNat first.located.instruction.size := by
                    rw [hpc]
                  _ = second.pc := hnextPC.symm
              have hheadTail : headPC (second :: tail) = some next.pc := by
                simp [headPC, hnextPC']
              have htail := ih (template := (second :: tail).map
                (fun site => site.located.instruction)) (by rfl) htailCont next
                hheadTail hadvanceTail
              cases hhalt : next.halt with
              | Running =>
                  have hloc :
                      Challenge.EvmProof.Stepper.runLocated first.located s = some next := by
                    simp [Challenge.EvmProof.Stepper.runLocated, first.pc_eq, hpc, hrunFirst]
                  change (match Challenge.EvmProof.Stepper.runLocated first.located s with
                    | none => none
                    | some next' =>
                        match (second :: tail).map (fun site => site.located) with
                        | [] => some next'
                        | _ :: _ =>
                            match next'.halt with
                            | .Running => Challenge.EvmProof.Stepper.runLocatedBlock
                                ((second :: tail).map (fun site => site.located)) next'
                            | _ => none) =
                    runInstrSeq (first.located.instruction ::
                      (second :: tail).map (fun site => site.located.instruction)) s
                  rw [hloc]
                  simp only [runInstrSeq, List.map]
                  rw [hrunFirst]
                  simp only [hhalt]
                  exact htail
              | Success =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Returned =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Reverted =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]
              | Exception error =>
                  simp [LocatedSite.path,
                    Challenge.EvmProof.Stepper.runLocatedBlock,
                    runInstrSeq, Challenge.EvmProof.Stepper.runLocated,
                    first.pc_eq, hpc, hrunFirst, hhalt]


theorem runLocatedBlock_eq_raw_terminal {artifact : ProgramArtifact} {fork : Fork}
    {code : List Instr} (site : GenericRoundSite artifact fork code)
    (s : State) (hpc : s.pc = site.startPC)
    (hform : ∀ instruction ∈ code.dropLast, DenseScheduleLift.Advances instruction) :
    Stepper.runLocatedBlock site.path s = runInstrSeq code s := by
  apply runLocatedBlock_eq_raw_terminal_sites site.sites code
    site.instruction_eq site.contiguous s
  · rw [site.head_eq]
    exact congrArg some hpc.symm
  · intro located hmem u v hresult
    apply DenseScheduleLift.runInstr_pc_of_advances _ hresult
    apply hform
    have h : located.located.instruction ∈
        site.sites.dropLast.map (fun item => item.located.instruction) :=
      List.mem_map_of_mem hmem
    rw [List.map_dropLast, site.instruction_eq] at h
    exact h


def gasSteps_terminal_of_raw {artifact : ProgramArtifact} {fork : Fork}
    {code : List Instr} (site : GenericRoundSite artifact fork code)
    (s t : State) (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = site.startPC)
    (hform : ∀ instruction ∈ code.dropLast, DenseScheduleLift.Advances instruction)
    (hresult : runInstrSeq code s = some t) : GasSteps s t := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
  · rw [runLocatedBlock_eq_raw_terminal site s hpc hform]
    exact hresult
  · exact hrun
  · exact hnp


def coreAdvancesCheck : Instr → Bool
  | .push _ _ => true
  | .op .ADD | .op .MUL | .op .AND | .op .OR | .op .XOR | .op .NOT |
    .op .SHL | .op .SHR | .op .POP | .op .MLOAD | .op .MSTORE | .op .JUMPDEST => true
  | .op (.Dup _) | .op (.Swap _) => true
  | _ => false

theorem coreAdvancesCheck_sound (instruction : Instr)
    (h : coreAdvancesCheck instruction = true) : DenseScheduleLift.Advances instruction := by
  cases instruction with
  | push width value => exact Or.inl (Or.inl (StraightLine.push width value))
  | op operation =>
    cases operation <;> first
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl (StraightLine.swap _))
      | (rename_i inner; cases inner <;> first
          | exact Or.inl (Or.inl StraightLine.add)
          | exact Or.inl (Or.inl StraightLine.and)
          | exact Or.inl (Or.inl StraightLine.or)
          | exact Or.inl (Or.inl StraightLine.xor)
          | exact Or.inl (Or.inl StraightLine.not)
          | exact Or.inl (Or.inl StraightLine.shl)
          | exact Or.inl (Or.inl StraightLine.shr)
          | exact Or.inl (Or.inl StraightLine.pop)
          | exact Or.inl (Or.inl StraightLine.mload)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
          | exact Or.inl (Or.inr (Or.inr rfl))
          | simp only [coreAdvancesCheck, Bool.false_eq_true] at h)


theorem coreAdvancesAll_sound (code : List Instr)
    (h : code.all coreAdvancesCheck = true) :
    ∀ instruction ∈ code, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  exact coreAdvancesCheck_sound instruction ((List.all_eq_true.mp h) instruction hmem)


theorem fullTemplate_terminal_advances :
    ∀ instruction ∈ fullTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide


theorem call16Template_terminal_advances :
    ∀ instruction ∈ call16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide


theorem inline0Template_terminal_advances :
    ∀ instruction ∈ inline0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide


def gasSteps_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate) (s : State)
    (q : Frame) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code q.ret.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := entryStack q rho}
      {s with pc := q.ret, stack := returnedStack q (rawT q (rawBoolean q)) (rawT (secondFrame q (rawT q (rawBoolean q))) (rawBoolean (secondFrame q (rawT q (rawBoolean q))))) rho} := by
  exact gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp rfl
    fullTemplate_terminal_advances (run_fullTemplate s site.startPC q rho hstack hrun hvalid)



/-- Metered execution for the same exact logical frame transition as CoreBlock. -/
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

theorem call20Template_terminal_advances :
    ∀ instruction ∈ call20Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem call22Template_terminal_advances :
    ∀ instruction ∈ call22Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem return24Template_terminal_advances :
    ∀ instruction ∈ return24Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline24Template_terminal_advances :
    ∀ instruction ∈ inline24Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem inline25Template_terminal_advances :
    ∀ instruction ∈ inline25Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

theorem call26Template_terminal_advances :
    ∀ instruction ∈ call26Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

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


theorem runInstrSeq_append_tail
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hwhole : runInstrSeq (first ++ second) s = some result) :
    runInstrSeq second middle = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst hwhole
      cases hfirst
      exact hwhole
  | cons instruction rest ih =>
      cases hrun : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil =>
                  simpa [runInstrSeq, hrun] using hwhole
              | cons nextInstruction secondRest =>
                  simpa [runInstrSeq, hrun, hmiddle] using hwhole
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have htail :
                      runInstrSeq (nextInstruction :: restTail) next = some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined :
                      runInstrSeq ((nextInstruction :: restTail) ++ second) next = some result := by
                    simpa [runInstrSeq, hrun, hhalt] using hwhole
                  exact ih htail hmiddle hjoined
              | Success =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst

def call16GasBlock {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork call16Template)
    (helper : GenericRoundSite artifact fork fullTemplate)
    (hpc : site.startPC = UInt256.ofNat 1880)
    (hhelper : helper.startPC = UInt256.ofNat 5168) :
    CoreGasBlock call16Block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    let q := f.frame
    have hh := hvalid 5168 (by decide)
    have raw0 := run_call16Template s (UInt256.ofNat 1880) q rho hstack hrun hactive hh
    have rawAll := call16Block.run s f rho hstack hrun hactive hvalid
    have raw1 : runInstrSeq fullTemplate
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call16Frame s.memory q) rho} =
        some {s with pc := UInt256.ofNat 1920, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call16Block.eval s.memory f) rho} :=
      runInstrSeq_append_tail (first := call16Template) (second := fullTemplate)
        raw0 hrun rawAll
    have g0 : GasSteps {s with pc := UInt256.ofNat 1880, stack := call16Entry q rho}
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call16Frame s.memory q) rho} :=
      gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm
        call16Template_terminal_advances raw0
    have g1 : GasSteps {s with pc := UInt256.ofNat 5168, stack := entryStack (call16Frame s.memory q) rho}
        {s with pc := UInt256.ofNat 1920, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call16Block.eval s.memory f) rho} :=
      gasSteps_terminal_of_raw helper _ _ hcode hfork hrun hnp hhelper.symm
        fullTemplate_terminal_advances raw1
    exact g0.trans g1

def call20GasBlock {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork call20Template)
    (helper : GenericRoundSite artifact fork fullTemplate)
    (hpc : site.startPC = UInt256.ofNat 2041)
    (hhelper : helper.startPC = UInt256.ofNat 5168) :
    CoreGasBlock call20Block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    let q := f.frame
    have hh := hvalid 5168 (by decide)
    have raw0 := run_call20Template s (UInt256.ofNat 2041) q rho hstack hrun hactive hh
    have rawAll := call20Block.run s f rho hstack hrun hactive hvalid
    have raw1 : runInstrSeq fullTemplate
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call20Frame s.memory q) rho} =
        some {s with pc := UInt256.ofNat 2077, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call20Block.eval s.memory f) rho} :=
      runInstrSeq_append_tail (first := call20Template) (second := fullTemplate)
        raw0 hrun rawAll
    have g0 : GasSteps {s with pc := UInt256.ofNat 2041, stack := call20Entry q rho}
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call20Frame s.memory q) rho} :=
      gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm
        call20Template_terminal_advances raw0
    have g1 : GasSteps {s with pc := UInt256.ofNat 5168, stack := entryStack (call20Frame s.memory q) rho}
        {s with pc := UInt256.ofNat 2077, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call20Block.eval s.memory f) rho} :=
      gasSteps_terminal_of_raw helper _ _ hcode hfork hrun hnp hhelper.symm
        fullTemplate_terminal_advances raw1
    exact g0.trans g1

def call22GasBlock {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork call22Template)
    (helper : GenericRoundSite artifact fork fullTemplate)
    (hpc : site.startPC = UInt256.ofNat 2077)
    (hhelper : helper.startPC = UInt256.ofNat 5168) :
    CoreGasBlock call22Block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    let q := f.frame
    have hh := hvalid 5168 (by decide)
    have raw0 := run_call22Template s (UInt256.ofNat 2077) q rho hstack hrun hactive hh
    have rawAll := call22Block.run s f rho hstack hrun hactive hvalid
    have raw1 : runInstrSeq fullTemplate
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call22Frame s.memory q) rho} =
        some {s with pc := UInt256.ofNat 2116, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call22Block.eval s.memory f) rho} :=
      runInstrSeq_append_tail (first := call22Template) (second := fullTemplate)
        raw0 hrun rawAll
    have g0 : GasSteps {s with pc := UInt256.ofNat 2077, stack := call22Entry q rho}
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call22Frame s.memory q) rho} :=
      gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm
        call22Template_terminal_advances raw0
    have g1 : GasSteps {s with pc := UInt256.ofNat 5168, stack := entryStack (call22Frame s.memory q) rho}
        {s with pc := UInt256.ofNat 2116, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call22Block.eval s.memory f) rho} :=
      gasSteps_terminal_of_raw helper _ _ hcode hfork hrun hnp hhelper.symm
        fullTemplate_terminal_advances raw1
    exact g0.trans g1

def call26GasBlock {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork call26Template)
    (helper : GenericRoundSite artifact fork fullTemplate)
    (hpc : site.startPC = UInt256.ofNat 2227)
    (hhelper : helper.startPC = UInt256.ofNat 5168) :
    CoreGasBlock call26Block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    let q := f.frame
    have hh := hvalid 5168 (by decide)
    have raw0 := run_call26Template s (UInt256.ofNat 2227) q rho hstack hrun hactive hh
    have rawAll := call26Block.run s f rho hstack hrun hactive hvalid
    have raw1 : runInstrSeq fullTemplate
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call26Frame s.memory q) rho} =
        some {s with pc := UInt256.ofNat 2264, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call26Block.eval s.memory f) rho} :=
      runInstrSeq_append_tail (first := call26Template) (second := fullTemplate)
        raw0 hrun rawAll
    have g0 : GasSteps {s with pc := UInt256.ofNat 2227, stack := call26Entry q rho}
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call26Frame s.memory q) rho} :=
      gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm
        call26Template_terminal_advances raw0
    have g1 : GasSteps {s with pc := UInt256.ofNat 5168, stack := entryStack (call26Frame s.memory q) rho}
        {s with pc := UInt256.ofNat 2264, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call26Block.eval s.memory f) rho} :=
      gasSteps_terminal_of_raw helper _ _ hcode hfork hrun hnp hhelper.symm
        fullTemplate_terminal_advances raw1
    exact g0.trans g1

def call28GasBlock {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork call28Template)
    (helper : GenericRoundSite artifact fork fullTemplate)
    (hpc : site.startPC = UInt256.ofNat 2264)
    (hhelper : helper.startPC = UInt256.ofNat 5168) :
    CoreGasBlock call28Block artifact fork where
  run := by
    intro s f rho hstack hrun hactive hvalid hcode hfork hnp
    let q := f.frame
    have hh := hvalid 5168 (by decide)
    have raw0 := run_call28Template s (UInt256.ofNat 2264) q rho hstack hrun hactive hh
    have rawAll := call28Block.run s f rho hstack hrun hactive hvalid
    have raw1 : runInstrSeq fullTemplate
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call28Frame s.memory q) rho} =
        some {s with pc := UInt256.ofNat 2303, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call28Block.eval s.memory f) rho} :=
      runInstrSeq_append_tail (first := call28Template) (second := fullTemplate)
        raw0 hrun rawAll
    have g0 : GasSteps {s with pc := UInt256.ofNat 2264, stack := call28Entry q rho}
        {s with pc := UInt256.ofNat 5168, stack := entryStack (call28Frame s.memory q) rho} :=
      gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp hpc.symm
        call28Template_terminal_advances raw0
    have g1 : GasSteps {s with pc := UInt256.ofNat 5168, stack := entryStack (call28Frame s.memory q) rho}
        {s with pc := UInt256.ofNat 2303, stack := coreStack [.a, .d, .b, .c, .upper, .e, .factor, .pair, .k, .lower] (call28Block.eval s.memory f) rho} :=
      gasSteps_terminal_of_raw helper _ _ hcode hfork hrun hnp hhelper.symm
        fullTemplate_terminal_advances raw1
    exact g0.trans g1

/-- Each physical window has its own exact bytecode binding; calls share one helper. -/
structure WholeCoreSites (artifact : ProgramArtifact) (fork : Fork) where
  group0 : {site : GenericRoundSite artifact fork group0Template // site.startPC = UInt256.ofNat 960}
  inline0 : {site : GenericRoundSite artifact fork inline0Template // site.startPC = UInt256.ofNat 981}
  inline1 : {site : GenericRoundSite artifact fork inline1Template // site.startPC = UInt256.ofNat 1035}
  inline2 : {site : GenericRoundSite artifact fork inline2Template // site.startPC = UInt256.ofNat 1089}
  inline3 : {site : GenericRoundSite artifact fork inline3Template // site.startPC = UInt256.ofNat 1144}
  inline4 : {site : GenericRoundSite artifact fork inline4Template // site.startPC = UInt256.ofNat 1198}
  inline5 : {site : GenericRoundSite artifact fork inline5Template // site.startPC = UInt256.ofNat 1253}
  inline6 : {site : GenericRoundSite artifact fork inline6Template // site.startPC = UInt256.ofNat 1308}
  inline7 : {site : GenericRoundSite artifact fork inline7Template // site.startPC = UInt256.ofNat 1363}
  inline8 : {site : GenericRoundSite artifact fork inline8Template // site.startPC = UInt256.ofNat 1418}
  inline9 : {site : GenericRoundSite artifact fork inline9Template // site.startPC = UInt256.ofNat 1473}
  inline10 : {site : GenericRoundSite artifact fork inline10Template // site.startPC = UInt256.ofNat 1528}
  inline11 : {site : GenericRoundSite artifact fork inline11Template // site.startPC = UInt256.ofNat 1583}
  inline12 : {site : GenericRoundSite artifact fork inline12Template // site.startPC = UInt256.ofNat 1638}
  inline13 : {site : GenericRoundSite artifact fork inline13Template // site.startPC = UInt256.ofNat 1692}
  inline14 : {site : GenericRoundSite artifact fork inline14Template // site.startPC = UInt256.ofNat 1747}
  inline15 : {site : GenericRoundSite artifact fork inline15Template // site.startPC = UInt256.ofNat 1802}
  group16 : {site : GenericRoundSite artifact fork group16Template // site.startPC = UInt256.ofNat 1857}
  call16 : {site : GenericRoundSite artifact fork call16Template // site.startPC = UInt256.ofNat 1880}
  return18 : {site : GenericRoundSite artifact fork return18Template // site.startPC = UInt256.ofNat 1920}
  inline18 : {site : GenericRoundSite artifact fork inline18Template // site.startPC = UInt256.ofNat 1921}
  inline19 : {site : GenericRoundSite artifact fork inline19Template // site.startPC = UInt256.ofNat 1981}
  call20 : {site : GenericRoundSite artifact fork call20Template // site.startPC = UInt256.ofNat 2041}
  call22 : {site : GenericRoundSite artifact fork call22Template // site.startPC = UInt256.ofNat 2077}
  return24 : {site : GenericRoundSite artifact fork return24Template // site.startPC = UInt256.ofNat 2116}
  inline24 : {site : GenericRoundSite artifact fork inline24Template // site.startPC = UInt256.ofNat 2117}
  inline25 : {site : GenericRoundSite artifact fork inline25Template // site.startPC = UInt256.ofNat 2167}
  call26 : {site : GenericRoundSite artifact fork call26Template // site.startPC = UInt256.ofNat 2227}
  call28 : {site : GenericRoundSite artifact fork call28Template // site.startPC = UInt256.ofNat 2264}
  return30 : {site : GenericRoundSite artifact fork return30Template // site.startPC = UInt256.ofNat 2303}
  inline30 : {site : GenericRoundSite artifact fork inline30Template // site.startPC = UInt256.ofNat 2304}
  inline31 : {site : GenericRoundSite artifact fork inline31Template // site.startPC = UInt256.ofNat 2353}
  group32 : {site : GenericRoundSite artifact fork group32Template // site.startPC = UInt256.ofNat 2414}
  inline32 : {site : GenericRoundSite artifact fork inline32Template // site.startPC = UInt256.ofNat 2437}
  inline33 : {site : GenericRoundSite artifact fork inline33Template // site.startPC = UInt256.ofNat 2487}
  inline34 : {site : GenericRoundSite artifact fork inline34Template // site.startPC = UInt256.ofNat 2537}
  inline35 : {site : GenericRoundSite artifact fork inline35Template // site.startPC = UInt256.ofNat 2586}
  inline36 : {site : GenericRoundSite artifact fork inline36Template // site.startPC = UInt256.ofNat 2636}
  inline37 : {site : GenericRoundSite artifact fork inline37Template // site.startPC = UInt256.ofNat 2686}
  inline38 : {site : GenericRoundSite artifact fork inline38Template // site.startPC = UInt256.ofNat 2736}
  inline39 : {site : GenericRoundSite artifact fork inline39Template // site.startPC = UInt256.ofNat 2786}
  inline40 : {site : GenericRoundSite artifact fork inline40Template // site.startPC = UInt256.ofNat 2835}
  inline41 : {site : GenericRoundSite artifact fork inline41Template // site.startPC = UInt256.ofNat 2885}
  inline42 : {site : GenericRoundSite artifact fork inline42Template // site.startPC = UInt256.ofNat 2935}
  inline43 : {site : GenericRoundSite artifact fork inline43Template // site.startPC = UInt256.ofNat 2984}
  inline44 : {site : GenericRoundSite artifact fork inline44Template // site.startPC = UInt256.ofNat 3034}
  inline45 : {site : GenericRoundSite artifact fork inline45Template // site.startPC = UInt256.ofNat 3084}
  inline46 : {site : GenericRoundSite artifact fork inline46Template // site.startPC = UInt256.ofNat 3133}
  inline47 : {site : GenericRoundSite artifact fork inline47Template // site.startPC = UInt256.ofNat 3173}
  group48 : {site : GenericRoundSite artifact fork group48Template // site.startPC = UInt256.ofNat 3213}
  inline48 : {site : GenericRoundSite artifact fork inline48Template // site.startPC = UInt256.ofNat 3236}
  inline49 : {site : GenericRoundSite artifact fork inline49Template // site.startPC = UInt256.ofNat 3296}
  inline50 : {site : GenericRoundSite artifact fork inline50Template // site.startPC = UInt256.ofNat 3357}
  inline51 : {site : GenericRoundSite artifact fork inline51Template // site.startPC = UInt256.ofNat 3418}
  inline52 : {site : GenericRoundSite artifact fork inline52Template // site.startPC = UInt256.ofNat 3478}
  inline53 : {site : GenericRoundSite artifact fork inline53Template // site.startPC = UInt256.ofNat 3528}
  inline54 : {site : GenericRoundSite artifact fork inline54Template // site.startPC = UInt256.ofNat 3589}
  inline55 : {site : GenericRoundSite artifact fork inline55Template // site.startPC = UInt256.ofNat 3650}
  inline56 : {site : GenericRoundSite artifact fork inline56Template // site.startPC = UInt256.ofNat 3710}
  inline57 : {site : GenericRoundSite artifact fork inline57Template // site.startPC = UInt256.ofNat 3771}
  inline58 : {site : GenericRoundSite artifact fork inline58Template // site.startPC = UInt256.ofNat 3832}
  inline59 : {site : GenericRoundSite artifact fork inline59Template // site.startPC = UInt256.ofNat 3893}
  inline60 : {site : GenericRoundSite artifact fork inline60Template // site.startPC = UInt256.ofNat 3954}
  inline61 : {site : GenericRoundSite artifact fork inline61Template // site.startPC = UInt256.ofNat 4015}
  inline62 : {site : GenericRoundSite artifact fork inline62Template // site.startPC = UInt256.ofNat 4076}
  inline63 : {site : GenericRoundSite artifact fork inline63Template // site.startPC = UInt256.ofNat 4137}
  group64 : {site : GenericRoundSite artifact fork group64Template // site.startPC = UInt256.ofNat 4198}
  inline64 : {site : GenericRoundSite artifact fork inline64Template // site.startPC = UInt256.ofNat 4205}
  inline65 : {site : GenericRoundSite artifact fork inline65Template // site.startPC = UInt256.ofNat 4260}
  inline66 : {site : GenericRoundSite artifact fork inline66Template // site.startPC = UInt256.ofNat 4314}
  inline67 : {site : GenericRoundSite artifact fork inline67Template // site.startPC = UInt256.ofNat 4369}
  inline68 : {site : GenericRoundSite artifact fork inline68Template // site.startPC = UInt256.ofNat 4424}
  inline69 : {site : GenericRoundSite artifact fork inline69Template // site.startPC = UInt256.ofNat 4478}
  inline70 : {site : GenericRoundSite artifact fork inline70Template // site.startPC = UInt256.ofNat 4533}
  inline71 : {site : GenericRoundSite artifact fork inline71Template // site.startPC = UInt256.ofNat 4588}
  inline72 : {site : GenericRoundSite artifact fork inline72Template // site.startPC = UInt256.ofNat 4643}
  inline73 : {site : GenericRoundSite artifact fork inline73Template // site.startPC = UInt256.ofNat 4698}
  inline74 : {site : GenericRoundSite artifact fork inline74Template // site.startPC = UInt256.ofNat 4752}
  inline75 : {site : GenericRoundSite artifact fork inline75Template // site.startPC = UInt256.ofNat 4807}
  inline76 : {site : GenericRoundSite artifact fork inline76Template // site.startPC = UInt256.ofNat 4862}
  inline77 : {site : GenericRoundSite artifact fork inline77Template // site.startPC = UInt256.ofNat 4916}
  inline78 : {site : GenericRoundSite artifact fork inline78Template // site.startPC = UInt256.ofNat 4971}
  inline79 : {site : GenericRoundSite artifact fork inline79Template // site.startPC = UInt256.ofNat 5026}
  coreExit : {site : GenericRoundSite artifact fork coreExitTemplate // site.startPC = UInt256.ofNat 5081}
  helper : {site : GenericRoundSite artifact fork fullTemplate // site.startPC = UInt256.ofNat 5168}

def wholeCoreGasChain {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) : CoreGasChain artifact fork wholeCoreChain :=
  .cons group0Block _ (CoreGasBlock.of_site group0Block sites.group0.val sites.group0.property group0Template_terminal_advances) (
  .cons inline0Block _ (CoreGasBlock.of_site inline0Block sites.inline0.val sites.inline0.property inline0Template_terminal_advances) (
  .cons inline1Block _ (CoreGasBlock.of_site inline1Block sites.inline1.val sites.inline1.property inline1Template_terminal_advances) (
  .cons inline2Block _ (CoreGasBlock.of_site inline2Block sites.inline2.val sites.inline2.property inline2Template_terminal_advances) (
  .cons inline3Block _ (CoreGasBlock.of_site inline3Block sites.inline3.val sites.inline3.property inline3Template_terminal_advances) (
  .cons inline4Block _ (CoreGasBlock.of_site inline4Block sites.inline4.val sites.inline4.property inline4Template_terminal_advances) (
  .cons inline5Block _ (CoreGasBlock.of_site inline5Block sites.inline5.val sites.inline5.property inline5Template_terminal_advances) (
  .cons inline6Block _ (CoreGasBlock.of_site inline6Block sites.inline6.val sites.inline6.property inline6Template_terminal_advances) (
  .cons inline7Block _ (CoreGasBlock.of_site inline7Block sites.inline7.val sites.inline7.property inline7Template_terminal_advances) (
  .cons inline8Block _ (CoreGasBlock.of_site inline8Block sites.inline8.val sites.inline8.property inline8Template_terminal_advances) (
  .cons inline9Block _ (CoreGasBlock.of_site inline9Block sites.inline9.val sites.inline9.property inline9Template_terminal_advances) (
  .cons inline10Block _ (CoreGasBlock.of_site inline10Block sites.inline10.val sites.inline10.property inline10Template_terminal_advances) (
  .cons inline11Block _ (CoreGasBlock.of_site inline11Block sites.inline11.val sites.inline11.property inline11Template_terminal_advances) (
  .cons inline12Block _ (CoreGasBlock.of_site inline12Block sites.inline12.val sites.inline12.property inline12Template_terminal_advances) (
  .cons inline13Block _ (CoreGasBlock.of_site inline13Block sites.inline13.val sites.inline13.property inline13Template_terminal_advances) (
  .cons inline14Block _ (CoreGasBlock.of_site inline14Block sites.inline14.val sites.inline14.property inline14Template_terminal_advances) (
  .cons inline15Block _ (CoreGasBlock.of_site inline15Block sites.inline15.val sites.inline15.property inline15Template_terminal_advances) (
  .cons group16Block _ (CoreGasBlock.of_site group16Block sites.group16.val sites.group16.property group16Template_terminal_advances) (
  .cons call16Block _ (call16GasBlock sites.call16.val sites.helper.val sites.call16.property sites.helper.property) (
  .cons return18Block _ (CoreGasBlock.of_site return18Block sites.return18.val sites.return18.property return18Template_terminal_advances) (
  .cons inline18Block _ (CoreGasBlock.of_site inline18Block sites.inline18.val sites.inline18.property inline18Template_terminal_advances) (
  .cons inline19Block _ (CoreGasBlock.of_site inline19Block sites.inline19.val sites.inline19.property inline19Template_terminal_advances) (
  .cons call20Block _ (call20GasBlock sites.call20.val sites.helper.val sites.call20.property sites.helper.property) (
  .cons call22Block _ (call22GasBlock sites.call22.val sites.helper.val sites.call22.property sites.helper.property) (
  .cons return24Block _ (CoreGasBlock.of_site return24Block sites.return24.val sites.return24.property return24Template_terminal_advances) (
  .cons inline24Block _ (CoreGasBlock.of_site inline24Block sites.inline24.val sites.inline24.property inline24Template_terminal_advances) (
  .cons inline25Block _ (CoreGasBlock.of_site inline25Block sites.inline25.val sites.inline25.property inline25Template_terminal_advances) (
  .cons call26Block _ (call26GasBlock sites.call26.val sites.helper.val sites.call26.property sites.helper.property) (
  .cons call28Block _ (call28GasBlock sites.call28.val sites.helper.val sites.call28.property sites.helper.property) (
  .cons return30Block _ (CoreGasBlock.of_site return30Block sites.return30.val sites.return30.property return30Template_terminal_advances) (
  .cons inline30Block _ (CoreGasBlock.of_site inline30Block sites.inline30.val sites.inline30.property inline30Template_terminal_advances) (
  .cons inline31Block _ (CoreGasBlock.of_site inline31Block sites.inline31.val sites.inline31.property inline31Template_terminal_advances) (
  .cons group32Block _ (CoreGasBlock.of_site group32Block sites.group32.val sites.group32.property group32Template_terminal_advances) (
  .cons inline32Block _ (CoreGasBlock.of_site inline32Block sites.inline32.val sites.inline32.property inline32Template_terminal_advances) (
  .cons inline33Block _ (CoreGasBlock.of_site inline33Block sites.inline33.val sites.inline33.property inline33Template_terminal_advances) (
  .cons inline34Block _ (CoreGasBlock.of_site inline34Block sites.inline34.val sites.inline34.property inline34Template_terminal_advances) (
  .cons inline35Block _ (CoreGasBlock.of_site inline35Block sites.inline35.val sites.inline35.property inline35Template_terminal_advances) (
  .cons inline36Block _ (CoreGasBlock.of_site inline36Block sites.inline36.val sites.inline36.property inline36Template_terminal_advances) (
  .cons inline37Block _ (CoreGasBlock.of_site inline37Block sites.inline37.val sites.inline37.property inline37Template_terminal_advances) (
  .cons inline38Block _ (CoreGasBlock.of_site inline38Block sites.inline38.val sites.inline38.property inline38Template_terminal_advances) (
  .cons inline39Block _ (CoreGasBlock.of_site inline39Block sites.inline39.val sites.inline39.property inline39Template_terminal_advances) (
  .cons inline40Block _ (CoreGasBlock.of_site inline40Block sites.inline40.val sites.inline40.property inline40Template_terminal_advances) (
  .cons inline41Block _ (CoreGasBlock.of_site inline41Block sites.inline41.val sites.inline41.property inline41Template_terminal_advances) (
  .cons inline42Block _ (CoreGasBlock.of_site inline42Block sites.inline42.val sites.inline42.property inline42Template_terminal_advances) (
  .cons inline43Block _ (CoreGasBlock.of_site inline43Block sites.inline43.val sites.inline43.property inline43Template_terminal_advances) (
  .cons inline44Block _ (CoreGasBlock.of_site inline44Block sites.inline44.val sites.inline44.property inline44Template_terminal_advances) (
  .cons inline45Block _ (CoreGasBlock.of_site inline45Block sites.inline45.val sites.inline45.property inline45Template_terminal_advances) (
  .cons inline46Block _ (CoreGasBlock.of_site inline46Block sites.inline46.val sites.inline46.property inline46Template_terminal_advances) (
  .cons inline47Block _ (CoreGasBlock.of_site inline47Block sites.inline47.val sites.inline47.property inline47Template_terminal_advances) (
  .cons group48Block _ (CoreGasBlock.of_site group48Block sites.group48.val sites.group48.property group48Template_terminal_advances) (
  .cons inline48Block _ (CoreGasBlock.of_site inline48Block sites.inline48.val sites.inline48.property inline48Template_terminal_advances) (
  .cons inline49Block _ (CoreGasBlock.of_site inline49Block sites.inline49.val sites.inline49.property inline49Template_terminal_advances) (
  .cons inline50Block _ (CoreGasBlock.of_site inline50Block sites.inline50.val sites.inline50.property inline50Template_terminal_advances) (
  .cons inline51Block _ (CoreGasBlock.of_site inline51Block sites.inline51.val sites.inline51.property inline51Template_terminal_advances) (
  .cons inline52Block _ (CoreGasBlock.of_site inline52Block sites.inline52.val sites.inline52.property inline52Template_terminal_advances) (
  .cons inline53Block _ (CoreGasBlock.of_site inline53Block sites.inline53.val sites.inline53.property inline53Template_terminal_advances) (
  .cons inline54Block _ (CoreGasBlock.of_site inline54Block sites.inline54.val sites.inline54.property inline54Template_terminal_advances) (
  .cons inline55Block _ (CoreGasBlock.of_site inline55Block sites.inline55.val sites.inline55.property inline55Template_terminal_advances) (
  .cons inline56Block _ (CoreGasBlock.of_site inline56Block sites.inline56.val sites.inline56.property inline56Template_terminal_advances) (
  .cons inline57Block _ (CoreGasBlock.of_site inline57Block sites.inline57.val sites.inline57.property inline57Template_terminal_advances) (
  .cons inline58Block _ (CoreGasBlock.of_site inline58Block sites.inline58.val sites.inline58.property inline58Template_terminal_advances) (
  .cons inline59Block _ (CoreGasBlock.of_site inline59Block sites.inline59.val sites.inline59.property inline59Template_terminal_advances) (
  .cons inline60Block _ (CoreGasBlock.of_site inline60Block sites.inline60.val sites.inline60.property inline60Template_terminal_advances) (
  .cons inline61Block _ (CoreGasBlock.of_site inline61Block sites.inline61.val sites.inline61.property inline61Template_terminal_advances) (
  .cons inline62Block _ (CoreGasBlock.of_site inline62Block sites.inline62.val sites.inline62.property inline62Template_terminal_advances) (
  .cons inline63Block _ (CoreGasBlock.of_site inline63Block sites.inline63.val sites.inline63.property inline63Template_terminal_advances) (
  .cons group64Block _ (CoreGasBlock.of_site group64Block sites.group64.val sites.group64.property group64Template_terminal_advances) (
  .cons inline64Block _ (CoreGasBlock.of_site inline64Block sites.inline64.val sites.inline64.property inline64Template_terminal_advances) (
  .cons inline65Block _ (CoreGasBlock.of_site inline65Block sites.inline65.val sites.inline65.property inline65Template_terminal_advances) (
  .cons inline66Block _ (CoreGasBlock.of_site inline66Block sites.inline66.val sites.inline66.property inline66Template_terminal_advances) (
  .cons inline67Block _ (CoreGasBlock.of_site inline67Block sites.inline67.val sites.inline67.property inline67Template_terminal_advances) (
  .cons inline68Block _ (CoreGasBlock.of_site inline68Block sites.inline68.val sites.inline68.property inline68Template_terminal_advances) (
  .cons inline69Block _ (CoreGasBlock.of_site inline69Block sites.inline69.val sites.inline69.property inline69Template_terminal_advances) (
  .cons inline70Block _ (CoreGasBlock.of_site inline70Block sites.inline70.val sites.inline70.property inline70Template_terminal_advances) (
  .cons inline71Block _ (CoreGasBlock.of_site inline71Block sites.inline71.val sites.inline71.property inline71Template_terminal_advances) (
  .cons inline72Block _ (CoreGasBlock.of_site inline72Block sites.inline72.val sites.inline72.property inline72Template_terminal_advances) (
  .cons inline73Block _ (CoreGasBlock.of_site inline73Block sites.inline73.val sites.inline73.property inline73Template_terminal_advances) (
  .cons inline74Block _ (CoreGasBlock.of_site inline74Block sites.inline74.val sites.inline74.property inline74Template_terminal_advances) (
  .cons inline75Block _ (CoreGasBlock.of_site inline75Block sites.inline75.val sites.inline75.property inline75Template_terminal_advances) (
  .cons inline76Block _ (CoreGasBlock.of_site inline76Block sites.inline76.val sites.inline76.property inline76Template_terminal_advances) (
  .cons inline77Block _ (CoreGasBlock.of_site inline77Block sites.inline77.val sites.inline77.property inline77Template_terminal_advances) (
  .cons inline78Block _ (CoreGasBlock.of_site inline78Block sites.inline78.val sites.inline78.property inline78Template_terminal_advances) (
  .cons inline79Block _ (CoreGasBlock.of_site inline79Block sites.inline79.val sites.inline79.property inline79Template_terminal_advances) (
  .cons coreExitBlock _ (CoreGasBlock.of_site coreExitBlock sites.coreExit.val sites.coreExit.property coreExitTemplate_terminal_advances) (.nil 5083 [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def gasSteps_wholeCore {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho}
      {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (wholeCoreChain.eval s.memory f) rho} :=
  (wholeCoreGasChain sites).run s f rho hstack hrun hactive hvalid hcode hfork hnp

def gasSteps_wholeCore_normalized {artifact : ProgramArtifact} {fork : Fork}
    (sites : WholeCoreSites artifact fork) (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hvalid : CoreJumpValid s)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hready : NormalizedScheduleReady s.memory words) :
    GasSteps {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho}
      {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} := by
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto left right, 0⟩
  have h0 := wholeCoreChain_eval s.memory f
  have h1 := algorithmFold_crypto s.memory words 80 (by decide) left right
    (algorithmMessage_of_normalized s.memory words hready)
  have he : wholeCoreChain.eval s.memory f = coreCryptoResult words left right :=
    h0.trans (congrArg (fun q => CoreFrame.mk q (algorithmKey 4)) h1)
  exact (gasSteps_wholeCore sites s f rho hstack hrun hactive hvalid hcode hfork hnp).cast rfl
    (congrArg (fun q => {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] q rho}) he)

#print axioms template_length
#print axioms run_template
#print axioms rawBoolean_eq
#print axioms firstTTemplate_length
#print axioms run_firstTTemplate
#print axioms firstC10Template_length
#print axioms run_firstC10Template
#print axioms secondBooleanTemplate_length
#print axioms run_secondBooleanTemplate
#print axioms secondTTemplate_length
#print axioms run_secondTTemplate
#print axioms secondC10Template_length
#print axioms run_secondC10Template
#print axioms run_returnTemplate
#print axioms fullTemplate_length
#print axioms fullTemplate_byteLength
#print axioms run_fullTemplate
#print axioms uand_comm
#print axioms umul_comm
#print axioms wordBlend_self
#print axioms wordRotate_eq_blend
#print axioms rawSum_eq
#print axioms rawRotation_eq
#print axioms rawT_eq
#print axioms rawC10_eq
#print axioms secondFrame_wordStep
#print axioms fullTemplate_eq_frozenHelper
#print axioms run_fullTemplate_word
#print axioms twoWordSteps_of_crypto
#print axioms run_fullTemplate_crypto
#print axioms active_schedule_preserved
#print axioms rawSum_of_boolean
#print axioms rawT_of_boolean
#print axioms inline0Boolean_eq
#print axioms inline2Boolean_eq
#print axioms inline3Boolean_eq
#print axioms inline4Boolean_eq
#print axioms inlineProduct_eq
#print axioms inlineT_eq_rawT
#print axioms singleT_eq_rawT
#print axioms inline0Template_length
#print axioms run_inline0Template
#print axioms run_inline0Template_word
#print axioms inline1Template_length
#print axioms run_inline1Template
#print axioms run_inline1Template_word
#print axioms inline2Template_length
#print axioms run_inline2Template
#print axioms run_inline2Template_word
#print axioms inline3Template_length
#print axioms run_inline3Template
#print axioms run_inline3Template_word
#print axioms inline4Template_length
#print axioms run_inline4Template
#print axioms run_inline4Template_word
#print axioms inline5Template_length
#print axioms run_inline5Template
#print axioms run_inline5Template_word
#print axioms inline6Template_length
#print axioms run_inline6Template
#print axioms run_inline6Template_word
#print axioms inline7Template_length
#print axioms run_inline7Template
#print axioms run_inline7Template_word
#print axioms inline8Template_length
#print axioms run_inline8Template
#print axioms run_inline8Template_word
#print axioms inline9Template_length
#print axioms run_inline9Template
#print axioms run_inline9Template_word
#print axioms inline10Template_length
#print axioms run_inline10Template
#print axioms run_inline10Template_word
#print axioms inline11Template_length
#print axioms run_inline11Template
#print axioms run_inline11Template_word
#print axioms inline12Template_length
#print axioms run_inline12Template
#print axioms run_inline12Template_word
#print axioms inline13Template_length
#print axioms run_inline13Template
#print axioms run_inline13Template_word
#print axioms inline14Template_length
#print axioms run_inline14Template
#print axioms run_inline14Template_word
#print axioms inline15Template_length
#print axioms run_inline15Template
#print axioms run_inline15Template_word
#print axioms inline18Template_length
#print axioms run_inline18Template
#print axioms run_inline18Template_word
#print axioms inline19Template_length
#print axioms run_inline19Template
#print axioms run_inline19Template_word
#print axioms inline24Template_length
#print axioms run_inline24Template
#print axioms run_inline24Template_word
#print axioms inline25Template_length
#print axioms run_inline25Template
#print axioms run_inline25Template_word
#print axioms inline30Template_length
#print axioms run_inline30Template
#print axioms run_inline30Template_word
#print axioms inline31Template_length
#print axioms run_inline31Template
#print axioms run_inline31Template_word
#print axioms inline32Template_length
#print axioms run_inline32Template
#print axioms run_inline32Template_word
#print axioms inline33Template_length
#print axioms run_inline33Template
#print axioms run_inline33Template_word
#print axioms inline34Template_length
#print axioms run_inline34Template
#print axioms run_inline34Template_word
#print axioms inline35Template_length
#print axioms run_inline35Template
#print axioms run_inline35Template_word
#print axioms inline36Template_length
#print axioms run_inline36Template
#print axioms run_inline36Template_word
#print axioms inline37Template_length
#print axioms run_inline37Template
#print axioms run_inline37Template_word
#print axioms inline38Template_length
#print axioms run_inline38Template
#print axioms run_inline38Template_word
#print axioms inline39Template_length
#print axioms run_inline39Template
#print axioms run_inline39Template_word
#print axioms inline40Template_length
#print axioms run_inline40Template
#print axioms run_inline40Template_word
#print axioms inline41Template_length
#print axioms run_inline41Template
#print axioms run_inline41Template_word
#print axioms inline42Template_length
#print axioms run_inline42Template
#print axioms run_inline42Template_word
#print axioms inline43Template_length
#print axioms run_inline43Template
#print axioms run_inline43Template_word
#print axioms inline44Template_length
#print axioms run_inline44Template
#print axioms run_inline44Template_word
#print axioms inline45Template_length
#print axioms run_inline45Template
#print axioms run_inline45Template_word
#print axioms inline46Template_length
#print axioms run_inline46Template
#print axioms run_inline46Template_word
#print axioms inline47Template_length
#print axioms run_inline47Template
#print axioms run_inline47Template_word
#print axioms inline48Template_length
#print axioms run_inline48Template
#print axioms run_inline48Template_word
#print axioms inline49Template_length
#print axioms run_inline49Template
#print axioms run_inline49Template_word
#print axioms inline50Template_length
#print axioms run_inline50Template
#print axioms run_inline50Template_word
#print axioms inline51Template_length
#print axioms run_inline51Template
#print axioms run_inline51Template_word
#print axioms inline52Template_length
#print axioms run_inline52Template
#print axioms run_inline52Template_word
#print axioms inline53Template_length
#print axioms run_inline53Template
#print axioms run_inline53Template_word
#print axioms inline54Template_length
#print axioms run_inline54Template
#print axioms run_inline54Template_word
#print axioms inline55Template_length
#print axioms run_inline55Template
#print axioms run_inline55Template_word
#print axioms inline56Template_length
#print axioms run_inline56Template
#print axioms run_inline56Template_word
#print axioms inline57Template_length
#print axioms run_inline57Template
#print axioms run_inline57Template_word
#print axioms inline58Template_length
#print axioms run_inline58Template
#print axioms run_inline58Template_word
#print axioms inline59Template_length
#print axioms run_inline59Template
#print axioms run_inline59Template_word
#print axioms inline60Template_length
#print axioms run_inline60Template
#print axioms run_inline60Template_word
#print axioms inline61Template_length
#print axioms run_inline61Template
#print axioms run_inline61Template_word
#print axioms inline62Template_length
#print axioms run_inline62Template
#print axioms run_inline62Template_word
#print axioms inline63Template_length
#print axioms run_inline63Template
#print axioms run_inline63Template_word
#print axioms inline64Template_length
#print axioms run_inline64Template
#print axioms run_inline64Template_word
#print axioms inline65Template_length
#print axioms run_inline65Template
#print axioms run_inline65Template_word
#print axioms inline66Template_length
#print axioms run_inline66Template
#print axioms run_inline66Template_word
#print axioms inline67Template_length
#print axioms run_inline67Template
#print axioms run_inline67Template_word
#print axioms inline68Template_length
#print axioms run_inline68Template
#print axioms run_inline68Template_word
#print axioms inline69Template_length
#print axioms run_inline69Template
#print axioms run_inline69Template_word
#print axioms inline70Template_length
#print axioms run_inline70Template
#print axioms run_inline70Template_word
#print axioms inline71Template_length
#print axioms run_inline71Template
#print axioms run_inline71Template_word
#print axioms inline72Template_length
#print axioms run_inline72Template
#print axioms run_inline72Template_word
#print axioms inline73Template_length
#print axioms run_inline73Template
#print axioms run_inline73Template_word
#print axioms inline74Template_length
#print axioms run_inline74Template
#print axioms run_inline74Template_word
#print axioms inline75Template_length
#print axioms run_inline75Template
#print axioms run_inline75Template_word
#print axioms inline76Template_length
#print axioms run_inline76Template
#print axioms run_inline76Template_word
#print axioms inline77Template_length
#print axioms run_inline77Template
#print axioms run_inline77Template_word
#print axioms inline78Template_length
#print axioms run_inline78Template
#print axioms run_inline78Template_word
#print axioms inline79Template_length
#print axioms run_inline79Template
#print axioms run_inline79Template_word
#print axioms call16Template_length
#print axioms run_call16Template
#print axioms run_call16Template_word
#print axioms call20Template_length
#print axioms run_call20Template
#print axioms run_call20Template_word
#print axioms call22Template_length
#print axioms run_call22Template
#print axioms run_call22Template_word
#print axioms call26Template_length
#print axioms run_call26Template
#print axioms run_call26Template_word
#print axioms call28Template_length
#print axioms run_call28Template
#print axioms run_call28Template_word
#print axioms run_group0Template
#print axioms run_group16Template
#print axioms run_return18Template
#print axioms run_return24Template
#print axioms run_return30Template
#print axioms run_group32Template
#print axioms run_group48Template
#print axioms run_group64Template
#print axioms run_coreExitTemplate
#print axioms CoreChain.run
#print axioms group0Block
#print axioms inline0Block
#print axioms inline1Block
#print axioms inline2Block
#print axioms inline3Block
#print axioms inline4Block
#print axioms inline5Block
#print axioms inline6Block
#print axioms inline7Block
#print axioms inline8Block
#print axioms inline9Block
#print axioms inline10Block
#print axioms inline11Block
#print axioms inline12Block
#print axioms inline13Block
#print axioms inline14Block
#print axioms inline15Block
#print axioms group16Block
#print axioms call16Block
#print axioms return18Block
#print axioms inline18Block
#print axioms inline19Block
#print axioms call20Block
#print axioms call22Block
#print axioms return24Block
#print axioms inline24Block
#print axioms inline25Block
#print axioms call26Block
#print axioms call28Block
#print axioms return30Block
#print axioms inline30Block
#print axioms inline31Block
#print axioms group32Block
#print axioms inline32Block
#print axioms inline33Block
#print axioms inline34Block
#print axioms inline35Block
#print axioms inline36Block
#print axioms inline37Block
#print axioms inline38Block
#print axioms inline39Block
#print axioms inline40Block
#print axioms inline41Block
#print axioms inline42Block
#print axioms inline43Block
#print axioms inline44Block
#print axioms inline45Block
#print axioms inline46Block
#print axioms inline47Block
#print axioms group48Block
#print axioms inline48Block
#print axioms inline49Block
#print axioms inline50Block
#print axioms inline51Block
#print axioms inline52Block
#print axioms inline53Block
#print axioms inline54Block
#print axioms inline55Block
#print axioms inline56Block
#print axioms inline57Block
#print axioms inline58Block
#print axioms inline59Block
#print axioms inline60Block
#print axioms inline61Block
#print axioms inline62Block
#print axioms inline63Block
#print axioms group64Block
#print axioms inline64Block
#print axioms inline65Block
#print axioms inline66Block
#print axioms inline67Block
#print axioms inline68Block
#print axioms inline69Block
#print axioms inline70Block
#print axioms inline71Block
#print axioms inline72Block
#print axioms inline73Block
#print axioms inline74Block
#print axioms inline75Block
#print axioms inline76Block
#print axioms inline77Block
#print axioms inline78Block
#print axioms inline79Block
#print axioms coreExitBlock
#print axioms run_wholeCoreChain
#print axioms pairedWordFold_crypto
#print axioms pairedWordFold_add
#print axioms group0Block_eval
#print axioms inline0Block_eval
#print axioms inline1Block_eval
#print axioms inline2Block_eval
#print axioms inline3Block_eval
#print axioms inline4Block_eval
#print axioms inline5Block_eval
#print axioms inline6Block_eval
#print axioms inline7Block_eval
#print axioms inline8Block_eval
#print axioms inline9Block_eval
#print axioms inline10Block_eval
#print axioms inline11Block_eval
#print axioms inline12Block_eval
#print axioms inline13Block_eval
#print axioms inline14Block_eval
#print axioms inline15Block_eval
#print axioms group16Block_eval
#print axioms call16Block_eval
#print axioms return18Block_eval
#print axioms inline18Block_eval
#print axioms inline19Block_eval
#print axioms call20Block_eval
#print axioms call22Block_eval
#print axioms return24Block_eval
#print axioms inline24Block_eval
#print axioms inline25Block_eval
#print axioms call26Block_eval
#print axioms call28Block_eval
#print axioms return30Block_eval
#print axioms inline30Block_eval
#print axioms inline31Block_eval
#print axioms group32Block_eval
#print axioms inline32Block_eval
#print axioms inline33Block_eval
#print axioms inline34Block_eval
#print axioms inline35Block_eval
#print axioms inline36Block_eval
#print axioms inline37Block_eval
#print axioms inline38Block_eval
#print axioms inline39Block_eval
#print axioms inline40Block_eval
#print axioms inline41Block_eval
#print axioms inline42Block_eval
#print axioms inline43Block_eval
#print axioms inline44Block_eval
#print axioms inline45Block_eval
#print axioms inline46Block_eval
#print axioms inline47Block_eval
#print axioms group48Block_eval
#print axioms inline48Block_eval
#print axioms inline49Block_eval
#print axioms inline50Block_eval
#print axioms inline51Block_eval
#print axioms inline52Block_eval
#print axioms inline53Block_eval
#print axioms inline54Block_eval
#print axioms inline55Block_eval
#print axioms inline56Block_eval
#print axioms inline57Block_eval
#print axioms inline58Block_eval
#print axioms inline59Block_eval
#print axioms inline60Block_eval
#print axioms inline61Block_eval
#print axioms inline62Block_eval
#print axioms inline63Block_eval
#print axioms group64Block_eval
#print axioms inline64Block_eval
#print axioms inline65Block_eval
#print axioms inline66Block_eval
#print axioms inline67Block_eval
#print axioms inline68Block_eval
#print axioms inline69Block_eval
#print axioms inline70Block_eval
#print axioms inline71Block_eval
#print axioms inline72Block_eval
#print axioms inline73Block_eval
#print axioms inline74Block_eval
#print axioms inline75Block_eval
#print axioms inline76Block_eval
#print axioms inline77Block_eval
#print axioms inline78Block_eval
#print axioms inline79Block_eval
#print axioms coreExitBlock_eval
#print axioms CoreEvalCert.sound
#print axioms algorithmFold_succ
#print axioms wholeCoreChain_eval
#print axioms algorithmRotation_group0
#print axioms algorithmRotation_group1
#print axioms algorithmRotation_group2
#print axioms algorithmRotation_group3
#print axioms algorithmRotation_group4
#print axioms algorithmKey_packed
#print axioms algorithmRotation_bounds
#print axioms pairedWordFold_congr
#print axioms algorithmFold_crypto
#print axioms run_wholeCore_crypto
#print axioms packed32_eq_or
#print axioms algorithmIndex_group0
#print axioms algorithmIndex_group1
#print axioms algorithmIndex_group2
#print axioms algorithmIndex_group3
#print axioms algorithmIndex_group4
#print axioms algorithmIndex_bounds
#print axioms algorithmMessage_of_normalized
#print axioms run_wholeCore_normalized
#print axioms runLocatedBlock_eq_raw_terminal_sites
#print axioms runLocatedBlock_eq_raw_terminal
#print axioms gasSteps_terminal_of_raw
#print axioms coreAdvancesCheck_sound
#print axioms coreAdvancesAll_sound
#print axioms fullTemplate_terminal_advances
#print axioms call16Template_terminal_advances
#print axioms inline0Template_terminal_advances
#print axioms gasSteps_fullTemplate
#print axioms runInstrSeq_append_tail
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
#print axioms call20Template_terminal_advances
#print axioms call22Template_terminal_advances
#print axioms return24Template_terminal_advances
#print axioms inline24Template_terminal_advances
#print axioms inline25Template_terminal_advances
#print axioms call26Template_terminal_advances
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
#print axioms call16GasBlock
#print axioms call20GasBlock
#print axioms call22GasBlock
#print axioms call26GasBlock
#print axioms call28GasBlock
#print axioms wholeCoreGasChain
#print axioms gasSteps_wholeCore
#print axioms gasSteps_wholeCore_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
