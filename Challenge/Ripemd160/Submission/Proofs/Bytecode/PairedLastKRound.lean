import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLastKRound

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist
open PairedSynthCoreTrace (fourRaw fourRaw_eq_inline4Boolean)

def lastFrame (memory : ByteArray) (q : PairedHelperBooleanTrace.Frame) : PairedHelperBooleanTrace.Frame :=
  {q with message0 := UInt256.lor (MachineState.readWord memory 560) (MachineState.readWord memory 608), leftShift0 := UInt256.ofNat 26, rightShift0 := UInt256.ofNat 21}

def lastEntry (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) : List UInt256 :=
  [q.d, q.k, q.c, q.b, q.e, q.a, q.factor, q.pair, q.upper, q.lower] ++ rho

def lastOutput (q : PairedHelperBooleanTrace.Frame) (value : UInt256) (rho : List UInt256) : List UInt256 :=
  [rawC10 q, value, q.b, q.e, q.d, q.factor, q.pair, q.upper, q.lower] ++ rho

def lastWordStack (q : PairedHelperBooleanTrace.Frame) (state : PairedLaneWordRound.WordLane) (rho : List UInt256) : List UInt256 :=
  [state.d, state.b, state.c, state.a, state.e, q.factor, q.pair, q.upper, q.lower] ++ rho

def lastTemplate : List Instr :=
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

theorem lastTemplate_length : lastTemplate.length = 46 := rfl

#print axioms lastTemplate_length

theorem run_lastTemplate_raw (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq lastTemplate {s with pc := pc, stack := lastEntry q rho} =
      some {s with pc := pcAfter pc lastTemplate, stack := lastOutput q (inlineT (lastFrame s.memory q) (fourRaw q)) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [lastTemplate, lastEntry, lastOutput,
    inlineT, inlineRotation, lastFrame, fourRaw, PairedLaneBooleanFactoring.factoredWord, inlineProduct, rawC10,
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
  let sum := UInt256.add (lastFrame s.memory q).message0 (UInt256.add (fourRaw q) q.a)
  change post (UInt256.add sum q.k) = post (UInt256.add q.k sum)
  exact congrArg post (Challenge.EvmProof.Word.word_add_comm sum q.k)

#print axioms run_lastTemplate_raw

theorem run_lastTemplate (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq lastTemplate {s with pc := pc, stack := lastEntry q rho} =
      some {s with pc := pcAfter pc lastTemplate, stack := lastOutput q (inlineT (lastFrame s.memory q) (inline4Boolean q)) rho} := by
  simpa only [fourRaw_eq_inline4Boolean] using
    run_lastTemplate_raw s pc q rho hstack hrun hactive

#print axioms run_lastTemplate

theorem run_lastTemplate_word (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfactor : q.factor = PairedLaneWordRotate.factorWord)
    (hpair : q.pair = pairWord) (hupper : q.upper = upperWord) (hlower : q.lower = lowerWord) :
    runInstrSeq lastTemplate {s with pc := pc, stack := lastEntry q rho} =
      some {s with pc := pcAfter pc lastTemplate, stack := lastWordStack q (PairedLaneWordRound.wordStep 4 6 11 (lastFrame s.memory q).message0 q.k (frameLane q)) rho} := by
  have ht : inlineT (lastFrame s.memory q) (inline4Boolean q) =
      PairedLaneWordRound.wordT 4 6 11 q.a q.b q.c q.d q.e
        (lastFrame s.memory q).message0 q.k :=
    (inlineT_eq_rawT _ _).trans
      ((congrArg (rawT (lastFrame s.memory q)) (inline4Boolean_eq q hlower)).trans
        (rawT_of_boolean (lastFrame s.memory q) 4 6 11 hfactor hpair hupper rfl rfl))
  have hout : lastOutput q (inlineT (lastFrame s.memory q) (inline4Boolean q)) rho =
      lastWordStack q
        (PairedLaneWordRound.wordStep 4 6 11 (lastFrame s.memory q).message0 q.k (frameLane q)) rho := by
    simp only [lastOutput, lastWordStack, PairedLaneWordRound.wordStep, frameLane,
      ht, rawC10_eq q hfactor hpair]
  exact (run_lastTemplate s pc q rho hstack hrun hactive).trans
    (congrArg (fun vs => some {s with pc := pcAfter pc lastTemplate, stack := vs}) hout)

#print axioms run_lastTemplate_word

theorem lastTemplate_bytes : (lastTemplate.map Instr.size).sum = 53 := rfl

#print axioms lastTemplate_bytes

theorem lastEntry_eq (q : PairedHelperBooleanTrace.Frame) (rho : List UInt256) :
    lastEntry q rho = PairedAllInlineCoreTrace.inline79Entry q rho := rfl

#print axioms lastEntry_eq

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLastKRound

