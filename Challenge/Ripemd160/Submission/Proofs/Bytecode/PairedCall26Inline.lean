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


theorem inline27Template_terminal_advances :
    ∀ instruction ∈ inline27Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide

#print axioms inline27Template_terminal_advances

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCall26Inline
