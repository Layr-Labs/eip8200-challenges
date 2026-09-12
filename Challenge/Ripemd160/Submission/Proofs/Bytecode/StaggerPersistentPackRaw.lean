import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
structure Input where
  rd : UInt256
  k : UInt256
  rc : UInt256
  rb : UInt256
  re : UInt256
  ra : UInt256
  factor : UInt256
  lower : UInt256
  cache140 : UInt256
  cache190 : UInt256
  cache310 : UInt256
  cache350 : UInt256
  h4 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h0 : UInt256
  off : UInt256
  limit : UInt256
def template : List Instr := [
  .op (.Swap ⟨0, by decide⟩),
  .op .POP,
  .op (.Swap ⟨3, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨15, by decide⟩),
  .op .OR,
  .op (.Swap ⟨1, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨12, by decide⟩),
  .op .OR,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨13, by decide⟩),
  .op .OR,
  .op (.Swap ⟨3, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨14, by decide⟩),
  .op .OR,
  .op (.Swap ⟨2, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨11, by decide⟩),
  .op .OR,
  .op (.Dup ⟨6, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHL,
  .op (.Dup ⟨7, by decide⟩),
  .op (.Dup ⟨1, by decide⟩),
  .op .OR ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 := [x.rd, x.k, x.rc, x.rb, x.re, x.ra, x.factor, x.lower, x.cache140, x.cache190, x.cache310, x.cache350, x.h4, x.h1, x.h2, x.h3, x.h0, x.off, x.limit] ++ rho
def outputStack (x : Input) (rho : List UInt256) : List UInt256 := [(UInt256.lor x.lower (UInt256.shiftLeft x.lower (UInt256.ofNat 144))), (UInt256.shiftLeft x.lower (UInt256.ofNat 144)), (UInt256.lor x.h4 (UInt256.shiftLeft x.re (UInt256.ofNat 144))), (UInt256.lor x.h1 (UInt256.shiftLeft x.rb (UInt256.ofNat 144))), (UInt256.lor x.h0 (UInt256.shiftLeft x.ra (UInt256.ofNat 144))), (UInt256.lor x.h3 (UInt256.shiftLeft x.rd (UInt256.ofNat 144))), (UInt256.lor x.h2 (UInt256.shiftLeft x.rc (UInt256.ofNat 144))), x.factor, x.lower, x.cache140, x.cache190, x.cache310, x.cache350, x.h4, x.h1, x.h2, x.h3, x.h0, x.off, x.limit] ++ rho
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, inputStack, outputStack,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, Word.lor_comm]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackRaw
