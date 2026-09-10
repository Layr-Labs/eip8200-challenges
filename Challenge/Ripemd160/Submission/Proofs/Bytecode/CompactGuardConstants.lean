import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactGuardConstants

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PatternedSwar StackRoundTrace

theorem repeated_one : UInt256.lnot (0 : UInt256) / (255 : UInt256) = M := by decide
theorem repeated_high : UInt256.shiftLeft M (7 : UInt256) = m8 := by decide
theorem repeated_low : UInt256.lnot m8 = m7 := by decide
theorem repeated_one_ofNat : UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 255 = M := by decide
theorem repeated_high_ofNat : UInt256.shiftLeft M (UInt256.ofNat 7) = m8 := by decide

def code : List Instr :=
  [.push 1 255, .push 0 0, .op .NOT, .op .DIV, .push 32 P,
   .op (.Dup ⟨1, by decide⟩), .push 1 7, .op .SHL, .op (.Dup ⟨0, by decide⟩), .op .NOT,
   .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨2, by decide⟩)]

set_option linter.unusedSimpArgs false in
theorem run_constants (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1019) (hrun : s.halt = .Running) :
    runInstrSeq code {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc code, stack := M :: m7 :: P :: m8 :: rho} := by
  have h0 : rho.length < 1024 := by omega
  have h1 : rho.length + 1 < 1024 := by omega
  have h2 : rho.length + 2 < 1024 := by omega
  have h3 : rho.length + 3 < 1024 := by omega
  have h4 : rho.length + 4 < 1024 := by omega
  have hzero : ({val := 0} : UInt256) = (0 : UInt256) := rfl
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  simp [code, runInstrSeq, Stepper.runInstr, hrun, h0, h1, h2, h3, h4, hzero,
    List.exchange, pcAfter, Instr.size, Instr.size_op, Instr.size_push, UInt256.succ,
    Word.literal_eq_ofNat, repeated_one, repeated_high, repeated_low,
    repeated_one_ofNat, repeated_high_ofNat, hadd]

#print axioms repeated_one
#print axioms repeated_high
#print axioms repeated_low
#print axioms run_constants

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactGuardConstants
