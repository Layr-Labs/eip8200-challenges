import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Codecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Sites

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Trace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory HoistedInherited.Pair13Endian
open HoistedInherited.Shared32Scratch HoistedInherited.Shared32Sites

/-- The 32-byte block, entered from the alignment guard at 143: the continuation slot becomes the
output entry 9667, the sentinel `0x80` and the length byte (the low byte of the resident
coefficient word in slot 4) are stored, then the flag is consumed at160 and joins the lower half at497. -/
def gasSteps_sparse (s : State) (e : Env s)
    (ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hmemsize : 194 ≤ s.memory.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → s.memory[a]?.getD 0 = 0)
    (hactive : s.activeWords = UInt256.ofNat 34)
    (_hone : UInt8.ofNat (a4.toNat % 256) = 1)
    (_h32 : s.executionEnv.calldata.size = 32) (hlim : lim = UInt256.ofNat 32) :
    GasSteps
      (atState s 143 (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho))
      (atState {s with memory := sparseMemory s.memory} 498
        (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 9667) rho)) := by
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho
  let F0 := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 9667) rho
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have hF0 : F0.length ≤ 900 := by simp only [F0, stk, List.length_cons]; omega
  let sM : State := {s with memory := sparseMemory s.memory}
  have eM : Env sM := ⟨e.code, e.fork, e.run, e.np⟩
  have g0 : GasSteps (atState s 143 F) (atState s 144 F) := by
    apply special.lift s (atState s 144 F) e F
    simpa only [special.template, atState, show UInt256.ofNat 143 + UInt256.ofNat 1 = UInt256.ofNat 144 by decide] using
      PadJump.run_merge s (UInt256.ofNat 143) F (by omega) e.run
  have g1 : GasSteps (atState s 144 F) (atState s 151 (UInt256.ofNat 1 :: F0)) := by
    apply head.lift s (atState s 151 (UInt256.ofNat 1 :: F0)) e F
    have h := HoistedInherited.Shared32SparseRun.run_head s (UInt256.ofNat 144) ret mw a2 a3 a4
      a5 a6 a7 a8 a9 a10 lim rho hstack e.run
    simpa only [head.template, head.end_pc, atState, F, F0, hlim, show UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat 32) = UInt256.ofNat 1 from rfl] using h
  have g2 : GasSteps (atState s 151 (UInt256.ofNat 1 :: F0)) (atState sM 497 F0) := by
    apply combined.lift s (atState sM 497 F0) e (UInt256.ofNat 1 :: F0)
    have hh := HoistedInherited.Shared32SparseRun.run_combined_hit s F0 hF0 e.run (by rw [hactive]; decide)
      (valid_lower s e)
    have hm : HoistedInherited.Shared32SparseRun.copied s.memory s.executionEnv.code = sparseMemory s.memory := by
      rw [e.code]
      exact HoistedInherited.Shared32Codecopy.copied_sparse s.memory hmemsize hzero
    simpa only [combined.template, atState, sM, hm] using hh
  have g6 : GasSteps (atState sM 497 F0) (atState sM 498 F0) := by
    apply lower.lift sM (atState sM 498 F0) eM F0
    simpa only [lower.template, atState, show UInt256.ofNat 497 + UInt256.ofNat 1 = UInt256.ofNat 498 by decide] using
      PadJump.run_merge sM (UInt256.ofNat 497) F0 (by omega) e.run
  exact g0.trans (g1.trans (g2.trans g6))

def gasSteps_table (s : State) (e : Env s)
    (ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    GasSteps
      (atState {s with memory := writeWord s.memory 162 highWord} 498
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho))
      (atState {s with memory := HoistedInherited.Shared32Table.tableMemory s.memory, activeWords := UInt256.ofNat 35} 824
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho)) := by
  let s1 : State := {s with memory := writeWord s.memory 162 highWord}
  have e1 : Env s1 := ⟨e.code, e.fork, e.run, e.np⟩
  apply table.lift s1 _ e1 _
  have h := HoistedInherited.Shared32Run.run_table s (UInt256.ofNat 498) ret a2 a3 a4 a5 a6 a7
    a8 a9 a10 lim rho hstack e.run hactive rfl
  simpa only [table.template, HoistedInherited.Shared32Run.end_pc, atState, s1] using h

#print axioms gasSteps_sparse
#print axioms gasSteps_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Trace
