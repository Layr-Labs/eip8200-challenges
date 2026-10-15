import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Trace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch Shared32Sites

/-- The 32-byte block, entered from the alignment guard at 143: the continuation slot becomes the
output entry 4736, the sentinel `0x80` and the length byte (the low byte of the resident
coefficient word in slot 4) are stored, then the 32-byte test at 158 joins the lower half at 497. -/
def gasSteps_sparse (s : State) (e : Env s)
    (ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hactive : s.activeWords = UInt256.ofNat 34)
    (hone : UInt8.ofNat (a4.toNat % 256) = 1)
    (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps
      (atState s 143 (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho))
      (atState {s with memory := sparseMemory s.memory} 498
        (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 4729) rho)) := by
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho
  let F0 := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 4729) rho
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have hF0 : F0.length ≤ 900 := by simp only [F0, stk, List.length_cons]; omega
  let sM : State := {s with memory := sparseMemory s.memory}
  have eM : Env sM := ⟨e.code, e.fork, e.run, e.np⟩
  let v := UInt256.ofNat 128
  have hbyte : UInt8.ofNat (v.toNat % 256) = 128 := by decide
  have g0 : GasSteps (atState s 143 F) (atState s 144 F) := by
    apply special.lift s (atState s 144 F) e F
    simpa only [special.template, atState, show UInt256.ofNat 143 + UInt256.ofNat 1 = UInt256.ofNat 144 by decide] using
      PadJump.run_merge s (UInt256.ofNat 143) F (by omega) e.run
  have g1 : GasSteps (atState s 144 F) (atState s 149 F0) := by
    apply head.lift s (atState s 149 F0) e F
    have h := Shared32SparseRun.run_head s (UInt256.ofNat 144) ret mw a2 a3 a4
      a5 a6 a7 a8 a9 a10 lim rho hstack e.run
    simpa only [head.template, head.end_pc, atState, F, F0] using h
  have g2 : GasSteps (atState s 149 F0) (atState s 151 (v :: F0)) := by
    apply fold.lift s (atState s 151 (v :: F0)) e F0
    have h := Shared32SparseRun.run_fold s (UInt256.ofNat 149) F0 hF0 e.run
    simpa only [fold.template, fold.end_pc, atState] using h
  have g4 : GasSteps (atState s 151 (v :: F0)) (atState sM 158 F0) := by
    apply sparse.lift s (atState sM 158 F0) e (v :: F0)
    have h := Shared32SparseRun.run_sparse s (UInt256.ofNat 151) v ret mw a2 a3 a4
      (a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: UInt256.ofNat 1056 :: UInt256.ofNat 4729 ::
        DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)
      (by simp only [List.length_cons]; omega) e.run hactive hbyte hone
    simpa only [sparse.template, sparse.end_pc, atState, sM, F0, stk] using h
  have g5 : GasSteps (atState sM 158 F0) (atState sM 497 F0) := by
    apply guard.lift sM (atState sM 497 F0) eM F0
    have h0 : F0.length < 1024 := by omega
    have h1 : F0.length + 1 < 1024 := by omega
    have h2 : F0.length + 2 < 1024 := by omega
    have hv := valid_lower sM eM
    have h32M : sM.executionEnv.calldata.size = 32 := h32
    simp [guard.template, atState, runInstrSeq, DataStepper.runInstr, eM.run,
      h0, h1, h2, h32M, UInt256.eq, UInt256.isTrue, hv]
  have g6 : GasSteps (atState sM 497 F0) (atState sM 498 F0) := by
    apply lower.lift sM (atState sM 498 F0) eM F0
    simpa only [lower.template, atState, show UInt256.ofNat 497 + UInt256.ofNat 1 = UInt256.ofNat 498 by decide] using
      PadJump.run_merge sM (UInt256.ofNat 497) F0 (by omega) e.run
  exact g0.trans (g1.trans (g2.trans (g4.trans (g5.trans g6))))

def gasSteps_table (s : State) (e : Env s)
    (ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    GasSteps
      (atState {s with memory := writeWord s.memory 162 highWord} 498
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho))
      (atState {s with memory := Shared32Table.tableMemory s.memory, activeWords := UInt256.ofNat 35} 824
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho)) := by
  let s1 : State := {s with memory := writeWord s.memory 162 highWord}
  have e1 : Env s1 := ⟨e.code, e.fork, e.run, e.np⟩
  apply table.lift s1 _ e1 _
  have h := Shared32Run.run_table s (UInt256.ofNat 498) ret a2 a3 a4 a5 a6 a7
    a8 a9 a10 lim rho hstack e.run hactive rfl
  simpa only [table.template, Shared32Run.end_pc, atState, s1] using h

#print axioms gasSteps_sparse
#print axioms gasSteps_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Trace
