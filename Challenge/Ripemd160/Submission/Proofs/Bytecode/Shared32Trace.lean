import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Trace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch Shared32Sites

def gasSteps_guard (s : State) (e : Env s) (F : List UInt256)
    (hstack : F.length ≤ 900) (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps (atState s 4750 F) (atState s 325 F) := by
  apply guard.lift s (atState s 325 F) e F
  have h0 : F.length < 1024 := by omega
  have h1 : F.length + 1 < 1024 := by omega
  have h2 : F.length + 2 < 1024 := by omega
  have hv := valid_special s e
  simp [guard.template, atState, runInstrSeq, DataStepper.runInstr, e.run,
    h0, h1, h2, h32, UInt256.eq, UInt256.isTrue, hv]

def gasSteps_sparse (s : State) (e : Env s)
    (ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hactive : s.activeWords = UInt256.ofNat 34)
    (hbyte : UInt8.ofNat (a4.toNat % 256) = 1) :
    GasSteps
      (atState s 325 (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho))
      (atState {s with memory := sparseMemory s.memory} 544
        (stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho)) := by
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  let sM : State := {s with memory := sparseMemory s.memory}
  have eM : Env sM := ⟨e.code, e.fork, e.run, e.np⟩
  have g0 : GasSteps (atState s 325 F) (atState s 326 F) := by
    apply special.lift s (atState s 326 F) e F
    simpa only [special.template, atState, show UInt256.ofNat 325 + UInt256.ofNat 1 = UInt256.ofNat 326 by decide] using
      PadJump.run_merge s (UInt256.ofNat 325) F (by omega) e.run
  have g1 : GasSteps (atState s 326 F) (atState s 328 (UInt256.ofNat 128 :: F)) := by
    apply marker.lift s (atState s 328 (UInt256.ofNat 128 :: F)) e F
    have hcap : F.length < 1024 := by omega
    simp [marker.template, atState, runInstrSeq, DataStepper.runInstr, e.run, hcap,
      UInt256.succ, Instr.size]
    decide
  have g2 : GasSteps (atState s 328 (UInt256.ofNat 128 :: F)) (atState sM 335 F) := by
    apply sparse.lift s (atState sM 335 F) e (UInt256.ofNat 128 :: F)
    have h := Shared32SparseRun.run_sparse s (UInt256.ofNat 328) ret mw a2 a3 a4
      a5 a6 a7 a8 a9 a10 lim rho hstack e.run hactive hbyte
    simpa only [sparse.template, sparse.end_pc, atState, sM, F] using h
  have g3 : GasSteps (atState sM 335 F) (atState sM 543 F) := by
    apply jump.lift sM (atState sM 543 F) eM F
    exact PadJump.run_template sM (UInt256.ofNat 335) F 543 (by omega) e.run
      (by simpa only [show (UInt256.ofNat 543).toNat = 543 by decide] using valid_lower sM eM)
  have g4 : GasSteps (atState sM 543 F) (atState sM 544 F) := by
    apply lower.lift sM (atState sM 544 F) eM F
    simpa only [lower.template, atState, show UInt256.ofNat 543 + UInt256.ofNat 1 = UInt256.ofNat 544 by decide] using
      PadJump.run_merge sM (UInt256.ofNat 543) F (by omega) e.run
  exact g0.trans (g1.trans (g2.trans (g3.trans g4)))

def gasSteps_table (s : State) (e : Env s)
    (ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880)
    (hactive : s.activeWords = UInt256.ofNat 34) :
    GasSteps
      (atState {s with memory := writeWord s.memory 162 highWord} 544
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho))
      (atState {s with memory := Shared32Table.tableMemory s.memory, activeWords := UInt256.ofNat 35} 861
        (stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho)) := by
  let s1 : State := {s with memory := writeWord s.memory 162 highWord}
  have e1 : Env s1 := ⟨e.code, e.fork, e.run, e.np⟩
  apply table.lift s1 _ e1 _
  have h := Shared32Run.run_table s (UInt256.ofNat 544) ret a2 a3 a4 a5 a6 a7
    a8 a9 a10 lim rho hstack e.run hactive
  simpa only [table.template, Shared32Run.end_pc, atState, s1] using h

#print axioms gasSteps_guard
#print axioms gasSteps_sparse
#print axioms gasSteps_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Trace
