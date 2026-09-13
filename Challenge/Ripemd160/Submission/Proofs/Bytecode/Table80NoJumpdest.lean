import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Schedule
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate

theorem run_without_jumpdest (code : List Instr) (s t : State)
    (hne : code ≠ []) (hstack : s.stack.length < 1024) (hrun : s.halt = .Running)
    (h : runInstrSeq (.op .JUMPDEST :: code) s = some t) :
    runInstrSeq code {s with pc := s.pc.succ} = some t := by
  cases code with
  | nil => exact False.elim (hne rfl)
  | cons instruction rest =>
    simpa only [runInstrSeq, Stepper.runInstr, hstack, if_pos, hrun] using h
#print axioms run_without_jumpdest
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
