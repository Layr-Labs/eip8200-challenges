import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawDispatch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace
def dispatchTemplate : List Instr := [.op (.Swap ⟨12, by decide⟩), .op .JUMP]

theorem run_dispatch (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont junk : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true) :
    runInstrSeq dispatchTemplate {s with pc := pc, stack := junk :: StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := cont
        stack := StaggerPersistentFrame.frame h off junk rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [dispatchTemplate, StaggerPersistentFrame.frame,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hvalid]


#print axioms run_dispatch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawDispatch
