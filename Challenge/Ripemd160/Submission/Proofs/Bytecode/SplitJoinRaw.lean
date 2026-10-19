import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SplitJoinRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerPersistentLoopRaw
private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl
private theorem add64 (x : UInt256) : UInt256.ofNat 64 + x = x + UInt256.ofNat 64 := Word.word_add_comm _ _
def template : List Instr :=
 [.op .JUMPDEST, .op (.Swap ⟨12, by decide⟩), .op .POP,
  .op (.Swap ⟨10, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .ADD,
  .op (.Swap ⟨10, by decide⟩), .push ⟨2, by decide⟩ (UInt256.ofNat 461), .op .JUMP]
theorem run_template (s : State) (pc : UInt256) (h : Compression.HashState)
    (off cont x : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true) :
    runInstrSeq template {s with pc := pc, stack := x :: StaggerPersistentFrame.frame h off cont rho} =
      some {s with
        pc := UInt256.ofNat 461
        stack := StaggerPersistentFrame.frame h (nextOffset off) x rho} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 461 = true := by simpa only [show (UInt256.ofNat 461).toNat = 461 by decide] using hvalid
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, StaggerPersistentFrame.frame, nextOffset,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    add_eq_hAdd, add64, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv]
theorem bytes_exact : PcEncoding.assembleBytes template = [91,156,80,154,96,64,1,154,97,1,205,86] := by decide
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SplitJoinRaw
