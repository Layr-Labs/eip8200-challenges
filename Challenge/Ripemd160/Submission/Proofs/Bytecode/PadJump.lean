import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

def template (dest : Nat) : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMP]

theorem run_template (s : State) (pc : UInt256) (rho : List UInt256) (dest : Nat)
    (hstack : rho.length ≤ 1021) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (template dest) {s with pc := pc, stack := rho} =
      some {s with pc := UInt256.ofNat dest, stack := UInt256.ofNat 4294967295 :: rho} := by
  have hcap : rho.length < 1024 := by omega
  have hcap1 : rho.length + 1 < 1024 := by omega
  have hcap2 : rho.length + 2 < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [template, runInstrSeq, Stepper.runInstr, hrun,
    hcap, hcap1, hcap2, hvalid, List.length_cons]

theorem run_merge (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1024) (hrun : s.halt = .Running) :
    runInstrSeq [.op .JUMPDEST] {s with pc := pc, stack := rho} =
      some {s with pc := pc + UInt256.ofNat 1, stack := rho} := by
  simp [runInstrSeq, Stepper.runInstr, hrun, hstack, UInt256.succ]
  rfl
#print axioms run_template
#print axioms run_merge
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
