import Challenge.Ripemd160.Submission.Proofs.Bytecode.GuardInstructionWindow
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Footer
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    DataStepper.WellFormed .Osaka (.op op) := ⟨hopcode, hplain, havailable⟩

/-- The exact-size test that used to divert a thirty-two byte call to a
constant footer store is retired.  Its five slots are now a stack-neutral
filler: three jump destinations, one wide zero push and its pop.  The window
keeps the footer-loop setup at its frozen offset while costing eight gas
instead of a calldata load, a comparison and a branch. -/
def guardPath : List (DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [ ⟨3672, .op .JUMPDEST, by exact GuardInstructionWindow.get 116, wfOp (by decide) trivial rfl⟩,
    ⟨3673, .op .JUMPDEST, by exact GuardInstructionWindow.get 117, wfOp (by decide) trivial rfl⟩,
    ⟨3674, .op .JUMPDEST, by exact GuardInstructionWindow.get 118, wfOp (by decide) trivial rfl⟩,
    ⟨3675, .push ⟨3, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 119, by decide⟩,
    ⟨3676, .op .POP, by exact GuardInstructionWindow.get 120, wfOp (by decide) trivial rfl⟩ ]

@[simp] private theorem pc3674 : Artifact.submissionArtifact.instructionPC 3672 = 4720 :=
  (GuardInstructionWindow.pc 116).trans (by rfl)
@[simp] private theorem pc3675 : Artifact.submissionArtifact.instructionPC 3673 = 4721 :=
  (GuardInstructionWindow.pc 117).trans (by rfl)
@[simp] private theorem pc3676 : Artifact.submissionArtifact.instructionPC 3674 = 4722 :=
  (GuardInstructionWindow.pc 118).trans (by rfl)
@[simp] private theorem pc3677 : Artifact.submissionArtifact.instructionPC 3675 = 4723 :=
  (GuardInstructionWindow.pc 119).trans (by rfl)
@[simp] private theorem pc3678 : Artifact.submissionArtifact.instructionPC 3676 = 4727 :=
  (GuardInstructionWindow.pc 120).trans (by rfl)

theorem run_guard_window (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock guardPath
      {s with pc := UInt256.ofNat 4720, stack := rho} =
      some {s with pc := UInt256.ofNat 4728, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [guardPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, hrun, hbase, hcap,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
    Word.word_toNat_ofNat, Word.ofNat_add_mod]

def gasSteps_guard_window (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4720, stack := rho}
      {s with pc := UInt256.ofNat 4728, stack := rho} :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    hcode hfork (run_guard_window s rho hstack hrun) hrun hnp

#print axioms gasSteps_guard_window
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Footer
