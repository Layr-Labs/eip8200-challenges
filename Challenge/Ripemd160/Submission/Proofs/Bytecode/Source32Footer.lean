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

def guardPath : List (DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [ ⟨3671, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 116, wfOp (by decide) trivial rfl⟩,
    ⟨3672, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by exact GuardInstructionWindow.get 117, by decide⟩,
    ⟨3673, .op .EQ, by exact GuardInstructionWindow.get 118, wfOp (by decide) trivial rfl⟩,
    ⟨3674, .push ⟨2, by decide⟩ (UInt256.ofNat 4700), by exact GuardInstructionWindow.get 119, by decide⟩,
    ⟨3675, .op .JUMPI, by exact GuardInstructionWindow.get 120, wfOp (by decide) trivial rfl⟩ ]

def constructorPath : List (DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [ ⟨3659, .op .JUMPDEST, by exact GuardInstructionWindow.get 104, wfOp (by decide) trivial rfl⟩,
    ⟨3660, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by exact GuardInstructionWindow.get 105, by decide⟩,
    ⟨3661, .push ⟨2, by decide⟩ (UInt256.ofNat 1177), by exact GuardInstructionWindow.get 106, by decide⟩,
    ⟨3662, .op .MSTORE8, by exact GuardInstructionWindow.get 107, wfOp (by decide) trivial rfl⟩,
    ⟨3663, .push ⟨2, by decide⟩ (UInt256.ofNat 389), by exact GuardInstructionWindow.get 108, by decide⟩,
    ⟨3664, .op .JUMP, by exact GuardInstructionWindow.get 109, wfOp (by decide) trivial rfl⟩ ]

@[simp] private theorem pc3662 : Artifact.submissionArtifact.instructionPC 3659 = 4700 :=
  (GuardInstructionWindow.pc 104).trans (by rfl)
@[simp] private theorem pc3663 : Artifact.submissionArtifact.instructionPC 3660 = 4701 :=
  (GuardInstructionWindow.pc 105).trans (by rfl)
@[simp] private theorem pc3664 : Artifact.submissionArtifact.instructionPC 3661 = 4703 :=
  (GuardInstructionWindow.pc 106).trans (by rfl)
@[simp] private theorem pc3665 : Artifact.submissionArtifact.instructionPC 3662 = 4706 :=
  (GuardInstructionWindow.pc 107).trans (by rfl)
@[simp] private theorem pc3666 : Artifact.submissionArtifact.instructionPC 3663 = 4707 :=
  (GuardInstructionWindow.pc 108).trans (by rfl)
@[simp] private theorem pc3667 : Artifact.submissionArtifact.instructionPC 3664 = 4710 :=
  (GuardInstructionWindow.pc 109).trans (by rfl)
@[simp] private theorem pc3674 : Artifact.submissionArtifact.instructionPC 3671 = 4720 :=
  (GuardInstructionWindow.pc 116).trans (by rfl)
@[simp] private theorem pc3675 : Artifact.submissionArtifact.instructionPC 3672 = 4721 :=
  (GuardInstructionWindow.pc 117).trans (by rfl)
@[simp] private theorem pc3676 : Artifact.submissionArtifact.instructionPC 3673 = 4723 :=
  (GuardInstructionWindow.pc 118).trans (by rfl)
@[simp] private theorem pc3677 : Artifact.submissionArtifact.instructionPC 3674 = 4724 :=
  (GuardInstructionWindow.pc 119).trans (by rfl)
@[simp] private theorem pc3678 : Artifact.submissionArtifact.instructionPC 3675 = 4727 :=
  (GuardInstructionWindow.pc 120).trans (by rfl)

private theorem valid_constructor (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 4700 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3659 (by rfl)
  rw [pc3662] at h
  rw [hcode]
  exact h

private theorem valid_initial (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 389 = true := by
  rw [hcode]
  exact Artifact.validJumpDest_initialize

theorem run_guard_miss (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ 32) :
    DataStepper.runLocatedBlock guardPath
      {s with pc := UInt256.ofNat 4720, stack := rho} =
      some {s with pc := UInt256.ofNat 4728, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat s.executionEnv.calldata.size) = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
    norm_num only
    rw [if_neg hmiss.symm]
  simp (discharger := omega) [guardPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, hrun, hbase, hcap, heq,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, UInt256.isTrue, Word.succ_ofNat_mod, Word.word_toNat_ofNat, Word.ofNat_add_mod]

theorem run_guard_hit (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : s.executionEnv.calldata.size = 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    DataStepper.runLocatedBlock guardPath
      {s with pc := UInt256.ofNat 4720, stack := rho} =
      some {s with pc := UInt256.ofNat 4700, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hv := valid_constructor s hcode
  simp (discharger := omega) [guardPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, hrun, hbase, hcap, hhit, UInt256.eq, hv,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, UInt256.isTrue, Word.succ_ofNat_mod, Word.word_toNat_ofNat, Word.ofNat_add_mod]

theorem run_constructor (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    DataStepper.runLocatedBlock constructorPath
      {s with pc := UInt256.ofNat 4700, stack := rho} =
      some {s with
        pc := UInt256.ofNat 389
        stack := rho
        memory := MachineState.writeBytes s.memory (ByteArray.mk #[1]) 1177
        activeWords := s.activeWordsAfterUInt256 1177 1} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hv := valid_initial s hcode
  simp (discharger := omega) [constructorPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, hrun, hbase, hcap, hv, State.activeWordsAfterUInt256,
    List.length_cons, Nat.add_assoc, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.word_toNat_ofNat, Word.ofNat_add_mod]

/-- Writing a zero just beyond the existing memory is redundant when the next
write fills the following byte. This includes exact ByteArray length. -/
theorem omit_zero (memory : ByteArray) (hsize : memory.size ≤ 1176) :
    MachineState.writeBytes (MachineState.writeBytes memory (ByteArray.mk #[0]) 1176)
        (ByteArray.mk #[1]) 1177 =
      MachineState.writeBytes memory (ByteArray.mk #[1]) 1177 := by
  have h0 : (ByteArray.mk #[0]).size = 1 := rfl
  have h1 : (ByteArray.mk #[1]).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, h0, h1, if_neg (by decide : (1 : Nat) ≠ 0)]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [MachineState.writeBytes_getElem?_getD, h0, h1]
    by_cases hlast : 1177 ≤ i ∧ i < 1177 + 1
    · simp only [if_pos hlast]
    · simp only [if_neg hlast]
      by_cases hzero : 1176 ≤ i ∧ i < 1176 + 1
      · have hi : i = 1176 := by omega
        subst i
        rw [if_pos (by omega)]
        rw [Memory.getElem?_getD_eq_zero_of_size_le memory 1176 hsize]
        rfl
      · simp only [if_neg hzero]


def gasSteps_guard_miss (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hmiss : s.executionEnv.calldata.size ≠ 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4720, stack := rho}
      {s with pc := UInt256.ofNat 4728, stack := rho} :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    hcode hfork (run_guard_miss s rho hstack hrun hfit hmiss) hrun hnp

def gasSteps_guard_hit (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hhit : s.executionEnv.calldata.size = 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4720, stack := rho}
      {s with pc := UInt256.ofNat 4700, stack := rho} :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    hcode hfork (run_guard_hit s rho hstack hrun hhit hcode) hrun hnp

def gasSteps_constructor (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4700, stack := rho}
      {s with
        pc := UInt256.ofNat 389
        stack := rho
        memory := MachineState.writeBytes s.memory (ByteArray.mk #[1]) 1177
        activeWords := s.activeWordsAfterUInt256 1177 1} :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka constructorPath
    hcode hfork (run_constructor s rho hstack hrun hcode) hrun hnp

#print axioms gasSteps_guard_miss
#print axioms gasSteps_guard_hit
#print axioms gasSteps_constructor
#print axioms omit_zero
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Footer
