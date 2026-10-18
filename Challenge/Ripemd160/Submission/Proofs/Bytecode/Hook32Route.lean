import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Route

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
open StackRoundTrace

private theorem toNat_one : (1 : UInt256).toNat = 1 := by
  rw [Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

private theorem toNat_zero : (0 : UInt256).toNat = 0 := by
  rw [Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

/-- Size-32 taken jump now lands on the appended recognizer, not PC 497. -/
theorem run_enter (s : State)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq guard.template (atState s 160 ((1 : UInt256) :: stk)) =
      some (atState s 9667 stk) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 9667 = true :=
    valid_9667 s hcode
  have hc : ∀ n, n ≤ 3 → stk.length + n < 1024 := by
    intro n hn
    omega
  have hcap : ((1 : UInt256) :: stk).length < 1024 := by
    simp [List.length_cons]
    omega
  simp (config := { maxSteps := 100000 }) (discharger := omega)
    [guard.template, atState, runInstrSeq, DataStepper.runInstr, hrun, hc, hcap,
      if_pos hcap, toNat_one, List.length_cons, Nat.add_assoc, UInt256.isTrue, hv,
      isTrue_one]

def cmp0 : List Instr := [
  .op .JUMPDEST,
  .push ⟨32, by decide⟩ word0,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .CALLDATALOAD,
  .op .EQ,
  .push ⟨2, by decide⟩ (UInt256.ofNat 9792),
  .op .JUMPI]

/-- First literal misses: fall through to the second compare. -/
theorem run_cmp0 (s : State)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word0)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp0 (atState s 9667 stk) = some (atState s 9708 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word0 = 0 :=
    eq_zero_of_ne hmiss
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have hfalse : ¬ (UInt256.ofNat 0).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact not_isTrue_zero
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp0, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_neg hfalse, toNat_zero, hzero,
      not_isTrue_zero, List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def cmp1 : List Instr := [
  .push ⟨32, by decide⟩ word1,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .CALLDATALOAD,
  .op .EQ,
  .push ⟨2, by decide⟩ (UInt256.ofNat 9820),
  .op .JUMPI]

/-- Second literal misses: fall through to the third compare. -/
theorem run_cmp1 (s : State)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word1)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp1 (atState s 9708 stk) = some (atState s 9748 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word1 = 0 :=
    eq_zero_of_ne hmiss
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have hfalse : ¬ (UInt256.ofNat 0).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact not_isTrue_zero
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp1, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_neg hfalse, toNat_zero, hzero,
      not_isTrue_zero, List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def cmp2 : List Instr := [
  .push ⟨32, by decide⟩ word2,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .CALLDATALOAD,
  .op .EQ,
  .push ⟨2, by decide⟩ (UInt256.ofNat 9848),
  .op .JUMPI]

/-- Third literal misses: fall through to the jump back to PC 497. -/
theorem run_cmp2 (s : State)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word2)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp2 (atState s 9748 stk) = some (atState s 9788 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word2 = 0 :=
    eq_zero_of_ne hmiss
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have hfalse : ¬ (UInt256.ofNat 0).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact not_isTrue_zero
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp2, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_neg hfalse, toNat_zero, hzero,
      not_isTrue_zero, List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def missJump : List Instr := [
  .push ⟨2, by decide⟩ (UInt256.ofNat 497),
  .op .JUMP]

/-- All three literals missed: jump back to the original size-32 body at PC 497. -/
theorem run_miss_jump (s : State)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    runInstrSeq missJump (atState s 9788 stk) = some (atState s 497 stk) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 497 = true :=
    valid_497 s hcode
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have hto : (UInt256.ofNat 497).toNat = 497 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  simp (config := { maxSteps := 100000 }) (discharger := omega)
    [missJump, atState, runInstrSeq, DataStepper.runInstr, hrun, h0, h1,
      if_pos h0, if_pos h1, hv, hto, List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod]

def gas_enter (s : State) (e : Env s) (stk : List UInt256)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 160 ((1 : UInt256) :: stk)) (atState s 9667 stk) :=
  guard.lift s (atState s 9667 stk) e ((1 : UInt256) :: stk)
    (run_enter s e.code e.run stk hlen)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Route
