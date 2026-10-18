import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Gas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Route
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Hit

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Route
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open YulEvmCompiler

private theorem toNat_one : (1 : UInt256).toNat = 1 := by
  rw [Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

private theorem toNat_zero : (0 : UInt256).toNat = 0 := by
  rw [Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

private theorem toNat_dest (n : Nat) (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Word 0 matches: the inverted compare takes the return stub at PC 9792. -/
theorem run_cmp0_hit (s : State)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word0)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp0 (atState s 9667 stk) = some (atState s 9792 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word0 = 1 :=
    eq_one_of_eq hhit
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have htrue : (UInt256.ofNat 1).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact isTrue_one
  have hv : Decode.isValidJumpDest s.executionEnv.code 9792 = true := valid_9792 s hcode
  have hto : (UInt256.ofNat 9792).toNat = 9792 := toNat_dest 9792 (by decide)
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp0, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_pos htrue, hv, hto, toNat_one, toNat_zero, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

/-- Word 1 matches: the inverted compare takes the return stub at PC 9820. -/
theorem run_cmp1_hit (s : State)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word1)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp1 (atState s 9708 stk) = some (atState s 9820 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word1 = 1 :=
    eq_one_of_eq hhit
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have htrue : (UInt256.ofNat 1).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact isTrue_one
  have hv : Decode.isValidJumpDest s.executionEnv.code 9820 = true := valid_9820 s hcode
  have hto : (UInt256.ofNat 9820).toNat = 9820 := toNat_dest 9820 (by decide)
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp1, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_pos htrue, hv, hto, toNat_one, toNat_zero, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

/-- Word 2 matches: the inverted compare takes the return stub at PC 9848. -/
theorem run_cmp2_hit (s : State)
    (hcode : s.executionEnv.code = submissionArtifact.code)
    (hrun : s.halt = .Running)
    (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word2)
    (hlen : stk.length + 3 < 1024) :
    runInstrSeq cmp2 (atState s 9748 stk) = some (atState s 9848 stk) := by
  have heq : UInt256.eq (MachineState.readWord s.executionEnv.calldata 0) word2 = 1 :=
    eq_one_of_eq hhit
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  have htrue : (UInt256.ofNat 1).isTrue := by
    rw [← Challenge.EvmProof.Word.literal_eq_ofNat]
    exact isTrue_one
  have hv : Decode.isValidJumpDest s.executionEnv.code 9848 = true := valid_9848 s hcode
  have hto : (UInt256.ofNat 9848).toNat = 9848 := toNat_dest 9848 (by decide)
  simp (config := { maxSteps := 200000 }) (discharger := omega)
    [cmp2, atState, runInstrSeq, DataStepper.runInstr, hrun, heq, h0, h1, h2,
      if_pos h0, if_pos h1, if_pos h2, if_pos htrue, hv, hto, toNat_one, toNat_zero, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gas_cmp0_hit (s : State) (e : Env s) (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word0)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9667 stk) (atState s 9792 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp0Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp0Sites cmp0 cmp0_inst
      cmp0_contig (atState s 9667 stk)
      (by simp [headPC, cmp0Sites, s5422, siteOf, atState]) cmp0_advances
    rw [hblock]
    exact run_cmp0_hit s e.code e.run stk hhit hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_cmp1_hit (s : State) (e : Env s) (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word1)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9708 stk) (atState s 9820 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp1Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp1Sites cmp1 cmp1_inst
      cmp1_contig (atState s 9708 stk)
      (by simp [headPC, cmp1Sites, s5429, siteOf, atState]) cmp1_advances
    rw [hblock]
    exact run_cmp1_hit s e.code e.run stk hhit hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_cmp2_hit (s : State) (e : Env s) (stk : List UInt256)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = word2)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9748 stk) (atState s 9848 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp2Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp2Sites cmp2 cmp2_inst
      cmp2_contig (atState s 9748 stk)
      (by simp [headPC, cmp2Sites, s5435, siteOf, atState]) cmp2_advances
    rw [hblock]
    exact run_cmp2_hit s e.code e.run stk hhit hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Hit
