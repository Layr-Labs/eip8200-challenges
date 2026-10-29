import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.CycleGlobal.CsubFixed
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.Csub
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Csub

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
def subEntryState (s : State) (memory : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3508
           stack := [pdst, ret] ++ rest
           memory := memory }


-- Keep earlier limb states opaque while checking each explicit recursive step.
attribute [local irreducible] csStep

private theorem fixedOrComm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      unfold UInt256.lor
      congr 1
      apply Fin.eq_of_val_eq
      simp [Fin.lor, Nat.or_comm]

private theorem fixedSubtractZero (x : UInt256) : x - UInt256.ofNat 0 = x := by
  cases x with
  | mk x =>
    change (⟨x - 0⟩ : UInt256) = ⟨x⟩
    congr 1
    apply Fin.eq_of_val_eq
    simp

/-- Fixed-address CSUB boundary; the memory and borrow are the existing recursion. -/
def csFixedState (s : State) (memory : ByteArray) (n j pc : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := (if j = 0 then [] else [(csStep memory n j).flag]) ++ [pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

-- the eight-limb entry now falls through the dispatch instead of jumping, so it no longer needs
-- the code hypothesis; the binder stays so the call sites are unchanged
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_csFixedEntry8 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord memory 2688 = UInt256.ofNat (32 * 8)) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedEntry8
      (subEntryState s memory pdst ret rest) =
      some (csFixedState s memory 8 0 3520 pdst ret rest) := by
  have hactS := activeWords_fix s 2688 32 (by decide) (by decide) hact
  have capacity (j : Nat) (hj : j ≤ 5) : rest.length + j < 1024 := by omega
  have hword9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword256 : (256 : UInt256).toNat = 256 := by decide
  have hword4972 : (3508 : UInt256).toNat = 3508 := by decide
  have hword5022 : (3468 : UInt256).toNat = 3468 := by decide
  have hword5131 : (3605 : UInt256).toNat = 3605 := by decide
  have hword2225 : (901 : UInt256).toNat = 901 := by decide
  have hwordEq4972 : (3508 : UInt256) = UInt256.ofNat 3508 := by decide
  have hwordEq5022 : (3468 : UInt256) = UInt256.ofNat 3468 := by decide
  have hwordEq5131 : (3605 : UInt256) = UInt256.ofNat 3605 := by decide
  have hwordEq2225 : (901 : UInt256) = UInt256.ofNat 901 := by decide
  have hwordZero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedEntry8, subEntryState, csFixedState, csStep,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      hrun, hcode, hs32, hactS, capacity, Nat.add_assoc,
      UInt256.eq, UInt256.isTrue, opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword9344, hword128, hword256, hword4972, hword5022, hword5131, hword2225, hwordEq4972, hwordEq5022, hwordEq5131, hwordEq2225, hwordZero, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_0 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_0
      (csFixedState s memory 8 0 3520 pdst ret rest) =
      some (csFixedState s memory 8 1 3536 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 224 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2336 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 2016 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 1 =
      (let prev := csStep memory 8 0
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 0))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 0))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (8 - 1 - 0))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 8 0
  have hword224 : (224 : UInt256).toNat = 224 := by decide
  have hword8480 : (2336 : UInt256).toNat = 2336 := by decide
  have hword7392 : (2016 : UInt256).toNat = 2016 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_0, csFixedState, fixedOrComm, hstep, csStep, fixedSubtractZero, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword224, hword8480, hword7392, List.exchange]
  try (split <;> decide)

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_1 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_1
      (csFixedState s memory 8 1 3536 pdst ret rest) =
      some (csFixedState s memory 8 2 3557 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 192 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2304 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1984 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 2 =
      (let prev := csStep memory 8 1
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 1))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 1))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 1))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 1
  have hword192 : (192 : UInt256).toNat = 192 := by decide
  have hword8448 : (2304 : UInt256).toNat = 2304 := by decide
  have hword7360 : (1984 : UInt256).toNat = 1984 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_1, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword192, hword8448, hword7360, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_2 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_2
      (csFixedState s memory 8 2 3557 pdst ret rest) =
      some (csFixedState s memory 8 3 3578 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 160 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2272 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1952 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 3 =
      (let prev := csStep memory 8 2
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 2))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 2))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 2))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 2
  have hword160 : (160 : UInt256).toNat = 160 := by decide
  have hword8416 : (2272 : UInt256).toNat = 2272 := by decide
  have hword7328 : (1952 : UInt256).toNat = 1952 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_2, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword160, hword8416, hword7328, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_3 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_3
      (csFixedState s memory 8 3 3578 pdst ret rest) =
      some (csFixedState s memory 8 4 3599 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 128 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2240 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1920 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 4 =
      (let prev := csStep memory 8 3
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 3))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 3))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 3))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 3
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword8384 : (2240 : UInt256).toNat = 2240 := by decide
  have hword7296 : (1920 : UInt256).toNat = 1920 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_3, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword128, hword8384, hword7296, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_4
      (csFixedState s memory 8 4 3599 pdst ret rest) =
      some (csFixedState s memory 8 5 3620 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 96 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2208 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1888 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 5 =
      (let prev := csStep memory 8 4
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 4))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 4))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 4))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 4
  have hword96 : (96 : UInt256).toNat = 96 := by decide
  have hword8352 : (2208 : UInt256).toNat = 2208 := by decide
  have hword7264 : (1888 : UInt256).toNat = 1888 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_4, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword96, hword8352, hword7264, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_5 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_5
      (csFixedState s memory 8 5 3620 pdst ret rest) =
      some (csFixedState s memory 8 6 3642 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 64 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2176 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1856 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 6 =
      (let prev := csStep memory 8 5
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 5))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 5))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 5))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 5
  have hword64 : (64 : UInt256).toNat = 64 := by decide
  have hword8320 : (2176 : UInt256).toNat = 2176 := by decide
  have hword7232 : (1856 : UInt256).toNat = 1856 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_5, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword64, hword8320, hword7232, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_6 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_6
      (csFixedState s memory 8 6 3642 pdst ret rest) =
      some (csFixedState s memory 8 7 3663 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 32 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2144 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1824 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 7 =
      (let prev := csStep memory 8 6
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 6))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 6))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 6))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 6
  have hword32 : (32 : UInt256).toNat = 32 := by decide
  have hword8288 : (2144 : UInt256).toNat = 2144 := by decide
  have hword7200 : (1824 : UInt256).toNat = 1824 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_6, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword32, hword8288, hword7200, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep8_7 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_7
      (csFixedState s memory 8 7 3663 pdst ret rest) =
      some (csFixedState s memory 8 8 3683 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 0 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2112 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1792 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 8 =
      (let prev := csStep memory 8 7
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 7))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 7))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (8 - 1 - 7))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 8 7
  have hword0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hword8256 : (2112 : UInt256).toNat = 2112 := by decide
  have hword7168 : (1792 : UInt256).toNat = 1792 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_7, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword0, hzeroNat, hword8256, hword7168, List.exchange]

set_option linter.unusedSimpArgs false in
/-- `use ≠ 0`: the `JUMPI` takes pc 4538, which copies the difference block at `SUBB`. -/
theorem run_csFixedTailSub8 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 =
      UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (huse : (csUse memory 8 8).toNat ≠ 0)
    (hsrc : (csSrc memory 8 8).toNat = 1792) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTailSub
      (csFixedState s memory 8 8 3683 pdst ret rest) =
      some (subReturnedState s memory 8 8 pdst ret rest) := by
  have h4538 : (3717 : UInt256).toNat = 3717 := by decide
  have heq4538 : (3717 : UInt256) = UInt256.ofNat 3717 := by decide
  have h1792 : (1792 : UInt256).toNat = 1792 := by decide
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32 * 8 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 8 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 8) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 8) (by omega) (by omega) hact
  have hcondEq : UInt256.lor (MachineState.readWord (csStep memory 8 8).memory 2080)
      (UInt256.isZero (csStep memory 8 8).flag) = csUse memory 8 8 := rfl
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      1792 (32 * 8)) = s.activeWords :=
    activeWords_fix s 1792 (32 * 8) (by omega) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [h4538, heq4538, h1792, jumpDestCopyResume, csFixedTailSub, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subReturnedState, hcondEq, hsrc, UInt256.isTrue, huse,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      capacity, Nat.add_assoc, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- `use = 0`: the `JUMPI` falls through to the shared copy block at pc 4527, which copies `t`. -/
theorem run_csFixedTailKeep8 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 =
      UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (huse : (csUse memory 8 8).toNat = 0)
    (hsrc : (csSrc memory 8 8).toNat = 2112) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTailKeep
      (csFixedState s memory 8 8 3683 pdst ret rest) =
      some (subReturnedState s memory 8 8 pdst ret rest) := by
  have h4538 : (3717 : UInt256).toNat = 3717 := by decide
  have h4527 : (3706 : UInt256).toNat = 3706 := by decide
  have heq4527 : (3706 : UInt256) = UInt256.ofNat 3706 := by decide
  have h2112 : (2112 : UInt256).toNat = 2112 := by decide
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32 * 8 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 8 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 8) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 8) (by omega) (by omega) hact
  have hcondEq : UInt256.lor (MachineState.readWord (csStep memory 8 8).memory 2080)
      (UInt256.isZero (csStep memory 8 8).flag) = csUse memory 8 8 := rfl
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      2112 (32 * 8)) = s.activeWords :=
    activeWords_fix s 2112 (32 * 8) (by omega) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [h4538, h4527, heq4527, h2112, jumpDestEarlyCopy, csFixedTailKeep, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subReturnedState, hcondEq, hsrc, UInt256.isTrue, huse,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      capacity, Nat.add_assoc, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- The selection tail, split on `use`: either branch returns `subReturnedState`. -/
def gasSteps_csFixedTail8 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 =
      UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (htn : (MachineState.readWord (csStep memory 8 8).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csFixedState s memory 8 8 3683 pdst ret rest)
      (subReturnedState s memory 8 8 pdst ret rest) := by
  have huse1 := csUse_le_one memory 8 8 htn
  by_cases hu : (csUse memory 8 8).toNat = 0
  · have hsrc : (csSrc memory 8 8).toNat = 2112 := by
      rw [csSrc_toNat memory 8 8 huse1, if_pos hu]
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka csFixedTailKeep
      (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
      (by simpa [csFixedState, State.fork] using hfork)
      (run_csFixedTailKeep8 s memory pdst ret rest hcap hrun hcode hact hjump hs32 hdstFit hu hsrc)
      (by simpa [csFixedState] using hrun)
      (by simpa [csFixedState, State.fork] using hnp)
  · have hsrc : (csSrc memory 8 8).toNat = 1792 := by
      rw [csSrc_toNat memory 8 8 huse1, if_neg hu]
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka csFixedTailSub
      (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
      (by simpa [csFixedState, State.fork] using hfork)
      (run_csFixedTailSub8 s memory pdst ret rest hcap hrun hcode hact hjump hs32 hdstFit hu hsrc)
      (by simpa [csFixedState] using hrun)
      (by simpa [csFixedState, State.fork] using hnp)

/-- From the `s8` `JUMPDEST` (4374): the eight limb steps and the select tail.  rarej's carry
continuation enters here directly. -/
def gasSteps_csFixedFrom8 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 = UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (htn : (MachineState.readWord (csStep memory 8 8).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csFixedState s memory 8 0 3520 pdst ret rest)
      (subReturnedState s memory 8 8 pdst ret rest) := by

  have hStep8_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_0
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_1
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_2
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_3
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_4
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_4 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_5 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_5
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_5 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_6 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_6
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_6 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_7 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_7
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_7 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hTail8 := gasSteps_csFixedTail8 s memory pdst ret rest hcap hrun hcode hact hjump hs32
    hdstFit hfork hnp htn

  exact (((((((hStep8_0.trans hStep8_1).trans hStep8_2).trans hStep8_3).trans hStep8_4).trans hStep8_5).trans hStep8_6).trans hStep8_7).trans hTail8

/-- The subtraction branch of the select with its source stated directly: valid for any nonzero
flag word at `0x820` (`csSrc` is only the `≤ 1` encoding of the same choice). -/
def subFlagReturnedState (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := MachineState.writeBytes (csStep memory n n).memory
             (MachineState.readPadded (csStep memory n n).memory 1792 (32 * n)) pdst.toNat }

set_option linter.unusedSimpArgs false in
/-- `use ≠ 0`: the `JUMPI` takes pc 4538, which copies the difference block at `SUBB`. -/
theorem run_csFixedTailSubFlag8 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 =
      UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (huse : (csUse memory 8 8).toNat ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTailSub
      (csFixedState s memory 8 8 3683 pdst ret rest) =
      some (subFlagReturnedState s memory 8 pdst ret rest) := by
  have h4538 : (3717 : UInt256).toNat = 3717 := by decide
  have heq4538 : (3717 : UInt256) = UInt256.ofNat 3717 := by decide
  have h1792 : (1792 : UInt256).toNat = 1792 := by decide
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32 * 8 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 8 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 8) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 8) (by omega) (by omega) hact
  have hcondEq : UInt256.lor (MachineState.readWord (csStep memory 8 8).memory 2080)
      (UInt256.isZero (csStep memory 8 8).flag) = csUse memory 8 8 := rfl
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      1792 (32 * 8)) = s.activeWords :=
    activeWords_fix s 1792 (32 * 8) (by omega) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [h4538, heq4538, h1792, jumpDestCopyResume, csFixedTailSub, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subFlagReturnedState, hcondEq, UInt256.isTrue, huse,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      capacity, Nat.add_assoc, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- From `s8` with a nonzero flag word at `0x820` (st8 stores the row head there on the carry
continuation): the eight limb steps and the subtraction branch of the select. -/
def gasSteps_csFixedFrom8Flag (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 = UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (hflag : (MachineState.readWord (csStep memory 8 8).memory 2080).toNat ≠ 0) :
    Challenge.EvmProof.GasSteps (csFixedState s memory 8 0 3520 pdst ret rest)
      (subFlagReturnedState s memory 8 pdst ret rest) := by

  have hStep8_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_0
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_1
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_2
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_3
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_4
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_4 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_5 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_5
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_5 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_6 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_6
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_6 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_7 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep8_7
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_7 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have huse : (csUse memory 8 8).toNat ≠ 0 := by
    rw [csUse, Challenge.EvmProof.Word.word_toNat_lor]
    have := @Nat.left_le_or (MachineState.readWord (csStep memory 8 8).memory 2080).toNat
      (UInt256.isZero (csStep memory 8 8).flag).toNat
    omega
  have hTail8 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedTailSub
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedTailSubFlag8 s memory pdst ret rest hcap hrun hcode hact hjump hs32 hdstFit huse)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  exact (((((((hStep8_0.trans hStep8_1).trans hStep8_2).trans hStep8_3).trans hStep8_4).trans hStep8_5).trans hStep8_6).trans hStep8_7).trans hTail8

def gasSteps_csFixed8 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs : MachineState.readWord memory 2688 = UInt256.ofNat (32 * 8))
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2688 = UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2816)
    (htn : (MachineState.readWord (csStep memory 8 8).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (subReturnedState s memory 8 8 pdst ret rest) := by

  have hEntry8 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedEntry8
    (by simpa [subEntryState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [subEntryState, State.fork] using hfork)
    (run_csFixedEntry8 s memory pdst ret rest hcap hrun hcode hact hs)
    (by simpa [subEntryState] using hrun)
    (by simpa [subEntryState, State.fork] using hnp)

  exact hEntry8.trans (gasSteps_csFixedFrom8 s memory pdst ret rest hcap hrun hcode hact hfork hnp
    hjump hs32 hdstFit htn)

set_option linter.unusedSimpArgs false in
theorem run_csFixedEntry4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord memory 2688 = UInt256.ofNat (32 * 4)) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedEntry4
      (subEntryState s memory pdst ret rest) =
      some (csFixedState s memory 4 0 3469 pdst ret rest) := by
  have hactS := activeWords_fix s 2688 32 (by decide) (by decide) hact
  have capacity (j : Nat) (hj : j ≤ 5) : rest.length + j < 1024 := by omega
  have hword9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword256 : (256 : UInt256).toNat = 256 := by decide
  have hword4972 : (3508 : UInt256).toNat = 3508 := by decide
  have hword5022 : (3468 : UInt256).toNat = 3468 := by decide
  have hword5131 : (3468 : UInt256).toNat = 3468 := by decide
  have hword2225 : (901 : UInt256).toNat = 901 := by decide
  have hwordEq4972 : (3508 : UInt256) = UInt256.ofNat 3508 := by decide
  have hwordEq5022 : (3468 : UInt256) = UInt256.ofNat 3468 := by decide
  have hwordEq5131 : (3468 : UInt256) = UInt256.ofNat 3468 := by decide
  have hwordEq2225 : (901 : UInt256) = UInt256.ofNat 901 := by decide
  have hwordZero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedEntry4, subEntryState, csFixedState, csStep,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      hrun, hcode, hs32, hactS, capacity, Nat.add_assoc,
      UInt256.eq, UInt256.isTrue, opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword9344, hword128, hword256, hword4972, hword5022, hword5131, hword2225, hwordEq4972, hwordEq5022, hwordEq5131, hwordEq2225, hwordZero, List.exchange]

set_option linter.unusedSimpArgs false in

theorem run_csFixedStep4_0 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_0
      (csFixedState s memory 4 0 3469 pdst ret rest) =
      some (csFixedState s memory 4 1 3620 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 96 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2208 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1888 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 1 =
      (let prev := csStep memory 4 0
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 0))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 0))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (4 - 1 - 0))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 0
  have hword96 : (96 : UInt256).toNat = 96 := by decide
  have hword8352 : (2208 : UInt256).toNat = 2208 := by decide
  have hword7264 : (1888 : UInt256).toNat = 1888 := by decide
  have hword5117 : (3620 : UInt256).toNat = 3620 := by decide
  have hwordEq5117 : (3620 : UInt256) = UInt256.ofNat 3620 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_0, csFixedState, fixedOrComm, hstep, csStep, fixedSubtractZero, hrun, hcode,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword96, hword8352, hword7264, hword5117, hwordEq5117, List.exchange]
  try (split <;> decide)

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep4_1 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_1
      (csFixedState s memory 4 1 3620 pdst ret rest) =
      some (csFixedState s memory 4 2 3642 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 64 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2176 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1856 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 2 =
      (let prev := csStep memory 4 1
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 1))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 1))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (4 - 1 - 1))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 4 1
  have hword64 : (64 : UInt256).toNat = 64 := by decide
  have hword8320 : (2176 : UInt256).toNat = 2176 := by decide
  have hword7232 : (1856 : UInt256).toNat = 1856 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_1, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword64, hword8320, hword7232, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep4_2 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_2
      (csFixedState s memory 4 2 3642 pdst ret rest) =
      some (csFixedState s memory 4 3 3663 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 32 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2144 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1824 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 3 =
      (let prev := csStep memory 4 2
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 2))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 2))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (4 - 1 - 2))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 4 2
  have hword32 : (32 : UInt256).toNat = 32 := by decide
  have hword8288 : (2144 : UInt256).toNat = 2144 := by decide
  have hword7200 : (1824 : UInt256).toNat = 1824 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_2, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword32, hword8288, hword7200, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csFixedStep4_3 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_3
      (csFixedState s memory 4 3 3663 pdst ret rest) =
      some (csFixedState s memory 4 4 3683 pdst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 9) : rest.length + j < 1024 := by omega
  have ha0 := activeWords_fix s 0 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2112 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1792 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 4 =
      (let prev := csStep memory 4 3
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 3))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 3))
       let y := md + prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded (t - y).toNat 32) (1792 + 32 * (4 - 1 - 3))
         flag := UInt256.lor (UInt256.lt t y) (UInt256.lt y prev.flag) } : LimbState) := csStep_succ_alt memory 4 3
  have hword0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hword8256 : (2112 : UInt256).toNat = 2112 := by decide
  have hword7168 : (1792 : UInt256).toNat = 1792 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_3, csFixedState, fixedOrComm, hstep, hrun,
      capacity, Nat.add_assoc, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword0, hzeroNat, hword8256, hword7168, List.exchange]

set_option linter.unusedSimpArgs false in
/-- `use ≠ 0`: the `JUMPI` takes pc 4538, which copies the difference block at `SUBB`. -/
theorem run_csFixedTailSub4 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 2688 =
      UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 2816)
    (huse : (csUse memory 4 4).toNat ≠ 0)
    (hsrc : (csSrc memory 4 4).toNat = 1792) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTailSub
      (csFixedState s memory 4 4 3683 pdst ret rest) =
      some (subReturnedState s memory 4 4 pdst ret rest) := by
  have h4538 : (3717 : UInt256).toNat = 3717 := by decide
  have heq4538 : (3717 : UInt256) = UInt256.ofNat 3717 := by decide
  have h1792 : (1792 : UInt256).toNat = 1792 := by decide
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32 * 4 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 4 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 4) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 4) (by omega) (by omega) hact
  have hcondEq : UInt256.lor (MachineState.readWord (csStep memory 4 4).memory 2080)
      (UInt256.isZero (csStep memory 4 4).flag) = csUse memory 4 4 := rfl
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      1792 (32 * 4)) = s.activeWords :=
    activeWords_fix s 1792 (32 * 4) (by omega) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [h4538, heq4538, h1792, jumpDestCopyResume, csFixedTailSub, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subReturnedState, hcondEq, hsrc, UInt256.isTrue, huse,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      capacity, Nat.add_assoc, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- `use = 0`: the `JUMPI` falls through to the shared copy block at pc 4527, which copies `t`. -/
theorem run_csFixedTailKeep4 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 2688 =
      UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 2816)
    (huse : (csUse memory 4 4).toNat = 0)
    (hsrc : (csSrc memory 4 4).toNat = 2112) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedTailKeep
      (csFixedState s memory 4 4 3683 pdst ret rest) =
      some (subReturnedState s memory 4 4 pdst ret rest) := by
  have h4538 : (3717 : UInt256).toNat = 3717 := by decide
  have h4527 : (3706 : UInt256).toNat = 3706 := by decide
  have heq4527 : (3706 : UInt256) = UInt256.ofNat 3706 := by decide
  have h2112 : (2112 : UInt256).toNat = 2112 := by decide
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32 * 4 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * 4 := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * 4) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * 4) (by omega) (by omega) hact
  have hcondEq : UInt256.lor (MachineState.readWord (csStep memory 4 4).memory 2080)
      (UInt256.isZero (csStep memory 4 4).flag) = csUse memory 4 4 := rfl
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      2112 (32 * 4)) = s.activeWords :=
    activeWords_fix s 2112 (32 * 4) (by omega) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [h4538, h4527, heq4527, h2112, jumpDestEarlyCopy, csFixedTailKeep, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csFixedState, subReturnedState, hcondEq, hsrc, UInt256.isTrue, huse,
      fixedPC3777, fixedPC3114, fixedPC3115, fixedPC3116,
      fixedPC3117, fixedPC3118, fixedPC3119, fixedPC3805,
      capacity, Nat.add_assoc, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- The selection tail, split on `use`: either branch returns `subReturnedState`. -/
def gasSteps_csFixedTail4 (s : State) (memory : ByteArray)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 2688 =
      UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 2816)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (htn : (MachineState.readWord (csStep memory 4 4).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csFixedState s memory 4 4 3683 pdst ret rest)
      (subReturnedState s memory 4 4 pdst ret rest) := by
  have huse1 := csUse_le_one memory 4 4 htn
  by_cases hu : (csUse memory 4 4).toNat = 0
  · have hsrc : (csSrc memory 4 4).toNat = 2112 := by
      rw [csSrc_toNat memory 4 4 huse1, if_pos hu]
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka csFixedTailKeep
      (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
      (by simpa [csFixedState, State.fork] using hfork)
      (run_csFixedTailKeep4 s memory pdst ret rest hcap hrun hcode hact hjump hs32 hdstFit hu hsrc)
      (by simpa [csFixedState] using hrun)
      (by simpa [csFixedState, State.fork] using hnp)
  · have hsrc : (csSrc memory 4 4).toNat = 1792 := by
      rw [csSrc_toNat memory 4 4 huse1, if_neg hu]
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka csFixedTailSub
      (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
      (by simpa [csFixedState, State.fork] using hfork)
      (run_csFixedTailSub4 s memory pdst ret rest hcap hrun hcode hact hjump hs32 hdstFit hu hsrc)
      (by simpa [csFixedState] using hrun)
      (by simpa [csFixedState, State.fork] using hnp)

def gasSteps_csFixed4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs : MachineState.readWord memory 2688 = UInt256.ofNat (32 * 4))
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 2688 = UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 2816)
    (htn : (MachineState.readWord (csStep memory 4 4).memory 2080).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (subReturnedState s memory 4 4 pdst ret rest) := by

  have hEntry4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedEntry4
    (by simpa [subEntryState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [subEntryState, State.fork] using hfork)
    (run_csFixedEntry4 s memory pdst ret rest hcap hrun hcode hact hs)
    (by simpa [subEntryState] using hrun)
    (by simpa [subEntryState, State.fork] using hnp)

  have hStep4_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep4_0
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep4_1
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep4_2
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka csFixedStep4_3
    (by simpa [csFixedState, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hTail4 := gasSteps_csFixedTail4 s memory pdst ret rest hcap hrun hcode hact hjump hs32
    hdstFit hfork hnp htn

  exact ((((hEntry4.trans hStep4_0).trans hStep4_1).trans hStep4_2).trans hStep4_3).trans hTail4

/-- Whole-subroutine trace for `CSUB`: from the entry `[pd, ret]` to the return
jump, with `t mod m` copied into the block at `pd`. -/
def gasSteps_csub_sub (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hml : MachineState.readWord memory 2752 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 2784 = UInt256.ofNat (2080 + 32 * n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 2688 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 2816)
    (htn : (MachineState.readWord (csStep memory n n).memory 2080).toNat ≤ 1)
    -- the rewritten dispatcher admits only four or eight limbs, so the general-width
    -- conditional subtraction below it is unreachable
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (subReturnedState s memory n n pdst ret rest) := by
  have hnn : n - 1 + 1 = n := by omega
  have hs : MachineState.readWord memory 2688 = UInt256.ofNat (32 * n) := by
    rw [csStep_readWord_disjoint memory n 2688 (by omega) (by omega) n le_rfl] at hs32
    exact hs32
  by_cases hn8 : n = 8
  · subst n
    exact gasSteps_csFixed8 s memory pdst ret rest hcap hrun hcode hact hfork hnp hs hjump hs32 hdstFit htn
  by_cases hn4 : n = 4
  · subst n
    exact gasSteps_csFixed4 s memory pdst ret rest hcap hrun hcode hact hfork hnp hs hjump hs32 hdstFit htn
  exact absurd hfast (fun h => h.elim hn4 hn8)


end CycleSubmission.Global.Fast.Csub
