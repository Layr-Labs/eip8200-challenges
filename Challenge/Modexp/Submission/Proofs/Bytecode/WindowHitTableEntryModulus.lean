import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryModulus

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates
open WindowHitPaths

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

@[simp] private theorem modulusPCs (index : Nat)
    (hlo : 1848 ≤ index) (hhi : index ≤ 1854) :
    Artifact.submissionArtifact.instructionPC index =
      [3024, 3025, 3027, 3028, 3029, 3030, 3033][index - 1848]! := by
  interval_cases index <;> decide

private theorem toNat_ne_zero {word : UInt256} (hword : word ≠ 0) :
    word.toNat ≠ 0 := by
  intro hz
  apply hword
  apply Challenge.EvmProof.Word.word_ext
  rw [show (0 : UInt256).toNat = 0 by decide]
  exact hz

set_option linter.unusedSimpArgs false in
theorem run_nonzero_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hword : MachineState.readWord template.executionEnv.calldata 160 ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock modulusCheckPath
      (framed template 3024 rest) =
    some (framed template 3034
      (MachineState.readWord template.executionEnv.calldata 160 :: rest)) := by
  have hnat := toNat_ne_zero hword
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  simp (disch := omega) [modulusCheckPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, modulusPCs, hnat,
    UInt256.isZero, UInt256.isTrue, hcap0, hcap1, hcap2, hcap3,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_zero_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hcode : template.executionEnv.code = submissionBytecode)
    (hword : MachineState.readWord template.executionEnv.calldata 160 = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock modulusCheckPath
      (framed template 3024 rest) =
    some (framed template 3563
      (MachineState.readWord template.executionEnv.calldata 160 :: rest)) := by
  have hnat : (MachineState.readWord template.executionEnv.calldata 160).toNat = 0 := by
    rw [hword]
    decide
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  simp (disch := omega) [modulusCheckPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, hcode, modulusPCs,
    hword, hnat, jump3563, UInt256.isZero, UInt256.isTrue,
    hcap0, hcap1, hcap2, hcap3,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_modulus_nonzero (input : ByteArray)
    (hmodulus : modulusWord input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock modulusCheckPath
      (hitState input) = some (nonzeroState input) := by
  have hcalldata :
      (Dispatch.wordEntryState input).executionEnv.calldata = input := by rfl
  have hword : MachineState.readWord
      (Dispatch.wordEntryState input).executionEnv.calldata 160 ≠ 0 := by
    rw [hcalldata]
    simpa only [modulusWord] using hmodulus
  have h := run_nonzero_generic (Dispatch.wordEntryState input)
    (routeStack input) (by simp [routeStack]) rfl
    hword
  rw [hcalldata] at h
  simpa only [framed, hitState, nonzeroState, modulusWord,
    routeStack_eq_entry] using h

theorem run_modulus_zero (input : ByteArray)
    (hmodulus : modulusWord input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock modulusCheckPath
      (hitState input) = some (zeroState input) := by
  have hcalldata :
      (Dispatch.wordEntryState input).executionEnv.calldata = input := by rfl
  have hword : MachineState.readWord
      (Dispatch.wordEntryState input).executionEnv.calldata 160 = 0 := by
    rw [hcalldata]
    simpa only [modulusWord] using hmodulus
  have h := run_zero_generic (Dispatch.wordEntryState input)
    (routeStack input) (by simp [routeStack]) rfl rfl
    hword
  rw [hcalldata] at h
  simpa only [framed, hitState, zeroState, modulusWord,
    routeStack_eq_entry] using h

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryModulus
