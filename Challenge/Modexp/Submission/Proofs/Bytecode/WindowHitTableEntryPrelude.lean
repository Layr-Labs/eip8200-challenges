import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryPrelude

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates
open WindowHitPaths

private def startState (template : State) (modulus : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 3034
    stack := modulus :: rest
    memory := ByteArray.empty
    activeWords := UInt256.ofNat 0 }

private def endState (template : State) (base modulus : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 3053
    stack := [WindowMath.tableWord base modulus 2, base, modulus] ++ rest
    memory := WindowTableMemory.tableMemoryThrough base modulus 3
    activeWords := UInt256.ofNat 3 }

@[simp] private theorem preludePCs (index : Nat)
    (hlo : 1855 ≤ index) (hhi : index ≤ 1869) :
    Artifact.submissionArtifact.instructionPC index =
      [3034, 3036, 3037, 3039, 3040, 3041, 3042, 3044,
       3045, 3046, 3047, 3048, 3049, 3050, 3052][index - 1855]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
theorem run_generic (template : State) (modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePreludePath
      (startState template modulus rest) =
    some (endState template
      (MachineState.readWord template.executionEnv.calldata 96) modulus rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (disch := omega)
    [tablePreludePath, Main.opAt, Main.pushAt, Main.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, startState, endState,
      WindowTableMemory.tableMemoryThrough, WindowTableMemory.storeWord,
      WindowMath.tableWord, List.range_succ, List.foldl_append,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      show (0 : UInt256).toNat = 0 by decide,
      hrun, hrest, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, preludePCs,
      List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  constructor
  · decide
  · rfl

theorem run_tablePrelude (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePreludePath
      (nonzeroState input) = some (tableState input 2 3053) := by
  have h := run_generic (Dispatch.wordEntryState input) (modulusWord input)
    (routeStack input) (by simp [routeStack]) rfl
  have hcalldata :
      (Dispatch.wordEntryState input).executionEnv.calldata = input := by rfl
  rw [hcalldata] at h
  have hstart : startState (Dispatch.wordEntryState input) (modulusWord input)
      (routeStack input) = nonzeroState input := by rfl
  have hend : endState (Dispatch.wordEntryState input)
      (MachineState.readWord input 96)
      (modulusWord input) (routeStack input) = tableState input 2 3053 := by rfl
  rw [hstart, hend] at h
  exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryPrelude
