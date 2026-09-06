import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Fixed-width table update 4

This module establishes the reusable proof shape for one lookup-table slot.
Later modules instantiate the same nine-instruction correspondence without
re-elaborating the modulus branch or the table prelude.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate4

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates
open WindowHitPaths

private def tableKernelState (template : State) (base modulus : UInt256)
    (power pc : Nat) (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat pc
    stack := [WindowMath.tableWord base modulus power, base, modulus] ++ rest
    memory := WindowTableMemory.tableMemoryThrough base modulus (power + 1)
    activeWords := UInt256.ofNat (power + 1) }

@[simp] private theorem table4PCs (index : Nat)
    (hlo : 1879 ≤ index) (hhi : index ≤ 1887) :
    Artifact.submissionArtifact.instructionPC index =
      ([3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3072]
        : List Nat)[index - 1879]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
private theorem run_table4_generic (template : State) (base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock table4Path
      (tableKernelState template base modulus 3 3063 rest) =
        some (tableKernelState template base modulus 4 3073 rest) := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have hactive : MachineState.activeWordsAfter 4 128 32 = 5 := by
    norm_num [MachineState.activeWordsAfter]
  simp (config := { maxSteps := 300000 }) (disch := omega)
    [table4Path, updateAt, Main.opAt, Main.pushAt, Main.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      tableKernelState, WindowTableMemory.tableMemoryThrough_succ,
      WindowMath.tableWord, WindowTableMemory.storeWord,
      hrest, h3, h4, h5, h6, hactive, hrun,
      table4PCs,
      State.activeWordsAfterUInt256,
      WindowTableMemory.activeWordsAfter_table,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_table4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock table4Path
      (tableState input 3 3063) = some (tableState input 4 3073) := by
  have h := run_table4_generic (Dispatch.wordEntryState input)
    (baseWord input) (modulusWord input) (routeStack input)
    (by simp [routeStack]) rfl
  simpa only [tableKernelState, tableState, tableWord, tableMemoryThrough] using h

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_table4 (input : ByteArray) : TableUpdateStep input 3 3063 := by
  exact sound table4Path (run_table4 input)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate4
