import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntry

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon

open EvmSemantics
open EvmSemantics.EVM
open WindowHitStates

def sound {s t : State}
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

syntax "window_table_update " ident ident ident num num num num num num : command

macro_rules
  | `(window_table_update $runName:ident $gasName:ident $pathName:ident
      $power:num $nextPower:num $startPC:num $endPC:num $firstIndex:num
      $offset:num) => `(
    private def tableKernelState (template : State) (base modulus : UInt256)
        (power pc : Nat) (rest : List UInt256) : State :=
      { template with
        pc := UInt256.ofNat pc
        stack := [WindowMath.tableWord base modulus power, base, modulus] ++ rest
        memory := WindowTableMemory.tableMemoryThrough base modulus (power + 1)
        activeWords := UInt256.ofNat (power + 1) }

    @[simp] private theorem tablePCs (index : Nat)
        (hlo : $firstIndex ≤ index) (hhi : index ≤ $firstIndex + 8) :
        Artifact.submissionArtifact.instructionPC index =
          $startPC + (index - $firstIndex) +
            (if index - $firstIndex = 8 then
              (if $offset < 256 then 1 else 2) else 0) := by
      interval_cases index <;> decide

    set_option linter.unusedSimpArgs false in
    private theorem run_generic (template : State) (base modulus : UInt256)
        (rest : List UInt256) (hrest : rest.length ≤ 1000)
        (hrun : template.halt = .Running) :
        Challenge.EvmProof.Stepper.runLocatedBlock $pathName
          (tableKernelState template base modulus $power $startPC rest) =
        some (tableKernelState template base modulus $nextPower $endPC rest) := by
      have h3 : rest.length + 3 < 1024 := by omega
      have h4 : rest.length + 4 < 1024 := by omega
      have h5 : rest.length + 5 < 1024 := by omega
      have h6 : rest.length + 6 < 1024 := by omega
      have hactive : MachineState.activeWordsAfter $nextPower $offset 32 =
          $nextPower + 1 := by
        norm_num [MachineState.activeWordsAfter]
      unfold $pathName
      simp (config := { maxSteps := 300000 }) (disch := omega)
        [WindowHitPaths.updateAt, Main.opAt, Main.pushAt, Main.wfOp,
          Challenge.EvmProof.Stepper.runLocatedBlock,
          Challenge.EvmProof.Stepper.runLocated,
          Challenge.EvmProof.Stepper.runInstr,
          tableKernelState, WindowTableMemory.tableMemoryThrough_succ,
          WindowMath.tableWord, WindowTableMemory.storeWord,
          hrest, h3, h4, h5, h6, hactive, hrun, tablePCs,
          show ($power : Nat) ≠ 0 by decide,
          State.activeWordsAfterUInt256, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, List.exchange,
          WindowTableMemory.activeWordsAfter_table,
          Challenge.EvmProof.Word.literal_eq_ofNat,
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Challenge.EvmProof.Word.succ_ofNat_mod,
          Challenge.EvmProof.Word.ofNat_add_mod]

    theorem $runName (input : ByteArray) :
        Challenge.EvmProof.Stepper.runLocatedBlock $pathName
          (WindowHitStates.tableState input $power $startPC) =
        some (WindowHitStates.tableState input $nextPower $endPC) := by
      have h := run_generic (Dispatch.wordEntryState input)
        (WindowHitStates.baseWord input) (WindowHitStates.modulusWord input)
        (WindowControlDefs.routeStack input)
        (by simp [WindowControlDefs.routeStack]) rfl
      simpa only [tableKernelState, WindowHitStates.tableState,
        WindowHitStates.tableWord, WindowHitStates.tableMemoryThrough] using h

    def $gasName (input : ByteArray) :
        WindowHitStates.TableUpdateStep input $power $startPC := by
      exact WindowHitTableUpdateCommon.sound $pathName ($runName input)
  )

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdateCommon
