import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Fixed-width table finish

This proves the four-instruction cleanup that establishes the loop head after
the last table slot.  The concrete execution is kept over generic framed
states so the legacy dispatcher is never unfolded.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableFinish

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitPaths
open WindowHitStates

private def tableEndState (template : State) (base modulus : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 3186
    stack := [WindowMath.tableWord base modulus 15, base, modulus] ++ rest
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

private def loopHeadState (template : State) (base modulus : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 3192
    stack := [UInt256.ofNat 128, UInt256.ofNat 1, modulus] ++ rest
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

@[simp] private theorem finishPCs (index : Nat)
    (hlo : 1950 ≤ index) (hhi : index ≤ 1953) :
    Artifact.submissionArtifact.instructionPC index =
      ([3186,3187,3188,3190] : List Nat)[index - 1950]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
private theorem run_tableFinish_generic (template : State)
    (base modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableFinishPath
      (tableEndState template base modulus rest) =
        some (loopHeadState template base modulus rest) := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have hpc3192 : (UInt256.ofNat 3187).toNat = 3187 := by decide
  have hpc3193 : (UInt256.ofNat 3188).toNat = 3188 := by decide
  have hpc3195 : (UInt256.ofNat 3190).toNat = 3190 := by decide
  have hsucc3192 : (UInt256.ofNat 3187).succ = UInt256.ofNat 3188 := by decide
  have hadd3193 : UInt256.ofNat 3188 + UInt256.ofNat 2 = UInt256.ofNat 3190 := by decide
  have hadd3195 : UInt256.ofNat 3190 + UInt256.ofNat 2 = UInt256.ofNat 3192 := by decide
  simp (disch := omega) [tableFinishPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    tableEndState, loopHeadState, hrest, h1, h2, h3, h4, hrun, finishPCs,
    hpc3192, hpc3193, hpc3195, hsucc3192, hadd3193, hadd3195,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tableFinish (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableFinishPath
      (tableState input 15 3186) =
        some (loopState input 128 (UInt256.ofNat 1)) := by
  have h := run_tableFinish_generic (Dispatch.wordEntryState input)
    (baseWord input) (modulusWord input) (routeStack input)
    (by simp [routeStack]) rfl
  have hmemory : tableMemoryThrough (baseWord input) (modulusWord input) 16 =
      tableMemory (baseWord input) (modulusWord input) := by rfl
  simpa only [tableEndState, loopHeadState, tableState, loopState,
    tableWord, Nat.reduceAdd, hmemory] using h

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

def gasSteps_tableFinish (input : ByteArray) :
    Challenge.EvmProof.GasSteps (tableState input 15 3186)
      (loopState input 128 (UInt256.ofNat 1)) :=
  sound tableFinishPath (run_tableFinish input)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableFinish
