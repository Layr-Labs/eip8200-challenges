import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Fixed-width loop guard and calldata-word load

This module stops before the repeated byte body.  It proves both outcomes of
the loop guard and the two-instruction load that establishes `wordState`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopControl

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates
open WindowHitPaths

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

@[simp] private theorem controlPCs (index : Nat)
    (hlo : 1991 ≤ index) (hhi : index ≤ 1998) :
    Artifact.submissionArtifact.instructionPC index =
      [3197, 3198, 3199, 3201, 3202, 3205, 3206, 3207][index - 1991]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
private theorem run_guard_continue_generic (template : State) (pointer : Nat)
    (accumulator modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hpointer : pointer < 160)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loopGuardPath
      (framed template 3197 (UInt256.ofNat pointer :: accumulator :: modulus :: rest)) =
    some (framed template 3206 (UInt256.ofNat pointer :: accumulator :: modulus :: rest)) := by
  have hmod : pointer % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pointer :=
    Nat.mod_eq_of_lt (by omega)
  have hne : pointer ≠ 160 := Nat.ne_of_lt hpointer
  have hne' : 160 ≠ pointer := hne.symm
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  simp (disch := omega) [loopGuardPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, controlPCs,
    UInt256.isTrue, UInt256.eq, hmod, hne, hne',
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc, hcap3, hcap4, hcap5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
private theorem run_load_generic (template : State) (pointer : Nat)
    (accumulator modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hpointer : pointer < 160)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordLoadPath
      (framed template 3206 (UInt256.ofNat pointer :: accumulator :: modulus :: rest)) =
    some (framed template 3208
      (MachineState.readWord template.executionEnv.calldata pointer ::
        UInt256.ofNat pointer :: accumulator :: modulus :: rest)) := by
  have hmod : pointer % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pointer :=
    Nat.mod_eq_of_lt (by omega)
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  simp (disch := omega) [wordLoadPath, Main.opAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, controlPCs,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc, hcap3, hcap4,
    Challenge.EvmProof.Word.succ_ofNat_mod]

set_option linter.unusedSimpArgs false in
private theorem run_guard_exit_generic (template : State)
    (accumulator modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hcode : template.executionEnv.code = submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock loopGuardPath
      (framed template 3197 (UInt256.ofNat 160 :: accumulator :: modulus :: rest)) =
    some (framed template 3555 (UInt256.ofNat 160 :: accumulator :: modulus :: rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  simp (disch := omega) [loopGuardPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, hrun, hcode, controlPCs,
    UInt256.isTrue, UInt256.eq, jump3555,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc, hcap3, hcap4, hcap5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_loopGuard_continue (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    Challenge.EvmProof.Stepper.runLocatedBlock loopGuardPath
      (loopState input pointer accumulator) =
        some (loopContinueState input pointer accumulator) := by
  have h := run_guard_continue_generic (loopState input pointer accumulator)
    pointer accumulator (modulusWord input) (routeStack input)
    (by simp [routeStack]) hpointer rfl
  simpa only [framed, loopState, loopContinueState, List.cons_append, List.nil_append] using h

theorem run_wordLoad (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordLoadPath
      (loopContinueState input pointer accumulator) =
        some (wordState input pointer 0 3208 accumulator) := by
  have h := run_load_generic (loopState input pointer accumulator)
    pointer accumulator (modulusWord input) (routeStack input)
    (by simp [routeStack]) hpointer rfl
  have hcalldata : (loopState input pointer accumulator).executionEnv.calldata = input := rfl
  rw [hcalldata] at h
  simpa only [framed, loopContinueState, loopState, wordState, byteAccumulator,
    List.cons_append, List.nil_append] using h

theorem run_loopGuard_exit (input : ByteArray) (accumulator : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock loopGuardPath
      (loopState input 160 accumulator) = some (finishState input accumulator) := by
  have h := run_guard_exit_generic (loopState input 160 accumulator)
    accumulator (modulusWord input) (routeStack input) (by simp [routeStack]) rfl rfl
  simpa only [framed, finishState, loopState, List.cons_append, List.nil_append] using h

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

def gasSteps_loopContinue (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    LoopContinueStep input pointer accumulator :=
  (sound loopGuardPath
    (run_loopGuard_continue input pointer accumulator hpointer)).trans
  (sound wordLoadPath (run_wordLoad input pointer accumulator hpointer))

def gasSteps_loopExit (input : ByteArray) (accumulator : UInt256) :
    LoopExitStep input accumulator :=
  sound loopGuardPath (run_loopGuard_exit input accumulator)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopControl
