import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
private theorem run_wordTail_generic (template : State)
    (b e m expOff modOff : UInt256)
    (hcode : template.executionEnv.code = submissionBytecode)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordTailPath
      (framed template 1253 [modOff, expOff, m, e, b]) =
    some (framed template 5329
      [b, e, m, UInt256.ofNat 96, expOff, modOff, UInt256.ofNat 1267,
        modOff, expOff, m, e, b]) := by
  have h5329 : (5329 : UInt256).toNat = 5329 := by decide
  have h5329Word : (5329 : UInt256) = UInt256.ofNat 5329 := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  have h1267Word : (1267 : UInt256) = UInt256.ofNat 1267 := by decide
  simp (config := { maxSteps := 200000 })
    [framed, wordTailPath, wordRestPath, wordEntryPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hcode, hrun, h5329, h5329Word, h96Word, h1267Word,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_wordTail (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordTailPath
      (wordCheckedState input) = some (wordDispatchRouteState input) := by
  have h := run_wordTail_generic (Main.headerState input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
    (UInt256.ofNat (modulusSize input)) (UInt256.ofNat (96 + baseSize input))
    (UInt256.ofNat (96 + (baseSize input + exponentSize input))) rfl rfl
  simpa only [framed, wordCheckedState, wordDispatchRouteState, wordEntryState,
    Nat.add_assoc] using h
set_option linter.unusedSimpArgs false in
theorem run_zeroExponentDispatch_nonzero (input : ByteArray)
    (hzero : exponentSize input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroExponentDispatchPath
      (wordDispatchRouteState input) = some (wordRouteEntryState input) := by
  have he : UInt256.ofNat (exponentSize input) ≠ 0 := by
    simp [hzero]
  simp [zeroExponentDispatchPath, wordDispatchRouteState, wordRouteEntryState,
    wordEntryState, opAt, pushAt, framed,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.isTrue, he, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroExponentDispatch_zero (input : ByteArray)
    (hzero : exponentSize input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroExponentDispatchZeroPath
      (wordDispatchRouteState input) = some (zeroExponentHandlerState input) := by
  have he : UInt256.ofNat (exponentSize input) = 0 := by simp [hzero]
  simp [zeroExponentDispatchZeroPath, zeroExponentDispatchPath,
    wordDispatchRouteState, zeroExponentHandlerState, wordEntryState, opAt,
    pushAt, framed, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.isTrue, he, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroExponentHandler (input : ByteArray)
    (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroExponentHandlerPath
      (zeroExponentHandlerState input) = some
        (zeroExponentBaseFinishState input) := by
  have hm : UInt256.ofNat (modulusValue input) ≠ 0 := by
    simp [hmodpos]
  simp [zeroExponentHandlerPath, zeroExponentHandlerState,
    zeroExponentBaseFinishState, wordDispatchRouteState, wordEntryState,
    opAt, pushAt, framed,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, hm]

set_option linter.unusedSimpArgs false in
theorem run_zeroExponentHandler_zeroModulus (input : ByteArray)
    (hmodzero : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroExponentHandlerZeroModulusPath
      (zeroExponentHandlerState input) = some (wordEntryState input) := by
  have hm : UInt256.ofNat (modulusValue input) = 0 := by simp [hmodzero]
  simp [zeroExponentHandlerZeroModulusPath, zeroExponentHandlerPath,
    zeroExponentHandlerState, wordDispatchRouteState, wordEntryState, opAt,
    pushAt, framed, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, hm]


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
