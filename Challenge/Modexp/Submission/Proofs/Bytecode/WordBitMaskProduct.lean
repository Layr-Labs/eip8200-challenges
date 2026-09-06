import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_bitDispatch_zero (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256)
    (hbit : exponentBit byte j = UInt256.ofNat 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDispatchPath
      (bitSquaredState input outer j byte offset acc base) =
        some (bitDispatchState input outer j byte offset acc base) := by
  have h641 : (641 : UInt256).toNat = 641 := by decide
  have h641Word : (641 : UInt256) = UInt256.ofNat 641 := by decide
  have hjump641 : Decode.isValidJumpDest submissionBytecode 641 = true :=
    Artifact.isValidJumpDest_index 512 (by rfl)
  simp (config := { maxSteps := 125000 })
    [bitDispatchPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitDispatchState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange, UInt256.isTrue, UInt256.isZero,
      Challenge.EvmProof.Word.word_toNat_ofNat, hbit, h641, h641Word, hjump641]

set_option linter.unusedSimpArgs false in
theorem run_bitDispatch_one (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256)
    (hbit : exponentBit byte j = UInt256.ofNat 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitDispatchPath
      (bitSquaredState input outer j byte offset acc base) =
        some (bitProductEntryState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitDispatchPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitSquaredState, bitProductEntryState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange, UInt256.isTrue, UInt256.isZero,
      Challenge.EvmProof.Word.word_toNat_ofNat, hbit]

set_option linter.unusedSimpArgs false in
theorem run_bitProduct (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitProductPath
      (bitProductEntryState input outer j byte offset acc base) =
        some (bitProductState input outer j byte offset acc base) := by
  simp (config := { maxSteps := 125000 })
    [bitProductPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductEntryState, bitProductState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange, UInt256.isTrue, UInt256.isZero,
      Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
