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
theorem run_bitJoin_zero (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256)
    (hbit : exponentBit byte j = UInt256.ofNat 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitJoinPath
      (bitDispatchState input outer j byte offset acc base) =
        some (bitJoinState input outer j byte offset
          (bitStep input byte j acc base) base) := by
  have hstep := bitStep_of_zero input byte j acc base hbit
  simp (config := { maxSteps := 150000 })
    [bitJoinPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitDispatchState, bitJoinState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange, hstep]

set_option linter.unusedSimpArgs false in
theorem run_bitJoin_one (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256)
    (hbit : exponentBit byte j = UInt256.ofNat 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitJoinPath
      (bitProductState input outer j byte offset acc base) =
        some (bitJoinState input outer j byte offset
          (bitStep input byte j acc base) base) := by
  have hstep := bitStep_of_one input byte j acc base hbit
  simp (config := { maxSteps := 150000 })
    [bitJoinPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitProductState, bitJoinState, bitLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, List.exchange, hstep]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
