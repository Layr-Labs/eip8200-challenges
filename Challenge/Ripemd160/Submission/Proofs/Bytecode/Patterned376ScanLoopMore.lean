import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 375)
    (_hfit : n < input.size) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 5017 = true :=
    validJumpDest_1399
  have hexp := PatternedScanLogic.expected_evm n (by omega)
  have hexp' :
      UInt256.land (UInt256.ofNat 255)
        (UInt256.ofNat 7 +
          (UInt256.ofNat 37 * UInt256.ofNat n +
            UInt256.ofNat 11 * (UInt256.ofNat n / UInt256.ofNat 251))) =
        PatternedScanLogic.expectedWord n := by
    have harg :
        UInt256.ofNat 7 +
            (UInt256.ofNat 37 * UInt256.ofNat n +
              UInt256.ofNat 11 * (UInt256.ofNat n / UInt256.ofNat 251)) =
          UInt256.ofNat n * UInt256.ofNat 37 +
            UInt256.ofNat n / UInt256.ofNat 251 * UInt256.ofNat 11 +
              UInt256.ofNat 7 := by
      rw [PatternedScanLogic.mul_comm_word (UInt256.ofNat 37) (UInt256.ofNat n),
        PatternedScanLogic.mul_comm_word (UInt256.ofNat 11)
          (UInt256.ofNat n / UInt256.ofNat 251),
        PatternedScanLogic.add_comm_word]
    rw [Word.land_comm, harg, hexp]
  have hnmod : n % 2 ^ 256 = n := Nat.mod_eq_of_lt (by omega)
  have hread : MachineState.readWord input
      (n % 115792089237316195423570985008687907853269984665640564039457584007913129639936) =
      MachineState.readWord input n := by
    rw [Nat.mod_eq_of_lt (by omega)]
  have hbyte : calldataByte input n =
      UInt256.byteAt ⟨0⟩ (MachineState.readWord input n) := rfl
  have hacc : scanAcc input (n + 1) =
      UInt256.lor (UInt256.xor (expectedWord n) (calldataByte input n))
        (scanAcc input n) := rfl
  have hxor : UInt256.xor
      (UInt256.byteAt ⟨0⟩ (MachineState.readWord input n)) (expectedWord n) =
      UInt256.xor (expectedWord n)
        (UInt256.byteAt ⟨0⟩ (MachineState.readWord input n)) :=
    BooleanSelect.xor_comm _ _
  have hlt : n + 1 < 376 := by omega
  have hcond :
      (UInt256.lt (UInt256.ofNat (n + 1)) (UInt256.ofNat 376)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 256),
      Nat.mod_eq_of_lt (by norm_num : 376 < 2 ^ 256), if_pos hlt]
    decide
  have hcond' :
      (UInt256.lt (UInt256.ofNat (1 + n)) (UInt256.ofNat 376)).toNat ≠ 0 := by
    simpa [Nat.add_comm] using hcond
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, hdest, hexp', hnmod, hread,
    hbyte, hacc, hxor, hcond, hcond', Nat.add_comm, List.exchange,
    UInt256.isTrue, Word.lor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
