import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLoopLastFallthrough

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def loopBodyPath : List Located := loopPath.take 29

theorem loopPath_eq_body_jump : loopPath = loopBodyPath ++ loopJumpPath := by rfl

theorem run_loop_body_last (input : ByteArray) :
    run loopBodyPath (loopState input 375) = some (loopBranchState input) := by
  have hexp := PatternedScanLogic.expected_evm 375 (by decide)
  have hexp' :
      UInt256.land (UInt256.ofNat 255)
        (UInt256.ofNat 7 +
          (UInt256.ofNat 37 * UInt256.ofNat 375 +
            UInt256.ofNat 11 * (UInt256.ofNat 375 / UInt256.ofNat 251))) =
        PatternedScanLogic.expectedWord 375 := by
    have harg :
        UInt256.ofNat 7 +
            (UInt256.ofNat 37 * UInt256.ofNat 375 +
              UInt256.ofNat 11 * (UInt256.ofNat 375 / UInt256.ofNat 251)) =
          UInt256.ofNat 375 * UInt256.ofNat 37 +
            UInt256.ofNat 375 / UInt256.ofNat 251 * UInt256.ofNat 11 +
              UInt256.ofNat 7 := by
      rw [PatternedScanLogic.mul_comm_word (UInt256.ofNat 37) (UInt256.ofNat 375),
        PatternedScanLogic.mul_comm_word (UInt256.ofNat 11)
          (UInt256.ofNat 375 / UInt256.ofNat 251),
        PatternedScanLogic.add_comm_word]
    rw [Word.land_comm, harg, hexp]
  have hnmod : 375 % 2 ^ 256 = 375 := Nat.mod_eq_of_lt (by norm_num)
  have hread : MachineState.readWord input
      (375 % 115792089237316195423570985008687907853269984665640564039457584007913129639936) =
      MachineState.readWord input 375 := by
    rw [Nat.mod_eq_of_lt (by norm_num)]
  have hbyte : calldataByte input 375 =
      UInt256.byteAt ⟨0⟩ (MachineState.readWord input 375) := rfl
  have hacc : scanAcc input (375 + 1) =
      UInt256.lor (UInt256.xor (expectedWord 375) (calldataByte input 375))
        (scanAcc input 375) := rfl
  have hxor : UInt256.xor
      (UInt256.byteAt ⟨0⟩ (MachineState.readWord input 375)) (expectedWord 375) =
      UInt256.xor (expectedWord 375)
        (UInt256.byteAt ⟨0⟩ (MachineState.readWord input 375)) :=
    BooleanSelect.xor_comm _ _
  have hcond :
      UInt256.lt (UInt256.ofNat 376) (UInt256.ofNat 376) = 0 := by
    apply Challenge.EvmProof.Word.word_ext
    decide
  simp (config := { maxSteps := 1000000 })
    [loopBodyPath, loopPath, opAt, pushAt, wfOp, loopState, loopBranchState,
    hexp', hnmod, hread, hbyte, hacc, hxor, hcond,
    Nat.add_comm, List.exchange, UInt256.isTrue, Word.lor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (input : ByteArray) (_hfit : 375 < input.size) :
    run loopPath (loopState input 375) = some (loopExitState input) := by
  rw [loopPath_eq_body_jump]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    loopBodyPath loopJumpPath (loopState input 375) (loopBranchState input)
    (loopExitState input) (run_loop_body_last input) (by rfl)
    (run_loop_fallthrough input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
