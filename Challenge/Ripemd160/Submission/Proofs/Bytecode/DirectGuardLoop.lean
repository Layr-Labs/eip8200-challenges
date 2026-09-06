import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardEarly

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The thirty-one word comparisons of the 1000-a guard. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 29) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x1347 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2815 (by rfl)
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hlt : 32 * n + 64 < 992 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 := Nat.mod_eq_of_lt hstart
  have hnextMod : (32 * n + 64) % 2 ^ 256 = 32 * n + 64 := Nat.mod_eq_of_lt hnext
  have hnaddr : 32 * (n + 1) = 32 * n + 32 := by omega
  have hsum : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hcond : (UInt256.lt (UInt256.ofNat (32 * n + 64))
      (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, hnextMod,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hxor : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (MachineState.readWord input 0) := BooleanSelect.xor_comm _ _
  have hacc : loopAcc input (n + 1) =
      UInt256.lor (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
        (referenceWord input)) (loopAcc input n) := by rw [loopAcc]
  have hstep : UInt256.lor
      (UInt256.xor (MachineState.readWord input 0)
        (MachineState.readWord input
          ((32 * n + 32) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936)))
      (loopAcc input n) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (32 * n + 32))
          (MachineState.readWord input 0))
        (loopAcc input n) := by
    rw [show
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        2 ^ 256 by norm_num]
    rw [hmod, hxor]
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, referenceWord, hdest, hstart,
    hnext, hmod, hnextMod, hnaddr, hsum, hlt, hcond, hxor, hacc, hstep,
    Word.lor_comm,
    List.exchange, Nat.add_assoc, Nat.mul_add, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (input : ByteArray) :
    run loopPath (loopState input 29) = some (loopExitState input) := by
  have hacc : loopAcc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960)
        (referenceWord input)) (loopAcc input 29) := by
    rw [show 30 = 29 + 1 by omega, loopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by decide
  have hcond : (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)).toNat = 0 := by
    decide
  have hxor : UInt256.xor (MachineState.readWord input 0)
      (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (MachineState.readWord input 0) := BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, loopExitState, referenceWord,
    hacc, hfalse, hcond, hxor, Word.lor_comm, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
