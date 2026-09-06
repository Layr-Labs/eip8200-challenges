import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.all false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputLogic

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 376) :
    run sizePath (size376Entry input) = some (fallbackState input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hword : UInt256.ofNat input.size ≠ UInt256.ofNat 376 := by
    intro heq
    have hnat := congrArg UInt256.toNat heq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hsize hnat
  have hxor : UInt256.xor (UInt256.ofNat 376)
      (UInt256.ofNat input.size) ≠ 0 := by
    intro hz
    exact hword ((KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 376) (UInt256.ofNat input.size)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 376) (UInt256.ofNat input.size)) := by
    intro hnat
    apply hxor
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have hcond : (UInt256.xor (UInt256.ofNat 376)
      (UInt256.ofNat input.size)).toNat ≠ 0 := htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp [sizePath, opAt, pushAt, wfOp, size376Entry, fallbackState, atPC,
    htrue, hcond, hdest, UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_match (input : ByteArray) (hsize : input.size = 376) :
    run sizePath (size376Entry input) = some (sizeMatched input) := by
  have hzero : UInt256.xor (UInt256.ofNat 376)
      (UInt256.ofNat input.size) = 0 := by
    rw [hsize]
    exact (KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 376) (UInt256.ofNat 376)).2 rfl
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 376) (UInt256.ofNat input.size)) := by
    rw [hzero]
    decide
  have hcond : (UInt256.xor (UInt256.ofNat 376)
      (UInt256.ofNat input.size)).toNat = 0 := by rw [hzero]; rfl
  have hcondLit : (UInt256.xor (UInt256.ofNat 376)
      (UInt256.ofNat 376)).toNat = 0 := by decide
  simp [sizePath, opAt, pushAt, wfOp, size376Entry, sizeMatched, atPC,
    hsize, hzero, hfalse, hcond, hcondLit, UInt256.isTrue,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_enter (input : ByteArray) :
    run enterPath (sizeMatched input) = some (loopState input 0) := by
  have hscan0 : scanAcc input 0 = 0 := rfl
  simp [enterPath, opAt, pushAt, wfOp, sizeMatched, atPC, loopState, hscan0,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
