import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

def gasSteps_test (input : ByteArray) :
    GasSteps (initialState submissionBytecode input 0)
      (stS input 7 [124, UInt256.eq 256 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 0 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 0 0 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 0 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 1 2 256)
    (blockOfS _ (pcFactS input 1 1 _ (by norm_num) (by rfl))
      (stepS_push input 1 2 256 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 2 .EQ)
    (blockOfS _ (pcFactS input 2 4 _ (by norm_num) (by rfl))
      (stepS_eq input 4 256 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 3 1 124)
    (blockOfS _ (pcFactS input 3 5 _ (by norm_num) (by rfl))
      (stepS_push input 5 1 124 [UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_skip (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0) (stS input 8 []) := by
  have hw : (256 : UInt256) ≠ UInt256.ofNat input.size := by
    intro h
    have ht := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))] at ht
    exact hne ht.symm
  have hc : ¬ UInt256.isTrue (UInt256.eq 256 (UInt256.ofNat input.size)) := by
    have hn : (256 : UInt256).toNat ≠ (UInt256.ofNat input.size).toNat :=
      fun h => hw (Challenge.EvmProof.Word.word_ext h)
    simp only [UInt256.eq, if_neg hn, UInt256.isTrue]
    decide
  exact (gasSteps_test input).trans
    (soundS (opAt 4 .JUMPI)
      (blockOfS _ (pcFactS input 4 7 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 7 124 (UInt256.eq 256 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_hit (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (initialState submissionBytecode input 0) (patternedEntry input) := by
  have hc : UInt256.isTrue (UInt256.eq 256 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  have hd : Decode.isValidJumpDest submissionBytecode 124 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 54 (by rfl)
  exact (gasSteps_test input).trans
    (soundS (opAt 4 .JUMPI)
      (blockOfS _ (pcFactS input 4 7 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 7 124 124 (UInt256.eq 256 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc hd)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
