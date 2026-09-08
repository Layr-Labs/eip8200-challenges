import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

def sizeFlag (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.eq 128 (UInt256.ofNat input.size))
    (UInt256.eq 256 (UInt256.ofNat input.size))

def gasSteps_test (input : ByteArray) :
    GasSteps (initialState submissionBytecode input 0)
      (stS input 13 [130, sizeFlag input]) := by
  have a := soundS (opAt 0 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 0 0 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 0 [] (by simp) (by norm_num)))
  have b := soundS (opAt 1 (.Dup ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 1 1 _ (by norm_num) (by rfl))
      (stepS_dup input 1 0 (by decide) [UInt256.ofNat input.size]
        (UInt256.ofNat input.size) (by rfl) (by simp) (by norm_num)))
  have c := soundS (pushAt 2 2 256)
    (blockOfS _ (pcFactS input 2 2 _ (by norm_num) (by rfl))
      (stepS_push input 2 2 256 [UInt256.ofNat input.size, UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have d := soundS (opAt 3 .EQ)
    (blockOfS _ (pcFactS input 3 5 _ (by norm_num) (by rfl))
      (stepS_eq input 5 256 (UInt256.ofNat input.size) [UInt256.ofNat input.size]
        (by simp) (by norm_num)))
  have e := soundS (opAt 4 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 4 6 _ (by norm_num) (by rfl))
      (stepS_swap input 6 0 (by decide)
        [UInt256.eq 256 (UInt256.ofNat input.size), UInt256.ofNat input.size]
        [UInt256.ofNat input.size, UInt256.eq 256 (UInt256.ofNat input.size)]
        (by rfl) (by simp) (by norm_num)))
  have f := soundS (pushAt 5 1 128)
    (blockOfS _ (pcFactS input 5 7 _ (by norm_num) (by rfl))
      (stepS_push input 7 1 128
        [UInt256.ofNat input.size, UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 6 .EQ)
    (blockOfS _ (pcFactS input 6 9 _ (by norm_num) (by rfl))
      (stepS_eq input 9 128 (UInt256.ofNat input.size)
        [UInt256.eq 256 (UInt256.ofNat input.size)] (by simp) (by norm_num)))
  have h := soundS (opAt 7 .OR)
    (blockOfS _ (pcFactS input 7 10 _ (by norm_num) (by rfl))
      (stepS_or input 10 (UInt256.eq 128 (UInt256.ofNat input.size))
        (UInt256.eq 256 (UInt256.ofNat input.size)) [] (by simp) (by norm_num)))
  have i := soundS (pushAt 8 1 130)
    (blockOfS _ (pcFactS input 8 11 _ (by norm_num) (by rfl))
      (stepS_push input 11 1 130 [sizeFlag input]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans (h.trans i)))))))

private theorem eq_size_zero (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n < 2 ^ 256) (hne : input.size ≠ n) :
    UInt256.eq (UInt256.ofNat n) (UInt256.ofNat input.size) = 0 := by
  have hw : (UInt256.ofNat n).toNat ≠ (UInt256.ofNat input.size).toNat := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))]
    exact Ne.symm hne
  simp only [UInt256.eq, if_neg hw]
  decide

def gasSteps_skip (input : ByteArray) (hfit : CalldataFits input)
    (hne128 : input.size ≠ 128) (hne256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0) (stS input 14 []) := by
  have hc : ¬ UInt256.isTrue (sizeFlag input) := by
    unfold sizeFlag
    rw [← show UInt256.ofNat 128 = (128 : UInt256) by decide,
      ← show UInt256.ofNat 256 = (256 : UInt256) by decide,
      eq_size_zero input hfit 128 (by norm_num) hne128,
      eq_size_zero input hfit 256 (by norm_num) hne256]
    decide
  exact (gasSteps_test input).trans
    (soundS (opAt 9 .JUMPI)
      (blockOfS _ (pcFactS input 9 13 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 13 130 (sizeFlag input) []
          (by simp) (by norm_num) hc)))

private def gasSteps_hit_of_flag (input : ByteArray)
    (hc : UInt256.isTrue (sizeFlag input)) :
    GasSteps (initialState submissionBytecode input 0) (stS input 130 []) := by
  have hd : Decode.isValidJumpDest submissionBytecode 130 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)
  exact (gasSteps_test input).trans
    (soundS (opAt 9 .JUMPI)
      (blockOfS _ (pcFactS input 9 13 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 13 130 130 (sizeFlag input) []
          (by simp) (by norm_num) rfl hc hd)))

def gasSteps_hit128 (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (initialState submissionBytecode input 0) (stS input 130 []) := by
  apply gasSteps_hit_of_flag input
  unfold sizeFlag
  rw [hsize]
  decide

def gasSteps_hit256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (initialState submissionBytecode input 0) (stS input 130 []) := by
  apply gasSteps_hit_of_flag input
  unfold sizeFlag
  rw [hsize]
  decide

def gasSteps_hit := gasSteps_hit256

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
