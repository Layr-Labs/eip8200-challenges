import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

def gasSteps_test (input : ByteArray) :
    GasSteps (initialState submissionBytecode input 0)
      (stS input 189 [276, UInt256.eq 256 (UInt256.ofNat input.size)]) := by
  have start : GasSteps (initialState submissionBytecode input 0)
      (stS input 180 []) := Execution.gasSteps_start input
  have jd := soundS (opAt 105 .JUMPDEST)
    (blockOfS _ (pcFactS input 105 180 [] (by norm_num) (by rfl))
      (stepS_jumpdest input 180 [] (by simp) (by norm_num)))
  have a := soundS (opAt 106 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 106 181 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 181 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 107 2 256)
    (blockOfS _ (pcFactS input 107 182 _ (by norm_num) (by rfl))
      (stepS_push input 182 2 256 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 108 .EQ)
    (blockOfS _ (pcFactS input 108 185 _ (by norm_num) (by rfl))
      (stepS_eq input 185 256 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 109 2 276)
    (blockOfS _ (pcFactS input 109 186 _ (by norm_num) (by rfl))
      (stepS_push input 186 2 276 [UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact start.trans (jd.trans (a.trans (b.trans (c.trans d))))

def gasSteps_skip (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 190) := by
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
    (soundS (opAt 110 .JUMPI)
      (blockOfS _ (pcFactS input 110 189 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 189 276 (UInt256.eq 256 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_hit (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (initialState submissionBytecode input 0) (patternedEntry input) := by
  have hc : UInt256.isTrue (UInt256.eq 256 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  have hd : Decode.isValidJumpDest submissionBytecode 276 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 163 (by rfl)
  have jump := soundS (opAt 110 .JUMPI)
    (blockOfS _ (pcFactS input 110 189 _ (by norm_num) (by rfl))
      (stepS_jumpi_taken input 189 276 276 (UInt256.eq 256 (UInt256.ofNat input.size)) []
        (by simp) (by norm_num) rfl hc hd))
  have jd := soundS (opAt 163 .JUMPDEST)
    (blockOfS _ (pcFactS input 163 276 [] (by norm_num) (by rfl))
      (stepS_jumpdest input 276 [] (by simp) (by norm_num)))
  exact (gasSteps_test input).trans (jump.trans jd)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
