import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) (rest : List UInt256) (hlen : rest.length < 1020) :
    GasSteps (stS input 268 rest) (stS input 346 (selected input :: rest)) := by
  have t0 := soundS (opAt 171 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 171 268 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 268 rest (by omega) (by norm_num)))
  have t1 := soundS (opAt 172 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 172 269 (UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_calldatasize input 269 (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t2 := soundS (pushAt 173 2 376)
    (blockOfS _ (pcFactS input 173 270 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 270 2 376 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t3 := soundS (opAt 174 .EQ)
    (blockOfS _ (pcFactS input 174 273 (376 :: UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_eq input 273 (376) (UInt256.ofNat input.size) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t4 := soundS (pushAt 175 20 digestDifference)
    (blockOfS _ (pcFactS input 175 274 (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 274 20 digestDifference (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t5 := soundS (opAt 176 .MUL)
    (blockOfS _ (pcFactS input 176 295 (digestDifference :: UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_mul input 295 (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t6 := soundS (opAt 177 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 177 296 (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_swap input 296 0 (by decide) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by rfl) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t7 := soundS (pushAt 178 2 256)
    (blockOfS _ (pcFactS input 178 297 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 297 2 256 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t8 := soundS (opAt 179 .EQ)
    (blockOfS _ (pcFactS input 179 300 (256 :: UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_eq input 300 (256) (UInt256.ofNat input.size) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t9 := soundS (pushAt 180 20 digestDifference256)
    (blockOfS _ (pcFactS input 180 301 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 301 20 digestDifference256 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t10 := soundS (opAt 181 .MUL)
    (blockOfS _ (pcFactS input 181 322 (digestDifference256 :: UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_mul input 322 (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t11 := soundS (opAt 182 .XOR)
    (blockOfS _ (pcFactS input 182 323 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 323 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) rest (by omega) (by norm_num)))
  have t12 := soundS (pushAt 183 20 digest1000)
    (blockOfS _ (pcFactS input 183 324 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_push input 324 20 digest1000 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t13 := soundS (opAt 184 .XOR)
    (blockOfS _ (pcFactS input 184 345 (digest1000 :: UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 345 (digest1000) (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)))) rest (by omega) (by norm_num)))
  exact t0.trans (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans (t10.trans (t11.trans (t12.trans (t13)))))))))))))

def gasSteps_skip128 (input : ByteArray) (rest : List UInt256)
    (hfit : CalldataFits input) (hlen : rest.length < 1020)
    (hsize : input.size ≠ 128) :
    GasSteps (stS input 260 rest) (stS input 268 rest) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsize' : 128 ≠ input.size := Ne.symm hsize
  have heq : UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
    simp [hsize']
  have hfalse : ¬ UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size)) := by
    rw [heq]
    decide
  have t0 := soundS (opAt 166 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 166 260 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 260 rest (by omega) (by norm_num)))
  have t1 := soundS (pushAt 167 1 128)
    (blockOfS _ (pcFactS input 167 261 (UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 261 1 128 (UInt256.ofNat input.size :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t2 := soundS (opAt 168 .EQ)
    (blockOfS _ (pcFactS input 168 263 (128 :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_eq input 263 128 (UInt256.ofNat input.size) rest
        (by omega) (by norm_num)))
  have t3 := soundS (pushAt 169 2 5287)
    (blockOfS _ (pcFactS input 169 264 (UInt256.eq 128 (UInt256.ofNat input.size) :: rest) (by norm_num) (by rfl))
      (stepS_push input 264 2 5287 (UInt256.eq 128 (UInt256.ofNat input.size) :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t4 := soundS (opAt 170 .JUMPI)
    (blockOfS _ (pcFactS input 170 267 (5287 :: UInt256.eq 128 (UInt256.ofNat input.size) :: rest) (by norm_num) (by rfl))
      (stepS_jumpi_fall input 267 5287 (UInt256.eq 128 (UInt256.ofNat input.size)) rest
        (by omega) (by norm_num) hfalse))
  exact t0.trans (t1.trans (t2.trans (t3.trans t4)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
