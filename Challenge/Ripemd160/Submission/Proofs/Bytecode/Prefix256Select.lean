import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) (rest : List UInt256) (hlen : rest.length < 1020) :
    GasSteps (stS input 269 rest) (stS input 347 (selected input :: rest)) := by
  have t0 := soundS (opAt 165 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 165 269 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 269 rest (by omega) (by norm_num)))
  have t1 := soundS (opAt 166 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 166 270 (UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_calldatasize input 270 (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t2 := soundS (pushAt 167 2 376)
    (blockOfS _ (pcFactS input 167 271 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 271 2 376 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t3 := soundS (opAt 168 .EQ)
    (blockOfS _ (pcFactS input 168 274 (376 :: UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_eq input 274 (376) (UInt256.ofNat input.size) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t4 := soundS (pushAt 169 20 digestDifference)
    (blockOfS _ (pcFactS input 169 275 (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 275 20 digestDifference (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t5 := soundS (opAt 170 .MUL)
    (blockOfS _ (pcFactS input 170 296 (digestDifference :: UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_mul input 296 (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t6 := soundS (opAt 171 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 171 297 (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_swap input 297 0 (by decide) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by rfl) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t7 := soundS (pushAt 172 2 256)
    (blockOfS _ (pcFactS input 172 298 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 298 2 256 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t8 := soundS (opAt 173 .EQ)
    (blockOfS _ (pcFactS input 173 301 (256 :: UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_eq input 301 (256) (UInt256.ofNat input.size) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t9 := soundS (pushAt 174 20 digestDifference256)
    (blockOfS _ (pcFactS input 174 302 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 302 20 digestDifference256 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t10 := soundS (opAt 175 .MUL)
    (blockOfS _ (pcFactS input 175 323 (digestDifference256 :: UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_mul input 323 (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t11 := soundS (opAt 176 .XOR)
    (blockOfS _ (pcFactS input 176 324 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 324 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) rest (by omega) (by norm_num)))
  have t12 := soundS (pushAt 177 20 digest1000)
    (blockOfS _ (pcFactS input 177 325 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_push input 325 20 digest1000 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t13 := soundS (opAt 178 .XOR)
    (blockOfS _ (pcFactS input 178 346 (digest1000 :: UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 346 (digest1000) (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)))) rest (by omega) (by norm_num)))
  exact t0.trans (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans (t10.trans (t11.trans (t12.trans (t13)))))))))))))

def gasSteps_skip128 (input : ByteArray) (rest : List UInt256)
    (hfit : CalldataFits input) (hlen : rest.length < 1020)
    (hsize : 129 ≤ input.size) :
    GasSteps (stS input 261 rest) (stS input 269 rest) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have heq : UInt256.gt (UInt256.ofNat 129) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
    unfold UInt256.gt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
    simp [show ¬ (129 > input.size) by omega]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.gt (UInt256.ofNat 129) (UInt256.ofNat input.size)) := by
    rw [heq]
    decide
  have t0 := soundS (opAt 160 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 160 261 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 261 rest (by omega) (by norm_num)))
  have t1 := soundS (pushAt 161 1 129)
    (blockOfS _ (pcFactS input 161 262 (UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 262 1 129 (UInt256.ofNat input.size :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t2 := soundS (opAt 162 .GT)
    (blockOfS _ (pcFactS input 162 264 (129 :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_gt input 264 129 (UInt256.ofNat input.size) rest
        (by omega) (by norm_num)))
  have t3 := soundS (pushAt 163 2 5197)
    (blockOfS _ (pcFactS input 163 265 (UInt256.gt 129 (UInt256.ofNat input.size) :: rest) (by norm_num) (by rfl))
      (stepS_push input 265 2 5197 (UInt256.gt 129 (UInt256.ofNat input.size) :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t4 := soundS (opAt 164 .JUMPI)
    (blockOfS _ (pcFactS input 164 268 (5197 :: UInt256.gt 129 (UInt256.ofNat input.size) :: rest) (by norm_num) (by rfl))
      (stepS_jumpi_fall input 268 5197 (UInt256.gt 129 (UInt256.ofNat input.size)) rest
        (by omega) (by norm_num) hfalse))
  exact t0.trans (t1.trans (t2.trans (t3.trans t4)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
