import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) (rest : List UInt256) (hlen : rest.length < 1020) :
    GasSteps (stS input 259 rest) (stS input 337 (selected input :: rest)) := by
  have t0 := soundS (opAt 165 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 165 259 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 259 rest (by omega) (by norm_num)))
  have t1 := soundS (opAt 166 (.Dup ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 166 260 (UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_dup input 260 0 (by decide) (UInt256.ofNat input.size :: rest) (UInt256.ofNat input.size) (by rfl) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t2 := soundS (pushAt 167 2 376)
    (blockOfS _ (pcFactS input 167 261 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 261 2 376 (UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t3 := soundS (opAt 168 .EQ)
    (blockOfS _ (pcFactS input 168 264 (376 :: UInt256.ofNat input.size :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_eq input 264 (376) (UInt256.ofNat input.size) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t4 := soundS (pushAt 169 20 digestDifference)
    (blockOfS _ (pcFactS input 169 265 (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_push input 265 20 digestDifference (UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t5 := soundS (opAt 170 .MUL)
    (blockOfS _ (pcFactS input 170 286 (digestDifference :: UInt256.eq (376) (UInt256.ofNat input.size) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_mul input 286 (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) (UInt256.ofNat input.size :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t6 := soundS (opAt 171 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 171 287 (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (by norm_num) (by rfl))
      (stepS_swap input 287 0 (by decide) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: UInt256.ofNat input.size :: rest) (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by rfl) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t7 := soundS (pushAt 172 2 256)
    (blockOfS _ (pcFactS input 172 288 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 288 2 256 (UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t8 := soundS (opAt 173 .EQ)
    (blockOfS _ (pcFactS input 173 291 (256 :: UInt256.ofNat input.size :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_eq input 291 (256) (UInt256.ofNat input.size) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t9 := soundS (pushAt 174 20 digestDifference256)
    (blockOfS _ (pcFactS input 174 292 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_push input 292 20 digestDifference256 (UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t10 := soundS (opAt 175 .MUL)
    (blockOfS _ (pcFactS input 175 313 (digestDifference256 :: UInt256.eq (256) (UInt256.ofNat input.size) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_mul input 313 (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by simp only [List.length_cons]; omega) (by norm_num)))
  have t11 := soundS (opAt 176 .XOR)
    (blockOfS _ (pcFactS input 176 314 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size)) :: UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 314 (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) rest (by omega) (by norm_num)))
  have t12 := soundS (pushAt 177 20 digest1000)
    (blockOfS _ (pcFactS input 177 315 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_push input 315 20 digest1000 (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have t13 := soundS (opAt 178 .XOR)
    (blockOfS _ (pcFactS input 178 336 (digest1000 :: UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size))) :: rest) (by norm_num) (by rfl))
      (stepS_xor input 336 (digest1000) (UInt256.xor (UInt256.mul (digestDifference256) (UInt256.eq (256) (UInt256.ofNat input.size))) (UInt256.mul (digestDifference) (UInt256.eq (376) (UInt256.ofNat input.size)))) rest (by omega) (by norm_num)))
  exact t0.trans (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans (t10.trans (t11.trans (t12.trans (t13)))))))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
