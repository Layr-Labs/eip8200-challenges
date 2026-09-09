import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 404 []) (stS input 453 [selected input]) := by
  have a := soundS (opAt 245 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 245 404 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 404 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 246 2 376)
    (blockOfS _ (pcFactS input 246 405 _ (by norm_num) (by rfl))
      (stepS_push input 405 2 376 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 247 .EQ)
    (blockOfS _ (pcFactS input 247 408 _ (by norm_num) (by rfl))
      (stepS_eq input 408 376 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 248 20 digestDifference)
    (blockOfS _ (pcFactS input 248 409 _ (by norm_num) (by rfl))
      (stepS_push input 409 20 digestDifference
        [UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 249 .MUL)
    (blockOfS _ (pcFactS input 249 430 _ (by norm_num) (by rfl))
      (stepS_mul input 430 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 250 20 digest1000)
    (blockOfS _ (pcFactS input 250 431 _ (by norm_num) (by rfl))
      (stepS_push input 431 20 digest1000
        [digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 251 .XOR)
    (blockOfS _ (pcFactS input 251 452 _ (by norm_num) (by rfl))
      (stepS_xor input 452 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
