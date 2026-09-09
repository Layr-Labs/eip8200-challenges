import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 406 []) (stS input 455 [selected input]) := by
  have a := soundS (opAt 246 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 246 406 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 406 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 247 2 376)
    (blockOfS _ (pcFactS input 247 407 _ (by norm_num) (by rfl))
      (stepS_push input 407 2 376 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 248 .EQ)
    (blockOfS _ (pcFactS input 248 410 _ (by norm_num) (by rfl))
      (stepS_eq input 410 376 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 249 20 digestDifference)
    (blockOfS _ (pcFactS input 249 411 _ (by norm_num) (by rfl))
      (stepS_push input 411 20 digestDifference
        [UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 250 .MUL)
    (blockOfS _ (pcFactS input 250 432 _ (by norm_num) (by rfl))
      (stepS_mul input 432 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 251 20 digest1000)
    (blockOfS _ (pcFactS input 251 433 _ (by norm_num) (by rfl))
      (stepS_push input 433 20 digest1000
        [digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 252 .XOR)
    (blockOfS _ (pcFactS input 252 454 _ (by norm_num) (by rfl))
      (stepS_xor input 454 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
