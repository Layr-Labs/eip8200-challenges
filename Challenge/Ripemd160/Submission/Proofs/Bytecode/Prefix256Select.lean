import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 441 []) (stS input 490 [selected input]) := by
  have a := soundS (opAt 276 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 276 441 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 441 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 277 2 376)
    (blockOfS _ (pcFactS input 277 442 _ (by norm_num) (by rfl))
      (stepS_push input 442 2 376 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 278 .EQ)
    (blockOfS _ (pcFactS input 278 445 _ (by norm_num) (by rfl))
      (stepS_eq input 445 376 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 279 20 digestDifference)
    (blockOfS _ (pcFactS input 279 446 _ (by norm_num) (by rfl))
      (stepS_push input 446 20 digestDifference
        [UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 280 .MUL)
    (blockOfS _ (pcFactS input 280 467 _ (by norm_num) (by rfl))
      (stepS_mul input 467 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 281 20 digest1000)
    (blockOfS _ (pcFactS input 281 468 _ (by norm_num) (by rfl))
      (stepS_push input 468 20 digest1000
        [digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 282 .XOR)
    (blockOfS _ (pcFactS input 282 489 _ (by norm_num) (by rfl))
      (stepS_xor input 489 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
