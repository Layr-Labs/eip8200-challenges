import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 409 []) (stS input 458 [selected input]) := by
  have a := soundS (opAt 251 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 251 409 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 409 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 252 2 376)
    (blockOfS _ (pcFactS input 252 410 _ (by norm_num) (by rfl))
      (stepS_push input 410 2 376 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 253 .EQ)
    (blockOfS _ (pcFactS input 253 413 _ (by norm_num) (by rfl))
      (stepS_eq input 413 376 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 254 20 digestDifference)
    (blockOfS _ (pcFactS input 254 414 _ (by norm_num) (by rfl))
      (stepS_push input 414 20 digestDifference
        [UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 255 .MUL)
    (blockOfS _ (pcFactS input 255 435 _ (by norm_num) (by rfl))
      (stepS_mul input 435 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 256 20 digest1000)
    (blockOfS _ (pcFactS input 256 436 _ (by norm_num) (by rfl))
      (stepS_push input 436 20 digest1000
        [digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 257 .XOR)
    (blockOfS _ (pcFactS input 257 457 _ (by norm_num) (by rfl))
      (stepS_xor input 457 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
