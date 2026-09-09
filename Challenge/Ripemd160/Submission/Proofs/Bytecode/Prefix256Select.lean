import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 407 []) (stS input 456 [selected input]) := by
  have a := soundS (opAt 248 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 248 407 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 407 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 249 2 376)
    (blockOfS _ (pcFactS input 249 408 _ (by norm_num) (by rfl))
      (stepS_push input 408 2 376 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 250 .EQ)
    (blockOfS _ (pcFactS input 250 411 _ (by norm_num) (by rfl))
      (stepS_eq input 411 376 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 251 20 digestDifference)
    (blockOfS _ (pcFactS input 251 412 _ (by norm_num) (by rfl))
      (stepS_push input 412 20 digestDifference
        [UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 252 .MUL)
    (blockOfS _ (pcFactS input 252 433 _ (by norm_num) (by rfl))
      (stepS_mul input 433 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 253 20 digest1000)
    (blockOfS _ (pcFactS input 253 434 _ (by norm_num) (by rfl))
      (stepS_push input 434 20 digest1000
        [digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 254 .XOR)
    (blockOfS _ (pcFactS input 254 455 _ (by norm_num) (by rfl))
      (stepS_xor input 455 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
