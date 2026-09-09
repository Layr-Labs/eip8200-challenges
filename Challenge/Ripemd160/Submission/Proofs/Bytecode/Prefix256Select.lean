import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 423 []) (stS input 472 [selected input]) := by
  have a := soundS (opAt 253 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 253 423 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 423 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 254 2 256)
    (blockOfS _ (pcFactS input 254 424 _ (by norm_num) (by rfl))
      (stepS_push input 424 2 256 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 255 .EQ)
    (blockOfS _ (pcFactS input 255 427 _ (by norm_num) (by rfl))
      (stepS_eq input 427 256 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 256 20 digestDifference)
    (blockOfS _ (pcFactS input 256 428 _ (by norm_num) (by rfl))
      (stepS_push input 428 20 digestDifference
        [UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 257 .MUL)
    (blockOfS _ (pcFactS input 257 449 _ (by norm_num) (by rfl))
      (stepS_mul input 449 digestDifference (UInt256.eq 256 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 258 20 digest1000)
    (blockOfS _ (pcFactS input 258 450 _ (by norm_num) (by rfl))
      (stepS_push input 450 20 digest1000
        [digestDifference * UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 259 .XOR)
    (blockOfS _ (pcFactS input 259 471 _ (by norm_num) (by rfl))
      (stepS_xor input 471 digest1000
        (digestDifference * UInt256.eq 256 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
