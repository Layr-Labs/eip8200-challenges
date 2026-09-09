import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) :
    GasSteps (stS input 417 []) (stS input 466 [selected input]) := by
  have a := soundS (opAt 249 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 249 417 [] (by norm_num) (by rfl))
      (stepS_calldatasize input 417 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 250 2 256)
    (blockOfS _ (pcFactS input 250 418 _ (by norm_num) (by rfl))
      (stepS_push input 418 2 256 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 251 .EQ)
    (blockOfS _ (pcFactS input 251 421 _ (by norm_num) (by rfl))
      (stepS_eq input 421 256 (UInt256.ofNat input.size) [] (by simp) (by norm_num)))
  have d := soundS (pushAt 252 20 digestDifference)
    (blockOfS _ (pcFactS input 252 422 _ (by norm_num) (by rfl))
      (stepS_push input 422 20 digestDifference
        [UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 253 .MUL)
    (blockOfS _ (pcFactS input 253 443 _ (by norm_num) (by rfl))
      (stepS_mul input 443 digestDifference (UInt256.eq 256 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  have f := soundS (pushAt 254 20 digest1000)
    (blockOfS _ (pcFactS input 254 444 _ (by norm_num) (by rfl))
      (stepS_push input 444 20 digest1000
        [digestDifference * UInt256.eq 256 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 255 .XOR)
    (blockOfS _ (pcFactS input 255 465 _ (by norm_num) (by rfl))
      (stepS_xor input 465 digest1000
        (digestDifference * UInt256.eq 256 (UInt256.ofNat input.size))
        [] (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
