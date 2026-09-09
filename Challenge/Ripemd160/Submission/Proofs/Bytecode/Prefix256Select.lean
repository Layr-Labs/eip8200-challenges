import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan Prefix256Value

def gasSteps_select (input : ByteArray) (rest : List UInt256) (hlen : rest.length < 1020) :
    GasSteps (stS input 423 rest) (stS input 472 (selected input :: rest)) := by
  have a := soundS (opAt 259 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 259 423 rest (by norm_num) (by rfl))
      (stepS_calldatasize input 423 rest (by omega) (by norm_num)))
  have b := soundS (pushAt 260 2 376)
    (blockOfS _ (pcFactS input 260 424 _ (by norm_num) (by rfl))
      (stepS_push input 424 2 376 (UInt256.ofNat input.size :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 261 .EQ)
    (blockOfS _ (pcFactS input 261 427 _ (by norm_num) (by rfl))
      (stepS_eq input 427 376 (UInt256.ofNat input.size) rest (by omega) (by norm_num)))
  have d := soundS (pushAt 262 20 digestDifference)
    (blockOfS _ (pcFactS input 262 428 _ (by norm_num) (by rfl))
      (stepS_push input 428 20 digestDifference
        (UInt256.eq 376 (UInt256.ofNat input.size) :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 263 .MUL)
    (blockOfS _ (pcFactS input 263 449 _ (by norm_num) (by rfl))
      (stepS_mul input 449 digestDifference (UInt256.eq 376 (UInt256.ofNat input.size))
        rest (by omega) (by norm_num)))
  have f := soundS (pushAt 264 20 digest1000)
    (blockOfS _ (pcFactS input 264 450 _ (by norm_num) (by rfl))
      (stepS_push input 450 20 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size) :: rest)
        (by simp only [List.length_cons]; omega) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 265 .XOR)
    (blockOfS _ (pcFactS input 265 471 _ (by norm_num) (by rfl))
      (stepS_xor input 471 digest1000
        (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size))
        rest (by omega) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
