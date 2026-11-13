import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Boolean
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PrepWordLiterals
open EvmSemantics
open PairedLaneUInt256Bridge Challenge.Ripemd160.Submission.Proofs.Bytecode
theorem pair : Paired144WordRound.pairWord =
    UInt256.ofNat 95780971281817308448866066055358605703522837925462015 := by decide +kernel
theorem upper_pack : word (Paired144Core.pack (0#32) (4294967295#32)) =
    UInt256.ofNat 95780971281817308448866066055358605703522833630494720 := by decide +kernel
theorem upper_mask : word Paired144Boolean.upperMask =
    UInt256.ofNat 95780971281817308448866066055358605703522833630494720 := by decide +kernel
theorem lower_pack : word (Paired144Core.pack (4294967295#32) (0#32)) =
    UInt256.ofNat 4294967295 := by decide +kernel
theorem lower_mask : word Paired144Boolean.lowerMask =
    UInt256.ofNat 4294967295 := by decide +kernel
#print axioms pair
#print axioms upper_pack
#print axioms upper_mask
#print axioms lower_pack
#print axioms lower_mask
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PrepWordLiterals
