import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
open EvmSemantics Challenge.EvmProof
namespace CycleSubmission.Global.DirectR5Subtract32
theorem identity (x : UInt256) :
 UInt256.ofNat (2^256-32)+x = x-UInt256.ofNat 32 := by
 apply Word.word_ext
 rw [Word.word_toNat_add,Word.word_toNat_sub]
 have hn : (UInt256.ofNat (2^256-32)).toNat = 2^256-32 := by decide
 have hk : (UInt256.ofNat 32).toNat = 32 := by decide
 rw [hn,hk]
 congr 1
 omega
theorem lnot_identity (x : UInt256) :
 UInt256.lnot (UInt256.ofNat 31)+x = x-UInt256.ofNat 32 := by
 have hn : UInt256.ofNat (2^256-32) = UInt256.lnot (UInt256.ofNat 31) := by decide
 simpa only [hn] using identity x
#print axioms identity
end CycleSubmission.Global.DirectR5Subtract32
