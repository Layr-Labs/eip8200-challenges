import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedSizeFlag
open EvmSemantics Challenge.EvmProof
abbrev reversedMask : UInt256 := UInt256.ofNat 28948022349768971278010700369584604374341282260324016856826403983149888438272
abbrev lowMask : UInt256 := UInt256.ofNat 342276208914615837337402008677671501826
private theorem small : ∀ i : Fin 256,
    UInt256.slt (UInt256.shiftLeft reversedMask (UInt256.ofNat i.val)) (UInt256.ofNat 0) =
      UInt256.land (UInt256.ofNat 1) (UInt256.shiftRight lowMask (UInt256.ofNat i.val)) := by decide
/-- Exact universal flag, including all shifts >=256, with no calldata-fit hypothesis. -/
theorem flag (x : UInt256) :
    UInt256.slt (UInt256.shiftLeft reversedMask x) (UInt256.ofNat 0) =
      UInt256.land (UInt256.ofNat 1) (UInt256.shiftRight lowMask x) := by
 by_cases h : x.toNat < 256
 · have hi := small ⟨x.toNat,h⟩
   rw [← Word.word_eq_ofNat_toNat x] at hi
   exact hi
 · have hb : x.toNat ≥ 256 := by omega
   simp only [UInt256.shiftLeft,UInt256.shiftRight,if_pos hb]
   decide
#print axioms flag
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedSizeFlag
