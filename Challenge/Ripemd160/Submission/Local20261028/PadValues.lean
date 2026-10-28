import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadValues
open EvmSemantics PairedLaneUInt256Bridge
def load (n : UInt256) (address : Nat) : UInt256 := match address with
  | 36 => UInt256.ofNat 128
  | 54 => UInt256.ofNat 2854495385411919762116571938898990272765493376
  | 72 => UInt256.ofNat 2854495385411919762116571938898990272765493248
  | 144 => UInt256.shiftLeft n (UInt256.ofNat 3)
  | 162 => UInt256.mul (UInt256.ofNat (8+2^147)) n
  | 180 => UInt256.shiftLeft n (UInt256.ofNat 147)
  | 522 => UInt256.ofNat 128
  | 540 => UInt256.ofNat 2854495385411919762116571938898990272765493248
  | 666 => UInt256.shiftLeft n (UInt256.ofNat 3)
  | 684 => UInt256.shiftLeft n (UInt256.ofNat 147)
  | _ => UInt256.ofNat 0
@[simp] theorem add_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply bits_injective
  simp [bits_add, bits_ofNat]
@[simp] theorem zero_add (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  rw [StaggerCoreCommon.add_comm, add_zero]
@[simp] theorem xor_zero (a : UInt256) : UInt256.xor a (UInt256.ofNat 0) = a := by
  apply bits_injective
  simp [bits_xor, bits_ofNat]
@[simp] theorem zero_xor (a : UInt256) : UInt256.xor (UInt256.ofNat 0) a = a := by
  rw [StaggerCoreCommon.xor_comm, xor_zero]
theorem fold_one (x : UInt256) :
    UInt256.add (UInt256.ofNat 2854495385411919762116571938898990272765493248)
      (UInt256.add (UInt256.ofNat 34535016170389834383797866734609369064725061767952793) x) =
    UInt256.add (UInt256.ofNat 34535019024885219795717628851181307963715334533446041) x := by
  rw [← StaggerCoreCommon.add_assoc]
  rfl
theorem fold_two (x : UInt256) :
    UInt256.add (UInt256.ofNat 2854495385411919762116571938898990272765493376)
      (UInt256.add (UInt256.ofNat 136726760529788758926252426176837954510549114783656865) x) =
    UInt256.add (UInt256.ofNat 136726763384284144338172188293409893409539387549150241) x := by
  rw [← StaggerCoreCommon.add_assoc]
  rfl
#print axioms add_zero
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadValues
