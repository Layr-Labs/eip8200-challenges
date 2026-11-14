import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.Arithmetic
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
theorem addC (a b : UInt256) : a + b = b + a := Challenge.EvmProof.Word.word_add_comm a b
theorem mulC (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [mul_comm]
theorem addA (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((a.val + b.val) + c.val).val = (a.val + (b.val + c.val)).val
  rw [add_assoc]
theorem addL (a b c : UInt256) : a + (b + c) = b + (a + c) := by
  rw [← addA,addC a b,addA]
theorem mmC (a b m : UInt256) : UInt256.mulMod a b m = UInt256.mulMod b a m := by
  simp [UInt256.mulMod,Nat.mul_comm]
theorem amC (a b m : UInt256) : UInt256.addMod a b m = UInt256.addMod b a m := by
  simp [UInt256.addMod,Nat.add_comm]
theorem andC (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val &&& b.val).val = (b.val &&& a.val).val
  simp only [Fin.and_val,Nat.and_comm]
theorem orC (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ||| b.val).val = (b.val ||| a.val).val
  simp only [Fin.or_val,Nat.or_comm]
theorem xorC (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  simp only [Fin.xor_val,Nat.xor_comm]
theorem eqC (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  simp [UInt256.eq,eq_comm]
theorem read_disjoint (mem : ByteArray) (v : UInt256) (a b : Nat)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) b) a =
    MachineState.readWord mem a := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h
#print axioms read_disjoint
end CycleSubmission.Prepared.Arithmetic
