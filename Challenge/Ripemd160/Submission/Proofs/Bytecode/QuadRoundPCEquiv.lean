import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem pcAfter_eq_add (pc : UInt256)
    (instructions : List YulEvmCompiler.Instr) :
    pcAfter pc instructions =
      pc + UInt256.ofNat ((instructions.map YulEvmCompiler.Instr.size).sum) := by
  induction instructions generalizing pc with
  | nil =>
      change pc = pc + (0 : UInt256)
      exact (Word.add_zero pc).symm
  | cons instruction rest ih =>
      simp only [pcAfter, List.map_cons, List.sum_cons]
      rw [ih, word_add_ofNat_assoc]

theorem legacy_pc_eq_optimized_pc (j : Nat) (hj : j < 5)
    (startPC constant : UInt256) :
    pcAfter startPC (legacyQuadBeforeJumpTemplate j constant) =
      pcAfter startPC (quadBeforeJumpTemplate j constant) := by
  rw [pcAfter_eq_add, pcAfter_eq_add]
  congr 2
  interval_cases j <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
