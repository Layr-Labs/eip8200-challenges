import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubSelectWord
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open CiosCachedMacCore

/-- The source-address rewrite holds for every word, not only boolean selectors. -/
theorem offset (flag : UInt256) :
    (8256 : UInt256) + (115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) * flag =
      (8256 : UInt256) - (1088 : UInt256) * flag := by
  change UInt256.mk ((8256 : Fin UInt256.size) +
    (115792089237316195423570985008687907853269984665640564039457584007913129638848 : Fin UInt256.size) * flag.val) =
    UInt256.mk ((8256 : Fin UInt256.size) - (1088 : Fin UInt256.size) * flag.val)
  have hn : (115792089237316195423570985008687907853269984665640564039457584007913129638848 : Fin UInt256.size) =
      -(1088 : Fin UInt256.size) := by decide
  rw [hn, neg_mul, sub_eq_add_neg]

def positiveProgram : List Instr :=
  [.push 2 1088, .op .MUL, .push 2 8256, .op .SUB]

theorem run_positive (s : State) (pc flag : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1021) :
    runInstructions positiveProgram (framed s pc (flag :: rest)) =
      some (framed s (pc + UInt256.ofNat 8)
        (((8256 : UInt256) - (1088 : UInt256) * flag) :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [positiveProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    framed,hc1,hc2,succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat]

#print axioms offset
#print axioms run_positive
end Challenge.Modexp.Submission.Proofs.Fast.CsubSelectWord
