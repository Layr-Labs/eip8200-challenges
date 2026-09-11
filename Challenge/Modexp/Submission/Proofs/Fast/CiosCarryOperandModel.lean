import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryOperand
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosOperandCache
variable {carrySlot : UInt256}

theorem run_model (slot : Fin 3) (pc : Nat) (off t : UInt256)
    (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (tl inv m0 aEnd a96 a64 a32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hfour : 4 ≤ n) (hj : j < n)
    (hoff : off.toNat = 32*(n-1-j)) (hselect : off.toNat = cacheAddress slot)
    (ht : t.toNat = 8256+32*(n-1-j)) (hpaFit : pa+32*n ≤ 8192)
    (hc : OperandCache mem pa n a96 a64 a32 aEnd) :
    runInstructions (CiosCarryOperand.extraProgram slot t)
      (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j inv m0 (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) =
    some (l1At (carrySlot := carrySlot) (pc+34) s mem bi pa pb n i (j+1) inv m0
      (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) := by
  have h := CiosCarryOperand.run_step (carrySlot := carrySlot) slot s (UInt256.ofNat pc) mem bi pa n j off t hoff hselect ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n)
    inv m0 tl a96 a64 a32 aEnd dst ret rest hcap hact hn hfour hj hpaFit hc
  simpa only [List.cons_append,List.nil_append,CiosCarryL1.state,l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h


theorem run_wide_model (pc : Nat) (off t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472) :
    runInstructions (CiosCarryOperand.wideProgram off t) (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j pdst ret rest) =
      some (l1At (carrySlot := carrySlot) (pc+42) s mem bi pa pb n i (j+1) pdst ret rest) := by
  have h := CiosCarryOperand.run_wide_step (carrySlot := carrySlot) s (UInt256.ofNat pc) mem bi pa n j off t hoff ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) pdst (ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hj hpa hpaFit
  simpa only [List.cons_append, List.nil_append, CiosCarryL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h


end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
