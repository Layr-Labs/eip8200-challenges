import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosCachedPointers
open CiosAccumulatorMemory

theorem pointer_next (base i : Nat) :
    negative32 + UInt256.ofNat (ptrAt base i) = UInt256.ofNat (ptrAt base (i+1)) := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    negative32_value
  rw [hK, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

def exitState (s : State) (mem : ByteArray) (slot pbi : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4885)
    ([pbi,UInt256.ofNat pa,UInt256.ofNat (pb-32),l1Target n,slot,allOnes,l2Target n,dst,ret] ++ rest)

theorem run_next (s : State) (mem : ByteArray) (c mu bit t : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 < n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4252 = true) :
    runInstructions CiosAccumulatorTrace.tailLoopProgram
      (tailState (carrySlot := t) s mem c mu bit pa pb n i dst ret rest) =
    some (outState (carrySlot := t) s (tailWithTN mem c bit t) pa pb n (i+1) dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) :=
    (l1_condition pb n (i+1) hpb hpbFit (by omega)).mpr hi
  have trace := CiosAccumulatorTrace.run_tail {s with memory := mem} c mu bit
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (l1Target n) t (allOnes :: l2Target n :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact htarget
  simpa only [framed,tailState,outState,hp,if_pos hcond,List.cons_append,List.nil_append] using trace

theorem run_last (s : State) (mem : ByteArray) (c mu bit t : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4252 = true) :
    runInstructions CiosAccumulatorTrace.tailLoopProgram
      (tailState (carrySlot := t) s mem c mu bit pa pb n i dst ret rest) =
    some (exitState s (tailWithTN mem c bit t) t
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb n dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : ¬UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) := by
    rw [l1_condition pb n (i+1) hpb hpbFit (by omega)]
    omega
  have trace := CiosAccumulatorTrace.run_tail {s with memory := mem} c mu bit
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (l1Target n) t (allOnes :: l2Target n :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact htarget
  simpa only [framed,tailState,exitState,hp,if_neg hcond,List.cons_append,List.nil_append] using trace

#print axioms run_next
#print axioms run_last
end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
