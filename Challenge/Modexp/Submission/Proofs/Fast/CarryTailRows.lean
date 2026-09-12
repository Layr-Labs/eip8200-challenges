import Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedExit
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedTailDefs
open CarryRowRun CiosCachedExit CiosCachedPointers CarryRowModel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem pointer_next (base i : Nat) :
    negative32 + UInt256.ofNat (ptrAt base i) = UInt256.ofNat (ptrAt base (i+1)) := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    negative32_value
  rw [hK, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

theorem run_next (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 < n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions CarryRowPrograms.tail
      (CiosCached.tailState s mem c mu bi pb n i hd ent dst ret rest) =
    some (CiosCached.outState s (tailCarry mem c bi) pb n (i+1) hd ent dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) :=
    (l1_condition pb n (i+1) hpb hpbFit (by omega)).mpr hi
  have trace := CarryRowRun.run_tail { s with memory := mem } c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target n) dst (ret :: rest) (by simp only [List.length_cons]; omega) hact htarget
  simpa only [List.cons_append, List.nil_append, input, result, baseStack, framed, CiosCached.tailState,
    CiosCached.outState, hp, if_pos hcond, List.cons_append, List.nil_append] using trace

theorem run_last (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions CarryRowPrograms.tail
      (CiosCached.tailState s mem c mu bi pb n i hd ent dst ret rest) =
    some (exitState s (tailCarry mem c bi)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n hd ent dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : ¬UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) := by
    rw [l1_condition pb n (i+1) hpb hpbFit (by omega)]
    omega
  have trace := CarryRowRun.run_tail { s with memory := mem } c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target n) dst (ret :: rest) (by simp only [List.length_cons]; omega) hact htarget
  simpa only [List.cons_append, List.nil_append, input, result, baseStack, framed, CiosCached.tailState,
    exitState, hp, if_neg hcond, List.cons_append, List.nil_append] using trace

end Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
