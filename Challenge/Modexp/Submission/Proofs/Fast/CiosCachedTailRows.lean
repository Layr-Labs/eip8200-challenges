import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTail
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedExit
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailRows

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedTailDefs
open CiosCachedTail CiosCachedExit CiosCachedPointers
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem pointer_next (base i : Nat) :
    negative32 + UInt256.ofNat (ptrAt base i) = UInt256.ofNat (ptrAt base (i+1)) := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    negative32_value
  rw [hK, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

theorem run_next (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 < n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4251 = true) :
    runInstructions tailLoopProgram
      (CiosCached.tailState s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (CiosCached.outState s (tailMem mem c) pa pb n (i+1) dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) :=
    (l1_condition pb n (i+1) hpb hpbFit (by omega)).mpr hi
  have trace := run_tail { s with memory := mem } pmj ptj c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
    (isFour n) dst ret rest hcap hact htarget
  simpa only [input, result, baseStack, framed, CiosCached.tailState,
    CiosCached.outState, hp, if_pos hcond, List.cons_append, List.nil_append] using trace

theorem run_last (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4251 = true) :
    runInstructions tailLoopProgram
      (CiosCached.tailState s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (exitState s (tailMem mem c)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb n dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : ¬UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) := by
    rw [l1_condition pb n (i+1) hpb hpbFit (by omega)]
    omega
  have trace := run_tail { s with memory := mem } pmj ptj c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
    (isFour n) dst ret rest hcap hact htarget
  simpa only [input, result, baseStack, framed, CiosCached.tailState,
    exitState, hp, if_neg hcond, List.cons_append, List.nil_append] using trace

theorem run_last_exit (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4251 = true)
    (hcsub : Decode.isValidJumpDest s.executionEnv.code 2292 = true) :
    runInstructions (tailLoopProgram ++ exitProgram)
      (CiosCached.tailState s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (mpCsubState s (tailMem mem c) dst ret rest) :=
  runInstructions_append_some _ _ _ _ _
    (run_last s mem pmj ptj c mu bi pa pb n i dst ret rest hcap hact hpb hpbFit hi htarget)
    (run_exit { s with memory := tailMem mem c }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
      (isFour n) dst ret rest hcap hcsub)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailRows
