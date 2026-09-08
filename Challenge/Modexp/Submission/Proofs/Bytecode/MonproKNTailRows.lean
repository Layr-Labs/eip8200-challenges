import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTail
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNExit
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNPointers

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailRows

open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNTailDefs
open MonproKNTail MonproKNExit MonproKNPointers
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem pointer_next (base i : Nat) :
    negative32 + UInt256.ofNat (ptrAt base i) = UInt256.ofNat (ptrAt base (i+1)) := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    negative32_value
  rw [hK, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

theorem run_next (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 < n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 1982 = true) :
    runInstructions tailProgram
      (MonproKNRowFrames.tail s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (MonproKNRowFrames.outer s (tailMem mem c) pa pb n (i+1) dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) :=
    (l1_condition pb n (i+1) hpb hpbFit (by omega)).mpr hi
  have trace := run_tail { s with memory := mem } pmj ptj c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
    dst ret rest hcap hact htarget
  simpa only [input, result, baseStack, framed, MonproKNRowFrames.tail,
    MonproKNRowFrames.outer, hp, if_pos hcond, List.cons_append, List.nil_append] using trace

theorem run_last (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 1982 = true) :
    runInstructions tailProgram
      (MonproKNRowFrames.tail s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (MonproKNRowFrames.exit s (tailMem mem c)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb dst ret rest) := by
  have hp := pointer_next (pb+32*n-32) i
  have hcond : ¬UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) := by
    rw [l1_condition pb n (i+1) hpb hpbFit (by omega)]
    omega
  have trace := run_tail { s with memory := mem } pmj ptj c mu bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
    dst ret rest hcap hact htarget
  simpa only [input, result, baseStack, framed, MonproKNRowFrames.tail,
    MonproKNRowFrames.exit, hp, if_neg hcond, List.cons_append, List.nil_append] using trace

theorem run_last_exit (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 1982 = true)
    (hcsub : Decode.isValidJumpDest s.executionEnv.code 2655 = true) :
    runInstructions (tailProgram ++ exitProgram)
      (MonproKNRowFrames.tail s mem pmj ptj c mu bi pa pb n i dst ret rest) =
    some (MonproKNRowFrames.csub s (tailMem mem c) dst ret rest) :=
  runInstructions_append_some _ _ _ _ _
    (run_last s mem pmj ptj c mu bi pa pb n i dst ret rest hcap hact hpb hpbFit hi htarget)
    (run_exit { s with memory := tailMem mem c }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32))
      dst ret rest hcap hcsub)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailRows
