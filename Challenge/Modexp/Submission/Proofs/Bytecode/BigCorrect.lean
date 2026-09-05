import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # End-to-end functional correctness of the multi-limb MODEXP arithmetic -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigCorrect

open EvmSemantics
open EvmSemantics.EVM

theorem exponentProgress_represents_result (input : ByteArray)
    (returnDest : UInt256) (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    let b := baseSize input
    let e := exponentSize input
    let m := modulusSize input
    let expOff := Word.expOffset input
    let modOff := Word.modulusOffset input
    let progress := BigComplete.exponentProgressState (Main.headerState input)
      b e m 96 expOff modOff returnDest rest
    Limbs.Represents progress.memory 2048 (Limbs.limbCount m)
      (Precompile.modPow (WordCorrect.baseNat input)
        (WordCorrect.exponentNat input) (Word.modulusValue input)) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let n := Limbs.limbCount m
  let header := Main.headerState input
  let entry := BigComplete.exponentState header b e m 96 expOff modOff
    returnDest rest
  let accumulator := BigComplete.modulusOr header b e m 96 expOff modOff
    returnDest rest
  let expTail := BigComplete.exponentRest modOff returnDest rest
  let beta := WordCorrect.baseNat input % Word.modulusValue input
  let phase := BigExponent.exponentPhaseState entry accumulator n b e m 96
    expOff expTail
  let decodeTail := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat 96, UInt256.ofNat expOff] ++ expTail
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hinitial := BigBaseCorrect.exponentState_initial input returnDest rest
    hvalid hbig hmodulusPos
  have haccReduced : 1 % Word.modulusValue input < Word.modulusValue input :=
    Nat.mod_lt _ hmodulusPos
  have hprogress := BigExponentCorrect.exponentPhase_represents entry
    accumulator n b e m 96 expOff expTail beta
    (Word.modulusValue input) hn hmodulusPos
    (Nat.mod_lt _ hmodulusPos) hinitial.1 hinitial.2.1 hinitial.2.2.1
    hinitial.2.2.2
  have hvalueReduced := BigExponentCorrect.exponentValueAfter_lt entry
    (Word.modulusValue input) beta expOff e (1 % Word.modulusValue input)
    hmodulusPos haccReduced
  have hdecoded := MontgomeryDecodeBlock.decodeReturned_correct phase
    (UInt256.ofNat e) accumulator n
    (BigExponentCorrect.exponentValueAfter entry (Word.modulusValue input)
      beta expOff e (1 % Word.modulusValue input))
    (Word.modulusValue input) decodeTail hn hmodulusPos hvalueReduced
    hprogress.2.1 hprogress.1 hprogress.2.2
  have hentryEnv : entry.executionEnv = header.executionEnv :=
    BigComplete.exponentState_executionEnv header b e m 96 expOff modOff
      returnDest rest
  have hvalueEnv := BigExponentCorrect.exponentValueAfter_executionEnv entry
    header (Word.modulusValue input)
    (WordCorrect.baseNat input % Word.modulusValue input) expOff e
    (1 % Word.modulusValue input) hentryEnv
  have hvalueHeader := BigExponentCorrect.exponentValueAfter_header_eq input
    (Word.modulusValue input)
    (WordCorrect.baseNat input % Word.modulusValue input)
    (1 % Word.modulusValue input) hvalid haccReduced
  have hvalue : BigExponentCorrect.exponentValueAfter entry
      (Word.modulusValue input)
      (WordCorrect.baseNat input % Word.modulusValue input) expOff e
      (1 % Word.modulusValue input) =
      Precompile.modPow (WordCorrect.baseNat input)
        (WordCorrect.exponentNat input) (Word.modulusValue input) := by
    rw [hvalueEnv]
    simpa [b, e, expOff, WordCorrect.exponentNat] using
      hvalueHeader.trans
        (WordCorrect.residue_power_eq_modPow (WordCorrect.baseNat input)
          (WordCorrect.exponentNat input) (Word.modulusValue input) e
          hmodulusPos)
  rw [hvalue] at hdecoded
  simpa only [BigComplete.exponentProgressState,
    BigComplete.encodedExponentProgressState, BigComplete.limbCount,
    phase, decodeTail, entry, accumulator, n, b, e, m, expOff, modOff,
    expTail, header] using hdecoded

end Challenge.Modexp.Submission.Proofs.Bytecode.BigCorrect
