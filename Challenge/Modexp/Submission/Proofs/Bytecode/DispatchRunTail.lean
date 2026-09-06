import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
private theorem run_wordTail_generic (template : State)
    (b e m expOff modOff : UInt256)
    (hcode : template.executionEnv.code = submissionBytecode)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordTailPath
      (framed template 1253 [modOff, expOff, m, e, b]) =
    some (framed template 3000
      [b, e, m, UInt256.ofNat 96, expOff, modOff, UInt256.ofNat 1267,
        modOff, expOff, m, e, b]) := by
  have h3000 : (3000 : UInt256).toNat = 3000 := by decide
  have h3000Word : (3000 : UInt256) = UInt256.ofNat 3000 := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  have h1267Word : (1267 : UInt256) = UInt256.ofNat 1267 := by decide
  simp (config := { maxSteps := 200000 })
    [framed, wordTailPath, wordRestPath, wordEntryPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hcode, hrun, h3000, h3000Word, h96Word, h1267Word,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_wordTail (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordTailPath
      (wordCheckedState input) = some (wordRouteEntryState input) := by
  have h := run_wordTail_generic (Main.headerState input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
    (UInt256.ofNat (modulusSize input)) (UInt256.ofNat (96 + baseSize input))
    (UInt256.ofNat (96 + (baseSize input + exponentSize input))) rfl rfl
  simpa only [framed, wordCheckedState, wordRouteEntryState, wordEntryState,
    Nat.add_assoc] using h


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
