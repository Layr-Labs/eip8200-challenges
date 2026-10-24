import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_wordRest (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordCheckPath
      (wordDispatchState input) = some (wordCheckedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb' : baseSize input < 2 ^ 256 := by omega
  have he' : exponentSize input < 2 ^ 256 := by omega
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hexp : 96 + baseSize input < 2 ^ 256 := by omega
  have hmod : 96 + baseSize input + exponentSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hgt : UInt256.gt (UInt256.ofNat (modulusSize input)) 32 = 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h32]
    have hle : modulusSize input % 2 ^ 256 ≤ 32 :=
      (Nat.mod_le (modulusSize input) (2 ^ 256)).trans hword
    rw [if_neg (Nat.not_lt.mpr hle)]
    rfl
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := baseSize input) hexp
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := exponentSize input) (b := 96 + baseSize input) (by omega)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  simp only [wordDispatchState, wordCheckedState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  simp (config := { maxSteps := 300000 })
    [wordCheckPath, wordRestPath, wordEntryPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hrun, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      hb', he', hm', hexp, hmod, hpositive, hword, hmmod, h32,
      hgt, h0, hzeroWord, h96Word,
      hadd₁, hadd₂, Nat.add_assoc]


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

