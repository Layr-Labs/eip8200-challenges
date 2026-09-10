import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_wordJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock wordJumpPath
      (Main.headerState input) = some (wordDispatchState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmodNat : modulusSize input % 2 ^ 256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hm']
    omega
  norm_num at hmodNat
  have h1237 : (1237 : UInt256).toNat = 1237 := by decide
  have h1237Word : (1237 : UInt256) = UInt256.ofNat 1237 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat (modulusSize input)) := by
    exact hmodNat
  simp only [wordDispatchState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  simp [wordJumpPath, wordEntryPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcode, hrun, hmodNat, h1237,
    h1237Word, htrue,
    UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

