import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerLoad (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerLoadPath
      (headerEntryState input) = some (headerLoadedState input) := by
  have hs1197 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1101) (by norm_num : 1101 + 1 < 2 ^ 256)
  have hs1198 := Challenge.EvmProof.Word.succ_ofNat
    (n := 5067) (by norm_num : 5067 + 1 < 2 ^ 256)
  have ha1199 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 5068) (b := 2) (by norm_num : 5068 + 2 < 2 ^ 256)
  have hs1201 := Challenge.EvmProof.Word.succ_ofNat
    (n := 5070) (by norm_num : 5070 + 1 < 2 ^ 256)
  have ha1202 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1140) (b := 2) (by norm_num : 1140 + 2 < 2 ^ 256)
  have hs1204 := Challenge.EvmProof.Word.succ_ofNat
    (n := 5073) (by norm_num : 5073 + 1 < 2 ^ 256)
  have ha1060 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1106) (b := 4) (by norm_num : 1106 + 4 < 2 ^ 256)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h64 : (64 : UInt256).toNat = 64 := by decide
  simp (config := { maxSteps := 200000 })
    [headerLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      headerEntryState, headerLoadedState, initialState, headerWord,
      baseSize, exponentSize, modulusSize,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hs1197, hs1198, ha1199, hs1201, ha1202, hs1204, ha1060, h0, h32, h64]; rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
