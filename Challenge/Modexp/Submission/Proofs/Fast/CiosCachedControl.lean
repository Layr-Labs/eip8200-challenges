import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_l1Dispatch4 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4396 = true) :
    runInstructions l1DispatchProgram (l1At 4244 s mem bi pa pb 4 i j pdst ret rest) =
      some (l1At 4396 s mem bi pa pb 4 i j pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc1 : rest.length+10 < 1024 := by omega
  have hc2 : rest.length+11 < 1024 := by omega
  have hc3 : rest.length+12 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, l1DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1At, hc1, hc2, hc3, l1Target_four, l2Target_four, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l1Dispatch8 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4246 = true) :
    runInstructions l1DispatchProgram (l1At 4244 s mem bi pa pb 8 i j pdst ret rest) =
      some (l1At 4246 s mem bi pa pb 8 i j pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc1 : rest.length+10 < 1024 := by omega
  have hc2 : rest.length+11 < 1024 := by omega
  have hc3 : rest.length+12 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, l1DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1At, hc1, hc2, hc3, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l1Join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999) :
    runInstructions joinProgram (l1At 4396 s mem bi pa pb n i j pdst ret rest) =
      some (l1At 4397 s mem bi pa pb n i j pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc : rest.length+10 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Dispatch4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4731 = true) :
    runInstructions l2DispatchProgram (l2At 4579 s mid bi mu c0 pa pb 4 i k pdst ret rest) =
      some (l2At 4731 s mid bi mu c0 pa pb 4 i k pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc1 : rest.length+11 < 1024 := by omega
  have hc2 : rest.length+12 < 1024 := by omega
  have hc3 : rest.length+13 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, l2DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc1, hc2, hc3, l1Target_four, l2Target_four, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l2Dispatch8 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4581 = true) :
    runInstructions l2DispatchProgram (l2At 4579 s mid bi mu c0 pa pb 8 i k pdst ret rest) =
      some (l2At 4581 s mid bi mu c0 pa pb 8 i k pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc1 : rest.length+11 < 1024 := by omega
  have hc2 : rest.length+12 < 1024 := by omega
  have hc3 : rest.length+13 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, l2DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc1, hc2, hc3, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l2Join (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999) :
    runInstructions joinProgram (l2At 4731 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At 4732 s mid bi mu c0 pa pb n i k pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l1Join8 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999) :
    runInstructions joinProgram (l1At 4246 s mem bi pa pb n i j pdst ret rest) =
      some (l1At 4247 s mem bi pa pb n i j pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc : rest.length+10 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 999) :
    runInstructions joinProgram (l2At 4581 s mid bi mu c0 pa pb n i k pdst ret rest) =
      some (l2At 4582 s mid bi mu c0 pa pb n i k pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hExtra15 : rest.length + 15 < 1024 := by omega
  have hExtra16 : rest.length + 16 < 1024 := by omega
  have hExtra17 : rest.length + 17 < 1024 := by omega
  have hExtra18 : rest.length + 18 < 1024 := by omega
  have hExtra19 : rest.length + 19 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, hExtra15, hExtra16, hExtra17, hExtra18, hExtra19, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
