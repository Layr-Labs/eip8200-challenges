import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- The first-loop dispatch `DUP6 JUMP` jumps to the frame's `ent` slot. -/
theorem run_l1Dispatch4 (s : State) (q : MacState) (bi : UInt256)
    (pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4201 = true) :
    runInstructions l1DispatchProgram (l1Q 4047 s q bi pb 4 i hd (l1Target 4) pdst ret rest) =
      some (l1Q 4201 s q bi pb 4 i hd (l1Target 4) pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc1 : rest.length+10 < 1024 := by omega
  have hc2 : rest.length+11 < 1024 := by omega
  have hc3 : rest.length+12 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, l1DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1Q, hc1, hc2, hc3, l1Target_four, l2Target_four, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l1Dispatch8 (s : State) (q : MacState) (bi : UInt256)
    (pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4049 = true) :
    runInstructions l1DispatchProgram (l1Q 4047 s q bi pb 8 i hd (l1Target 8) pdst ret rest) =
      some (l1Q 4049 s q bi pb 8 i hd (l1Target 8) pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc1 : rest.length+10 < 1024 := by omega
  have hc2 : rest.length+11 < 1024 := by omega
  have hc3 : rest.length+12 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, l1DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l1Q, hc1, hc2, hc3, l1Target_four, l2Target_four, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

/-- The second-loop dispatch `DUP10 JUMP` jumps to `l2Target n`. -/
theorem run_l2Dispatch4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4500 = true) :
    runInstructions l2DispatchProgram (l2At 4346 s mid bi mu c0 pb 4 i k hd ent pdst ret rest) =
      some (l2At 4500 s mid bi mu c0 pb 4 i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc1 : rest.length+11 < 1024 := by omega
  have hc2 : rest.length+12 < 1024 := by omega
  have hc3 : rest.length+13 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, l2DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc1, hc2, hc3, l1Target_four, l2Target_four, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l2Dispatch8 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4348 = true) :
    runInstructions l2DispatchProgram (l2At 4346 s mid bi mu c0 pb 8 i k hd ent pdst ret rest) =
      some (l2At 4348 s mid bi mu c0 pb 8 i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc1 : rest.length+11 < 1024 := by omega
  have hc2 : rest.length+12 < 1024 := by omega
  have hc3 : rest.length+13 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, l2DispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc1, hc2, hc3, l1Target_four, l2Target_four, l1Target_eight, l2Target_eight, htarget,
    UInt256.isTrue, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l2Join (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 4500 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 4501 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 4348 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 4349 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
