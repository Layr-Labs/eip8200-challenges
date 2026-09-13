import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardEarly

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

/-- The exact paired loop preserves arbitrary backing state and stack suffix.
There are no memory or active-word assumptions.  The strict stack bound is the
uniform pre-instruction bound required by DataStepper. -/
theorem run_reverse_pair (s : State) (input : ByteArray) (n : Nat) (hn : n < 15)
    (a r : UInt256) (rest : List UInt256) (hlen : rest.length ≤ 1018)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hinput : s.executionEnv.calldata = input) :
    run loopPath
      { s with
        pc := UInt256.ofNat 59
        stack := [a, UInt256.ofNat (960 - 64 * n), r] ++ rest } =
    some { s with
      pc := UInt256.ofNat (if n < 14 then 59 else 81)
      stack := [UInt256.lor
          (UInt256.xor (MachineState.readWord input (928 - 64 * n)) r)
          (UInt256.lor
            (UInt256.xor (MachineState.readWord input (960 - 64 * n)) r) a),
        UInt256.ofNat (896 - 64 * n), r] ++ rest } := by
  have hdest : Decode.isValidJumpDest submissionBytecode 59 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 40 (by rfl)
    rw [pc_direct_40] at h
    exact h
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hp : 960 - 64 * n < 2 ^ 256 := by omega
  have hq : 928 - 64 * n < 2 ^ 256 := by omega
  have ht : 896 - 64 * n < 2 ^ 256 := by omega
  have hp32 : 32 ≤ 960 - 64 * n := by omega
  have hp64 : 64 ≤ 960 - 64 * n := by omega
  have heq32 : 960 - 64 * n - 32 = 928 - 64 * n := by omega
  have heq64 : 960 - 64 * n - 64 = 896 - 64 * n := by omega
  have hsub32 : UInt256.ofNat (960 - 64 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (928 - 64 * n) := by
    rw [Word.ofNat_sub_ofNat hp32 hp, heq32]
  have hsub64 : UInt256.ofNat (960 - 64 * n) - UInt256.ofNat 64 =
      UInt256.ofNat (896 - 64 * n) := by
    rw [Word.ofNat_sub_ofNat hp64 hp, heq64]
  have hxor : UInt256.xor r (MachineState.readWord input (928 - 64 * n)) =
      UInt256.xor (MachineState.readWord input (928 - 64 * n)) r := BooleanSelect.xor_comm _ _
  have hxorFirst : UInt256.xor r (MachineState.readWord input (960 - 64 * n)) =
      UInt256.xor (MachineState.readWord input (960 - 64 * n)) r := BooleanSelect.xor_comm _ _
  have horder :
      UInt256.lor (UInt256.xor (MachineState.readWord input (960 - 64 * n)) r)
        (UInt256.lor (UInt256.xor (MachineState.readWord input (928 - 64 * n)) r) a) =
      UInt256.lor (UInt256.xor (MachineState.readWord input (928 - 64 * n)) r)
        (UInt256.lor (UInt256.xor (MachineState.readWord input (960 - 64 * n)) r) a) := by
    apply Word.word_ext
    simp only [Word.word_toNat_lor]
    exact Nat.or_left_comm _ _ _
  by_cases hmore : n < 14
  · have hnonzero : 896 - 64 * n ≠ 0 := by omega
    simp (config := { maxSteps := 1000000 }) (disch := omega)
      [loopPath, opAt, pushAt, wfOp, hrun, hcap3, hcap4, hcap5, hcode, hinput, hdest, hmore,
       hsub32, hsub64, hxor, hxorFirst, horder, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq,
       Nat.mod_eq_of_lt ht, hnonzero, List.exchange, List.getElem?_cons_zero, UInt256.isTrue,
       Challenge.EvmProof.DataStepper.runLocatedBlock,
       Challenge.EvmProof.DataStepper.runLocated,
       Challenge.EvmProof.DataStepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod,
       Word.ofNat_add_mod, Word.word_toNat_ofNat]
    have hpmod : (960 - 64 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        960 - 64 * n := Nat.mod_eq_of_lt hp
    have hqmod : (928 - 64 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        928 - 64 * n := Nat.mod_eq_of_lt hq
    have htmod : (896 - 64 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        896 - 64 * n := Nat.mod_eq_of_lt ht
    simp only [hpmod, hqmod, htmod, hnonzero, if_false, hxor, hxorFirst, horder]
  · have hn14 : n = 14 := by omega
    subst n
    simp (config := { maxSteps := 1000000 }) (disch := omega)
      [loopPath, opAt, pushAt, wfOp, hrun, hcap3, hcap4, hcap5, hcode, hinput, hdest,
       hsub32, hsub64, hxor, hxorFirst, horder, List.exchange, List.getElem?_cons_zero, UInt256.isTrue,
       Challenge.EvmProof.DataStepper.runLocatedBlock,
       Challenge.EvmProof.DataStepper.runLocated,
       Challenge.EvmProof.DataStepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod,
       Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 14) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have h := run_reverse_pair (initialState submissionBytecode input 0) input n
    (by omega) (reverseAcc input n) (referenceWord input) [] (by decide) rfl rfl rfl
  have hp : 960 - 64 * (n + 1) = 896 - 64 * n := by omega
  have ha : reverseAcc input (n + 1) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (928 - 64 * n)) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input (960 - 64 * n)) (referenceWord input))
          (reverseAcc input n)) := rfl
  simpa only [loopState, if_pos hn, List.append_nil, hp, ha] using h

theorem run_loop_last (input : ByteArray) :
    run loopPath (loopState input 14) = some (loopExitState input) := by
  have h := run_reverse_pair (initialState submissionBytecode input 0) input 14
    (by decide) (reverseAcc input 14) (referenceWord input) [] (by decide) rfl rfl rfl
  have ha : reverseAcc input 15 =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input 32) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input 64) (referenceWord input))
          (reverseAcc input 14)) := rfl
  rw [reverseAcc_final] at ha
  simpa only [loopState, loopExitState, show ¬ 14 < 14 by decide, if_false,
    List.append_nil, show 896 - 64 * 14 = 0 by decide,
    show 928 - 64 * 14 = 32 by decide, show 960 - 64 * 14 = 64 by decide, ← ha] using h

#print axioms run_reverse_pair
#print axioms run_loop_more
#print axioms run_loop_last
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
