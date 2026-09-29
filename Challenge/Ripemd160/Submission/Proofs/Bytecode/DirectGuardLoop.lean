import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardEarly

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

/-- The exact three-word loop preserves arbitrary backing state and stack suffix.
There are no memory or active-word assumptions.  The strict stack bound is the
uniform pre-instruction bound required by DataStepper. -/
theorem run_reverse_triple (s : State) (input : ByteArray) (n : Nat) (hn : n < 10)
    (a r : UInt256) (rest : List UInt256) (hlen : rest.length ≤ 1018)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hinput : s.executionEnv.calldata = input) :
    run loopPath
      { s with
        pc := UInt256.ofNat 41
        stack := [a, UInt256.ofNat (960 - 96 * n), r] ++ rest } =
    some { s with
      pc := UInt256.ofNat (if n < 9 then 41 else 71)
      stack := [UInt256.lor
          (UInt256.xor (MachineState.readWord input (960 - 96 * n)) r)
          (UInt256.lor
            (UInt256.xor (MachineState.readWord input (896 - 96 * n)) r)
            (UInt256.lor
              (UInt256.xor (MachineState.readWord input (928 - 96 * n)) r) a)),
        UInt256.ofNat (864 - 96 * n), r] ++ rest } := by
  have hdest : Decode.isValidJumpDest submissionBytecode 41 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 26 (by rfl)
    rw [pc_direct_26] at h
    exact h
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hp : 960 - 96 * n < 2 ^ 256 := by omega
  have hq : 928 - 96 * n < 2 ^ 256 := by omega
  have hq2 : 896 - 96 * n < 2 ^ 256 := by omega
  have ht : 864 - 96 * n < 2 ^ 256 := by omega
  have hp32 : 32 ≤ 960 - 96 * n := by omega
  have hp64 : 64 ≤ 960 - 96 * n := by omega
  have hp96 : 96 ≤ 960 - 96 * n := by omega
  have heq32 : 960 - 96 * n - 32 = 928 - 96 * n := by omega
  have heq64 : 960 - 96 * n - 64 = 896 - 96 * n := by omega
  have heq96 : 960 - 96 * n - 96 = 864 - 96 * n := by omega
  have hsub32 : UInt256.ofNat (960 - 96 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (928 - 96 * n) := by
    rw [Word.ofNat_sub_ofNat hp32 hp, heq32]
  have hsub64 : UInt256.ofNat (960 - 96 * n) - UInt256.ofNat 64 =
      UInt256.ofNat (896 - 96 * n) := by
    rw [Word.ofNat_sub_ofNat hp64 hp, heq64]
  have hsub96 : UInt256.ofNat (960 - 96 * n) - UInt256.ofNat 96 =
      UInt256.ofNat (864 - 96 * n) := by
    rw [Word.ofNat_sub_ofNat hp96 hp, heq96]
  have hxor1 : UInt256.xor r (MachineState.readWord input (928 - 96 * n)) =
      UInt256.xor (MachineState.readWord input (928 - 96 * n)) r := BooleanSelect.xor_comm _ _
  have hxor2 : UInt256.xor r (MachineState.readWord input (896 - 96 * n)) =
      UInt256.xor (MachineState.readWord input (896 - 96 * n)) r := BooleanSelect.xor_comm _ _
  have hxor3 : UInt256.xor r (MachineState.readWord input (960 - 96 * n)) =
      UInt256.xor (MachineState.readWord input (960 - 96 * n)) r := BooleanSelect.xor_comm _ _
  by_cases hmore : n < 9
  · have hnonzero : 864 - 96 * n ≠ 0 := by omega
    simp (config := { maxSteps := 1000000 }) (disch := omega)
      [loopPath, opAt, pushAt, wfOp, hrun, hcap3, hcap4, hcap5, hcode, hinput, hdest, hmore,
       hsub32, hsub64, hsub96, hxor1, hxor2, hxor3, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq,
       Nat.mod_eq_of_lt hq2, Nat.mod_eq_of_lt ht, hnonzero, List.exchange,
       List.getElem?_cons_zero, UInt256.isTrue,
       Challenge.EvmProof.DataStepper.runLocatedBlock,
       Challenge.EvmProof.DataStepper.runLocated,
       Challenge.EvmProof.DataStepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod,
       Word.ofNat_add_mod, Word.word_toNat_ofNat]
    have hpmod : (960 - 96 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        960 - 96 * n := Nat.mod_eq_of_lt hp
    have hqmod : (928 - 96 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        928 - 96 * n := Nat.mod_eq_of_lt hq
    have hq2mod : (896 - 96 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        896 - 96 * n := Nat.mod_eq_of_lt hq2
    have htmod : (864 - 96 * n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        864 - 96 * n := Nat.mod_eq_of_lt ht
    simp only [hpmod, hqmod, hq2mod, htmod, hnonzero, if_false, hxor1, hxor2, hxor3]
  · have hn9 : n = 9 := by omega
    subst n
    simp (config := { maxSteps := 1000000 }) (disch := omega)
      [loopPath, opAt, pushAt, wfOp, hrun, hcap3, hcap4, hcap5, hcode, hinput, hdest,
       hsub32, hsub64, hsub96, hxor1, hxor2, hxor3, List.exchange, List.getElem?_cons_zero,
       UInt256.isTrue,
       Challenge.EvmProof.DataStepper.runLocatedBlock,
       Challenge.EvmProof.DataStepper.runLocated,
       Challenge.EvmProof.DataStepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod,
       Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 9) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have h := run_reverse_triple (initialState submissionBytecode input 0) input n
    (by omega) (reverseAcc input n) (referenceWord input) [] (by decide) rfl rfl rfl
  have hp : 960 - 96 * (n + 1) = 864 - 96 * n := by omega
  have ha : reverseAcc input (n + 1) =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input (960 - 96 * n)) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input (896 - 96 * n)) (referenceWord input))
          (UInt256.lor
            (UInt256.xor (MachineState.readWord input (928 - 96 * n)) (referenceWord input))
            (reverseAcc input n))) := rfl
  simpa only [loopState, if_pos hn, List.append_nil, hp, ha] using h

theorem run_loop_last (input : ByteArray) :
    run loopPath (loopState input 9) = some (loopExitState input) := by
  have h := run_reverse_triple (initialState submissionBytecode input 0) input 9
    (by decide) (reverseAcc input 9) (referenceWord input) [] (by decide) rfl rfl rfl
  have ha : reverseAcc input 10 =
      UInt256.lor
        (UInt256.xor (MachineState.readWord input 96) (referenceWord input))
        (UInt256.lor
          (UInt256.xor (MachineState.readWord input 32) (referenceWord input))
          (UInt256.lor
            (UInt256.xor (MachineState.readWord input 64) (referenceWord input))
            (reverseAcc input 9))) := rfl
  simpa only [loopState, loopExitState, show ¬ 9 < 9 by decide, if_false,
    List.append_nil, show 864 - 96 * 9 = 0 by decide,
    show 928 - 96 * 9 = 64 by decide, show 896 - 96 * 9 = 32 by decide,
    show 960 - 96 * 9 = 96 by decide, ← ha] using h

#print axioms run_reverse_triple
#print axioms run_loop_more
#print axioms run_loop_last
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
