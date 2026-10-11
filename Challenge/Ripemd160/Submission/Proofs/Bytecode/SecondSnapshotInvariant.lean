import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Start
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration SecondSnapshotCertificates

theorem scheduled_repeat (s : State) (i : Nat) (hc : PoolShapeV2.ClearV2 s.memory) :
    Repeat4 (scheduledState s i).memory := by
  by_cases hh : s.executionEnv.calldata.size = DriverTrace.blockOffset i ∧ s.executionEnv.calldata.size < 256
  · rw [scheduledState_hit s i hh]
    exact pad_repeat _ _
  · rw [scheduledState_miss s i hh]
    exact result_repeat _ _ _ hc

theorem states_repeat (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input)
    (hpos : 0 < input.size) (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    Repeat4 (states input n).memory := by
  cases n with
  | zero =>
    intro k hk
    change (PadSkipEntry.entryState input).memory[206+k]?.getD 0 =
      (PadSkipEntry.entryState input).memory[224+k]?.getD 0
    rw [PadSkipEntry.entryState_zero_below input hfit _ (by change _ < 1056; omega),
      PadSkipEntry.entryState_zero_below input hfit _ (by change _ < 1056; omega)]
  | succ n =>
    exact scheduled_repeat (states input n) n (states_context input hfit hpos n (by omega)).clear

theorem scratch_repeat (m : ByteArray) (lo hi : UInt256) (hr : Repeat4 m) :
    Repeat4 (Pair13Endian.scratchV2 m lo hi) := by
  intro k hk
  simp only [Pair13Endian.scratchV2, Shared32Scratch.writeWord_getD,
    if_neg (by omega : ¬ (252 ≤ 206+k ∧ 206+k < 252+32)),
    if_neg (by omega : ¬ (162 ≤ 206+k ∧ 206+k < 162+32)),
    if_neg (by omega : ¬ (252 ≤ 224+k ∧ 224+k < 252+32)),
    if_neg (by omega : ¬ (162 ≤ 224+k ∧ 224+k < 162+32))]
  exact hr k hk

#print axioms states_repeat
#print axioms scratch_repeat
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotInvariant
