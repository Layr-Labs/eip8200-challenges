import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Universal coverage lemma for the PC59 scanner:
- full first word `readWord input 0 = KnownInputData.fullWord` covers `[0, 32)`;
- `readWord input 32 = readWord input 0` covers `[32, 64)`;
- `readWord input 59 = readWord input 0` covers `[59, 91) ⊇ [64, 80)`;
- `readWord input (16 + 32 * k) = readWord input 0` for `2 ≤ k < 30` covers `[80, 976) ⊇ [80, 968)`;
- `readWord input 968 = readWord input 0` covers `[968, 1000)`.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedCoverage
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def byte (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (YulSemantics.EVM.byteFrom input.toList i).toNat

theorem byte_eq_of_word (input : ByteArray) (a b i : Nat) (hi : i < 32)
    (h : MachineState.readWord input a = MachineState.readWord input b) :
    byte input (a+i) = byte input (b+i) := by
  have hh := congrArg (UInt256.byteAt (UInt256.ofNat i)) h
  simpa only [Bytes.byteAt_readWord input a i hi,
    Bytes.byteAt_readWord input b i hi, byte] using hh

theorem fullWord_byteAt (i : Nat) (hi : i < 32) :
    UInt256.byteAt (UInt256.ofNat i) KnownInputData.fullWord = UInt256.ofNat 97 := by
  interval_cases i <;> decide

theorem reference_bytes (input : ByteArray)
    (h0 : MachineState.readWord input 0 = KnownInputData.fullWord) :
    ∀ i, i < 32 → byte input i = UInt256.ofNat 97 := by
  intro i hi
  have h := congrArg (UInt256.byteAt (UInt256.ofNat i)) h0
  rw [Bytes.byteAt_readWord input 0 i hi, Nat.zero_add, fullWord_byteAt i hi] at h
  exact h

/-- Every byte in `[0, 1000)` is constrained to `0x61` (`97`) universally in `input`. -/
theorem all_bytes (input : ByteArray)
    (h0 : MachineState.readWord input 0 = KnownInputData.fullWord)
    (h32 : MachineState.readWord input 32 = MachineState.readWord input 0)
    (h59 : MachineState.readWord input 59 = MachineState.readWord input 0)
    (hmain : ∀ k, 2 ≤ k → k < 30 → MachineState.readWord input (16+32*k) = MachineState.readWord input 0)
    (h968 : MachineState.readWord input 968 = MachineState.readWord input 0) :
    ∀ j, j < 1000 → byte input j = UInt256.ofNat 97 := by
  have href := reference_bytes input h0
  intro j hj
  by_cases hj32 : j < 32
  · exact href j hj32
  · by_cases hj64 : j < 64
    · have he := byte_eq_of_word input 32 0 (j - 32) (by omega) h32
      rw [Nat.add_sub_of_le (by omega : 32 ≤ j), Nat.zero_add] at he
      exact he.trans (href (j - 32) (by omega))
    · by_cases hj80 : j < 80
      · have he := byte_eq_of_word input 59 0 (j - 59) (by omega) h59
        rw [Nat.add_sub_of_le (by omega : 59 ≤ j), Nat.zero_add] at he
        exact he.trans (href (j - 59) (by omega))
      · by_cases hlast : 968 ≤ j
        · have he := byte_eq_of_word input 968 0 (j - 968) (by omega) h968
          rw [Nat.add_sub_of_le hlast, Nat.zero_add] at he
          exact he.trans (href (j - 968) (by omega))
        · let k := (j - 16) / 32
          let r := (j - 16) % 32
          have hk1 : 2 ≤ k := by dsimp [k]; omega
          have hk2 : k < 30 := by dsimp [k]; omega
          have hr : r < 32 := Nat.mod_lt _ (by decide)
          have he : 16 + 32 * k + r = j := by dsimp [k, r]; omega
          have hh := byte_eq_of_word input (16 + 32 * k) 0 r hr (hmain k hk1 hk2)
          rw [he, Nat.zero_add] at hh
          exact hh.trans (href r hr)

#print axioms fullWord_byteAt
#print axioms reference_bytes
#print axioms all_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedCoverage
