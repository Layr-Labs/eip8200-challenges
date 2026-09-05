import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryBaseLoadValue

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

def loadBaseLeaf (s : State) (offset length : Nat) : State :=
  MontgomerySetupBlock.flatLeaf s
    (BigLoad.loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length)
      1024 0 [])

private theorem loadMemory_preserves_region (calldata memory : ByteArray)
    (offset length i start size : Nat) (hlength : length < 2 ^ 256)
    (hi : i ≤ length) (hfit : 1024 + 32 * Limbs.limbCount length < 2 ^ 256)
    (hdisjoint : start + size ≤ 1024 ∨
      1024 + 32 * Limbs.limbCount length ≤ start) :
    MachineState.readPadded
        (BigLoad.loadMemory calldata offset (UInt256.ofNat 1024) length i memory)
        start size = MachineState.readPadded memory start size := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hiStep : i < length := by omega
      have haddr := BigLoadCorrect.loadAt_ofNat 1024 length i hlength hiStep hfit
      have hlimb : BigLoad.loadLimb length i < Limbs.limbCount length := by
        unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
        omega
      rw [BigLoad.loadMemory, Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint]
      · exact ih (by omega)
      · rw [haddr]
        rcases hdisjoint with hbefore | hafter
        · exact Or.inl (by omega)
        · right
          have hsize (value : Nat) : (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize]
          omega

/-- Preserve every padded read outside the actual written limb region. -/
theorem loadBase_preserves_region (s : State) (offset length n start size : Nat)
    (_hn : 1 ≤ n) (hN : n ≤ 32) (hoffset : offset < 2 ^ 256)
    (hlength : length ≤ 32 * n)
    (hdisjoint : start + size ≤ 1024 ∨
      1024 + 32 * Limbs.limbCount length ≤ start) :
    MachineState.readPadded (loadBaseLeaf s offset length).memory start size =
      MachineState.readPadded s.memory start size := by
  have hk : Limbs.limbCount length ≤ n := by unfold Limbs.limbCount; omega
  have hlen : length < 2 ^ 256 := by omega
  have hoffsetWord : (UInt256.ofNat offset).toNat = offset := by
    exact Nat.mod_eq_of_lt hoffset
  have hlengthWord : (UInt256.ofNat length).toNat = length := by
    exact Nat.mod_eq_of_lt hlen
  change MachineState.readPadded
    (BigLoad.loadMemory s.executionEnv.calldata (UInt256.ofNat offset).toNat
      1024 (UInt256.ofNat length).toNat (UInt256.ofNat length).toNat s.memory)
    start size = _
  rw [hoffsetWord, hlengthWord]
  exact loadMemory_preserves_region s.executionEnv.calldata s.memory offset length length
    start size hlen (Nat.le_refl length) (by omega) hdisjoint

private theorem ofDigits_extend_zero (memory : ByteArray) (ptr k extra : Nat)
    (hzero : ∀ j, k ≤ j → j < k + extra →
      (MachineState.readWord memory (ptr + 32 * j)).toNat = 0) :
    Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr (k + extra)) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr k) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      have hlast := hzero (k + extra) (by omega) (by omega)
      have hstep : Limbs.memoryLimbs memory ptr (k + extra + 1) =
          Limbs.memoryLimbs memory ptr (k + extra) ++ [0] := by
        simp only [Limbs.memoryLimbs, List.range_succ, List.map_append,
          List.map_singleton, hlast]
      rw [← Nat.add_assoc k extra 1, hstep, Nat.ofDigits_append_zero]
      exact ih (fun j hj hje => hzero j hj (by omega))

/-- A fitting raw load represents its value across the full initially zero capacity. -/
theorem loadBase_correct (s : State) (offset length n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hoffset : offset < 2 ^ 256)
    (hlength : length ≤ 32 * n)
    (hzero : Limbs.Represents s.memory 1024 n 0) :
    Limbs.Represents (loadBaseLeaf s offset length).memory 1024 n
      (Precompile.bytesToNatPadded s.executionEnv.calldata offset length) := by
  let k := Limbs.limbCount length
  have hk : k ≤ n := by dsimp only [k]; unfold Limbs.limbCount; omega
  have hlen : length < 2 ^ 256 := by omega
  have hzeroDigits : Limbs.memoryLimbs s.memory 1024 n = List.replicate n 0 := by
    simpa [Limbs.limbDigits, Nat.digitsAppend] using hzero.2
  have hprefix : Limbs.memoryLimbs s.memory 1024 k = List.replicate k 0 := by
    calc
      Limbs.memoryLimbs s.memory 1024 k =
          (Limbs.memoryLimbs s.memory 1024 n).take k := by
        simp [Limbs.memoryLimbs, ← List.map_take, List.take_range, Nat.min_eq_left hk]
      _ = List.replicate k 0 := by rw [hzeroDigits]; simp [Nat.min_eq_left hk]
  have hsmallZero : Limbs.Represents s.memory 1024 k 0 := by
    refine ⟨pow_pos Limbs.radix_pos k, ?_⟩
    simpa [Limbs.limbDigits, Nat.digitsAppend] using hprefix
  have loaded : Limbs.Represents (loadBaseLeaf s offset length).memory 1024 k
      (Precompile.bytesToNatPadded s.executionEnv.calldata offset length) :=
    BigLoadCorrect.loadReturned_represents s offset 1024 length 0 []
      hoffset hlen (by change 1024 + 32 * k < 2 ^ 256; omega) hsmallZero
  have hbound : Precompile.bytesToNatPadded s.executionEnv.calldata offset length <
      Limbs.radix ^ n :=
    loaded.1.trans_le (Nat.pow_le_pow_right (by have := Limbs.radix_gt_one; omega) hk)
  apply (Limbs.represents_iff_value hbound).2
  have hzeroWord (j : Nat) (hj : j < n) :
      (MachineState.readWord s.memory (1024 + 32 * j)).toNat = 0 := by
    have hopt := congrArg (fun xs : List Nat => xs[j]?) hzeroDigits
    simpa [Limbs.memoryLimbs, hj] using hopt
  have hsum : k + (n - k) = n := by omega
  have extended := ofDigits_extend_zero (loadBaseLeaf s offset length).memory
    1024 k (n - k) (by
      intro j hkj hjn
      have hread := loadBase_preserves_region s offset length n (1024 + 32 * j) 32
        hn hN hoffset hlength (Or.inr (by change 1024 + 32 * k ≤ 1024 + 32 * j; omega))
      unfold MachineState.readWord
      rw [hread]
      exact hzeroWord j (by omega))
  rw [hsum] at extended
  exact extended.trans (Limbs.value_of_represents loaded)

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryBaseLoadValue

