import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open MontgomeryOneBlock
open Challenge.Modexp (submissionBytecode)

-- Exact canonical leaf bridges to the accepted Task16 model.
theorem clearLeaf_eq (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) :
    clearLeaf s n = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.clearLeaf s 7168 n ret saved := rfl

theorem seedLeaf_eq (s : State) :
    seedLeaf s = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.storeOneLeaf s 7168 := rfl

theorem reduceLeaf_eq (s : State) (n : Nat) (high ret : UInt256) (saved : List UInt256) :
    reduceLeaf s n high = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf s 7168 0 high n ret saved := rfl

theorem doubleLeaf_eq (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) :
    doubleLeaf s n = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleLeaf s 7168 0 n ret saved := rfl

theorem progress_eq (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256) :
    progress s n i = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress s 7168 0 n ret saved i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [progress, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress, ih, doubleLeaf_eq]

theorem highSeed_memoryLimbs (s : State) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) :
    Limbs.memoryLimbs (highSeedLeaf (clearLeaf s n) n).memory 7168 n =
      List.replicate (n - 1) 0 ++ [1] := by
  apply List.ext_get
  · simp [Limbs.length_memoryLimbs]
    omega
  · intro i hiLeft hiRight
    have hi : i < n := by simpa using hiLeft
    by_cases hlast : i = n - 1
    · subst i
      simp only [Limbs.memoryLimbs] at hiLeft ⊢
      simp only [List.get_eq_getElem]
      rw [List.getElem_map (h := hiLeft)]
      simp only [List.getElem_range]
      change (MachineState.readWord
        (MachineState.writeBytes (clearLeaf s n).memory
          (Data.Bytes.natToBytesPadded 1 32) (7168 + 32 * (n - 1)))
        (7168 + 32 * (n - 1))).toNat = _
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt]
      · simp
      · norm_num
    · have hz := BigHelpers.readWord_clearMemory s.memory 7168 n i
          (by norm_num; omega) hi
      have hiNext : i + 1 < n := by omega
      have hreadNat :
          (MachineState.readWord
            (MachineState.writeBytes (clearLeaf s n).memory
              (Data.Bytes.natToBytesPadded 1 32) (7168 + 32 * (n - 1)))
            (7168 + 32 * i)).toNat = 0 := by
        rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact hz
        · simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          omega
      simp only [Limbs.memoryLimbs] at hiLeft ⊢
      simp only [List.get_eq_getElem]
      rw [List.getElem_map (h := hiLeft)]
      simp only [List.getElem_range]
      change (MachineState.readWord
        (MachineState.writeBytes (clearLeaf s n).memory
          (Data.Bytes.natToBytesPadded 1 32) (7168 + 32 * (n - 1)))
        (7168 + 32 * i)).toNat = _
      rw [hreadNat]
      simp [List.getElem_append, hiNext]

theorem highSeed_represents (s : State) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) :
    Limbs.Represents (highSeedLeaf (clearLeaf s n) n).memory 7168 n
      (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ (n - 1)) := by
  have hradix : 1 < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B := by
    norm_num [Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B, Limbs.radix]
  have hp : Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ (n - 1) <
      Limbs.radix ^ n := by
    exact Nat.pow_lt_pow_right hradix (by omega)
  apply (Limbs.represents_iff_value hp).2
  change Nat.ofDigits Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B
    (Limbs.memoryLimbs (highSeedLeaf (clearLeaf s n) n).memory 7168 n) = _
  rw [highSeed_memoryLimbs s n hn hN, Nat.ofDigits_append,
    Nat.ofDigits_replicate_zero, Nat.ofDigits_singleton]
  simp

theorem highSeed_preserves_region (s : State) (n ptr value : Nat)
    (hdisjoint : 7168 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 7168)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (highSeedLeaf s n).memory ptr n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  change (MachineState.readWord
      (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 1 32)
        (7168 + 32 * (n - 1))) (ptr + 32 * i)).toNat =
    (MachineState.readWord s.memory (ptr + 32 * i)).toNat
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rcases hdisjoint with h | h <;> omega

theorem returned_correct (s : State) (n m : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hmR : m < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) (hodd : m % 2 = 1)
    (hmod : Limbs.Represents s.memory 0 n m) :
    Limbs.Represents (returned s n ret saved).memory 7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n % m) ∧
      Limbs.Represents (returned s n ret saved).memory 0 n m := by
  let c := clearLeaf s n
  have hclearUnit : Limbs.Represents c.memory 7168 n 0 := by
    change Limbs.Represents (clearLeaf s n).memory 7168 n 0
    rw [clearLeaf_eq]
    exact Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.clearLeaf_zero
      s n hN ret saved
  have hclearMod : Limbs.Represents c.memory 0 n m := by
    change Limbs.Represents (clearLeaf s n).memory 0 n m
    rw [clearLeaf_eq]
    exact Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.clearLeaf_modulus
      s n m hN hmod ret saved
  have htop := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.top_value_after_clear
    s n m hn hN hmod ret saved
  have htop' : (top c n).toNat =
      (m / Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ (n - 1)) %
        Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B := by
    change (MachineState.readWord (clearLeaf s n).memory (32 * (n - 1))).toNat = _
    rw [clearLeaf_eq]
    exact htop
  by_cases hfast : 2 ^ 255 ≤ (top c n).toNat
  · have hbound := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.strict_fast_bound
      n m hn hmR hodd (by simpa [htop'] using hfast)
    have hRpos : 0 < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n :=
      pow_pos Limbs.radix_pos _
    have hunit : Limbs.Represents c.memory 7168 n
        (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n %
          Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) := by
      simpa using hclearUnit
    have hhigh : (UInt256.ofNat 1).toNat =
        Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n /
          Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n := by
      simp [Nat.div_self hRpos]
    have hresult := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_represents_mod
      c n m (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n)
      (UInt256.ofNat 1) hN hm hmR hbound hunit hclearMod hhigh ret saved
    have hmodulus := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_modulus
      c n m (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n)
      (UInt256.ofNat 1) hN hclearMod ret saved
    rw [returned_fast s n ret saved (by simpa [c] using hfast), touched_clear s n hn hN]
    constructor
    · rw [reduceLeaf_eq]
      exact hresult
    · rw [reduceLeaf_eq]
      exact hmodulus
  · by_cases hzero : (top c n).toNat = 0
    · have hseed := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.storeOne_represents_one
        s n hn hN ret saved
      have hseedMod := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.storeOne_preserves_region
        c n 0 m hN
        (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.setup_disjoint_zero n hN).1
        hclearMod
      have honeR : 1 < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n :=
        Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.one_lt_R n hn
      have hunit : Limbs.Represents (seedLeaf c).memory 7168 n
          (1 % Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) := by
        change Limbs.Represents (seedLeaf (clearLeaf s n)).memory 7168 n _
        rw [seedLeaf_eq]
        rw [clearLeaf_eq]
        simpa [Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit,
          Nat.mod_eq_of_lt honeR] using hseed
      have hseedMod' : Limbs.Represents (seedLeaf c).memory 0 n m := by
        rw [seedLeaf_eq]
        exact hseedMod
      have hhigh : (UInt256.ofNat 0).toNat =
          1 / Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n := by
        simp [Nat.div_eq_of_lt honeR]
      have hred := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_represents_mod
        (seedLeaf c) n m 1 (UInt256.ofNat 0) hN hm hmR
        (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.slow_total_bound m hm)
        hunit hseedMod' hhigh ret saved
      have hredMod := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_modulus
        (seedLeaf c) n m 1 (UInt256.ofNat 0) hN
        hseedMod' ret saved
      have hred' : Limbs.Represents (reduceLeaf (seedLeaf c) n 0).memory 7168 n
          (1 % m) := by
        rw [reduceLeaf_eq]
        exact hred
      have hredMod' : Limbs.Represents (reduceLeaf (seedLeaf c) n 0).memory 0 n m := by
        rw [reduceLeaf_eq]
        exact hredMod
      have hdp := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress_correct
        (reduceLeaf (seedLeaf c) n 0) n m (1 % m) hN hm hmR
        hred' hredMod'
        (Nat.mod_lt 1 hm) ret saved (256 * n)
      have hvalue := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleIter_radix m n hm
      rw [returned_slow s n ret saved (by simpa [c] using hfast) (by simpa [c] using hzero),
        touched_clear s n hn hN]
      change Limbs.Represents
          (progress (reduceLeaf (seedLeaf (clearLeaf s n)) n 0) n (256 * n)).memory
            7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n % m) ∧
        Limbs.Represents
          (progress (reduceLeaf (seedLeaf (clearLeaf s n)) n 0) n (256 * n)).memory 0 n m
      constructor
      · rw [progress_eq _ _ _ ret saved, ← hvalue]
        simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp.1
      · rw [progress_eq _ _ _ ret saved]
        simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp.2
    · let p := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ (n - 1)
      have hpPos : 0 < p := pow_pos Limbs.radix_pos _
      have hR : Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n =
          Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B * p := by
        unfold Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R
        calc
          Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ n =
              Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ ((n - 1) + 1) := by
                congr 1
                omega
          _ = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ^ (n - 1) *
              Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B := by rw [pow_succ]
          _ = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B * p := by
            simp [p, Nat.mul_comm]
      have hqLt : m / p < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B := by
        apply (Nat.div_lt_iff_lt_mul hpPos).2
        simpa [hR, Nat.mul_comm] using hmR
      have hqMod : (m / p) % Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B =
          m / p := Nat.mod_eq_of_lt hqLt
      have hqPos : 0 < m / p := by
        have : (m / p) % Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B ≠ 0 := by
          rw [← htop']
          exact hzero
        simpa [hqMod] using Nat.pos_of_ne_zero this
      have hpLe : p ≤ m := by
        calc
          p = p * 1 := by simp
          _ ≤ p * (m / p) := Nat.mul_le_mul_left p hqPos
          _ ≤ m := by simpa [Nat.mul_comm] using Nat.mul_div_le m p
      have hpLtR : p < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n := by
        rw [hR]
        have hB : 1 < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B := by
          norm_num [Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B, Limbs.radix]
        nlinarith
      have hseed := highSeed_represents s n hn hN
      have hseedMod := highSeed_preserves_region c n 0 m
        (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.setup_disjoint_zero n hN).1 hclearMod
      have hunit : Limbs.Represents (highSeedLeaf c n).memory 7168 n
          (p % Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) := by
        simpa [c, p, Nat.mod_eq_of_lt hpLtR] using hseed
      have hhigh : (UInt256.ofNat 0).toNat =
          p / Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n := by
        simp [Nat.div_eq_of_lt hpLtR]
      have hpBound : p < 2 * m := by omega
      have hred := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_represents_mod
        (highSeedLeaf c n) n m p (UInt256.ofNat 0) hN hm hmR hpBound hunit
        hseedMod hhigh ret saved
      have hredMod := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_modulus
        (highSeedLeaf c n) n m p (UInt256.ofNat 0) hN hseedMod ret saved
      have hred' : Limbs.Represents (reduceLeaf (highSeedLeaf c n) n 0).memory 7168 n
          (p % m) := by
        rw [reduceLeaf_eq]
        exact hred
      have hredMod' : Limbs.Represents (reduceLeaf (highSeedLeaf c n) n 0).memory 0 n m := by
        rw [reduceLeaf_eq]
        exact hredMod
      have hdp := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress_correct
        (reduceLeaf (highSeedLeaf c n) n 0) n m (p % m) hN hm hmR
        hred' hredMod'
        (Nat.mod_lt p hm) ret saved 256
      have hiter := Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter_encode
        m 0 p 256 hm
      have hpPow : p * 2 ^ 256 = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n := by
        rw [hR]
        norm_num [p, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.B,
          Limbs.radix]
        ring
      have hvalue : Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m
          (p % m) 256 = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n % m := by
        rw [hpPow] at hiter
        simpa [Challenge.Modexp.Submission.Proofs.Montgomery.Domain.encode,
          Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R] using hiter
      rw [returned_middle s n ret saved (by simpa [c] using hfast)
        (by simpa [c] using hzero), touched_clear s n hn hN]
      change Limbs.Represents
          (progress (reduceLeaf (highSeedLeaf (clearLeaf s n) n) n 0) n 256).memory
            7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n % m) ∧
        Limbs.Represents
          (progress (reduceLeaf (highSeedLeaf (clearLeaf s n) n) n 0) n 256).memory 0 n m
      constructor
      · rw [progress_eq _ _ _ ret saved, ← hvalue]
        simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp.1
      · rw [progress_eq _ _ _ ret saved]
        simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp.2

theorem returned_preserves_region (s : State) (n m ptr value : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (_hm : 0 < m) (_hmR : m < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) (_hodd : m % 2 = 1)
    (_hmod : Limbs.Represents s.memory 0 n m)
    (hdisjoint : Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.DisjointSetup n ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (returned s n ret saved).memory ptr n value := by
  let c := clearLeaf s n
  have hclearRep : Limbs.Represents c.memory ptr n value := by
    change Limbs.Represents (clearLeaf s n).memory ptr n value
    rw [clearLeaf_eq]
    exact Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.clearLeaf_preserves_region
      s n ptr value hN hdisjoint.1 hrep ret saved
  by_cases hfast : 2 ^ 255 ≤ (top c n).toNat
  · have hout := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_preserves_region
      c n ptr n value (UInt256.ofNat 1) hN hdisjoint.1 hdisjoint.2 hclearRep ret saved
    rw [returned_fast s n ret saved (by simpa [c] using hfast), touched_clear s n hn hN]
    rw [reduceLeaf_eq]
    exact hout
  · by_cases hzero : (top c n).toNat = 0
    · have hseedRep := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.storeOne_preserves_region
        c n ptr value hN hdisjoint.1 hclearRep
      have hredRep := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_preserves_region
        (seedLeaf c) n ptr n value (UInt256.ofNat 0) hN hdisjoint.1 hdisjoint.2
        (by rw [seedLeaf_eq]; exact hseedRep) ret saved
      have hredRep' : Limbs.Represents (reduceLeaf (seedLeaf c) n 0).memory ptr n value := by
        rw [reduceLeaf_eq]
        exact hredRep
      have hdp := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress_preserves_region
        (reduceLeaf (seedLeaf c) n 0) n ptr value hN hdisjoint
        hredRep' ret saved (256 * n)
      rw [returned_slow s n ret saved (by simpa [c] using hfast) (by simpa [c] using hzero),
        touched_clear s n hn hN]
      rw [progress_eq _ _ _ ret saved]
      simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp
    · have hseedRep := highSeed_preserves_region c n ptr value hdisjoint.1 hclearRep
      have hredRep := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf_preserves_region
        (highSeedLeaf c n) n ptr n value (UInt256.ofNat 0) hN hdisjoint.1 hdisjoint.2
        hseedRep ret saved
      have hredRep' : Limbs.Represents
          (reduceLeaf (highSeedLeaf c n) n 0).memory ptr n value := by
        rw [reduceLeaf_eq]
        exact hredRep
      have hdp := Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress_preserves_region
        (reduceLeaf (highSeedLeaf c n) n 0) n ptr value hN hdisjoint
        hredRep' ret saved 256
      rw [returned_middle s n ret saved (by simpa [c] using hfast)
        (by simpa [c] using hzero), touched_clear s n hn hN]
      rw [progress_eq _ _ _ ret saved]
      simpa only [c, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit] using hdp

def gasSteps_makeMontgomeryOne (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (entry s n ret saved)
      (returned s n ret saved) :=
  gasSteps_unit s n ret saved hcap hn hN hcode hfork hrun hnp hret

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneCorrect
