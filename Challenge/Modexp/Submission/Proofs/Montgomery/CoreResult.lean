import Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proofs.Bytecode

abbrev B : Nat := radix
abbrev scratch : Nat := 0x2400
abbrev candidate : Nat := 0x1400

/-- The high limb is read from the actual raw state. -/
def highWord (rawState : State) (n : Nat) : UInt256 :=
  MachineState.readWord rawState.memory (scratch + 32 * n)

/-- The existing reducer followed by the existing output copy. No execution is assumed. -/
def finishReturned (rawState : State) (out modulus n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) : State :=
  BigHelpers.copyReturned
    (MontgomeryReduceBlock.reduceReturned rawState (UInt256.ofNat scratch)
      (UInt256.ofNat modulus) (highWord rawState n) n reduceRet reduceRest)
    (UInt256.ofNat out) (UInt256.ofNat scratch) n copyRet copyRest

theorem represented_low {memory : ByteArray} {ptr count total n : Nat}
    (hrep : Represents memory ptr count total) (hn : n ≤ count) :
    Represents memory ptr n (total % B ^ n) := by
  apply (represents_iff_value (Nat.mod_lt _ (pow_pos radix_pos n))).2
  rw [← value_of_represents hrep,
    Nat.ofDigits_mod_pow_eq_ofDigits_take n radix_pos _
      (fun _ hd => memoryLimb_lt memory ptr count hd)]
  congr 1
  simp [memoryLimbs, ← List.map_take, List.take_range, Nat.min_eq_left hn]

private theorem subtractProgress_active_irrel (memory : ByteArray)
    (active active' dst modulus : UInt256) (n : Nat) :
    (BigHelpers.subtractProgress memory active dst modulus n).memory =
      (BigHelpers.subtractProgress memory active' dst modulus n).memory ∧
    (BigHelpers.subtractProgress memory active dst modulus n).borrow =
      (BigHelpers.subtractProgress memory active' dst modulus n).borrow := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => simp only [BigHelpers.subtractProgress, ih.1, ih.2, and_self]

private theorem selectProgress_active_irrel (memory : ByteArray)
    (active active' dst mask : UInt256) (n : Nat) :
    (BigHelpers.selectProgress memory active dst mask n).memory =
      (BigHelpers.selectProgress memory active' dst mask n).memory := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [BigHelpers.selectProgress, ih]

private theorem reduceReturned_memory_congr (s s' : State)
    (dst modulus high : UInt256) (n : Nat) (ret ret' : UInt256)
    (rest rest' : List UInt256) (hmem : s.memory = s'.memory) :
    (MontgomeryReduceBlock.reduceReturned s dst modulus high n ret rest).memory =
      (MontgomeryReduceBlock.reduceReturned s' dst modulus high n ret' rest').memory := by
  have hs := subtractProgress_active_irrel s.memory s.activeWords s'.activeWords dst modulus n
  dsimp only [MontgomeryReduceBlock.reduceReturned, MontgomeryReduceBlock.reduceUseSub]
  rw [← hmem, hs.1, hs.2]
  exact selectProgress_active_irrel _ _ _ _ _ _

/-- Control fields and memory accounting do not change the functional result. -/
theorem finishReturned_memory_congr (rawState otherState : State) (out modulus n : Nat)
    (reduceRet reduceRet' copyRet copyRet' : UInt256)
    (reduceRest reduceRest' copyRest copyRest' : List UInt256)
    (hmem : rawState.memory = otherState.memory) :
    (finishReturned rawState out modulus n reduceRet reduceRest copyRet copyRest).memory =
      (finishReturned otherState out modulus n reduceRet' reduceRest' copyRet' copyRest').memory := by
  have hhigh : highWord rawState n = highWord otherState n := by
    simp only [highWord, hmem]
  dsimp only [finishReturned, BigHelpers.copyReturned]
  rw [hhigh, reduceReturned_memory_congr rawState otherState _ _ _ n
    reduceRet reduceRet' reduceRest reduceRest' hmem]

private theorem copyMemory_byte_outside (memory : ByteArray) (dst src count addr : Nat)
    (hfit : dst + 32 * count < B) (hout : addr < dst ∨ dst + 32 * count ≤ addr) :
    (BigHelpers.copyMemory memory (UInt256.ofNat dst) (UInt256.ofNat src) count)[addr]?.getD 0 =
      memory[addr]?.getD 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hsize (v : Nat) : (Data.Bytes.natToBytesPadded v 32).size = 32 := by
        simp [Data.Bytes.natToBytesPadded, ByteArray.size]
      rw [BigHelpers.copyMemory, MachineState.writeBytes_getElem?_getD, hsize,
        BigHelpers.clearOffset_toNat dst count (by change dst + 32 * (count + 1) < 2^256 at hfit; omega),
        if_neg (by omega)]
      exact ih (by omega) (by omega)

/-- Padded bytes outside all three write regions retain their initial value. -/
theorem finishReturned_byte_outside (initialMemory : ByteArray) (rawState : State)
    (out modulus n addr : Nat) (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256)
    (hraw : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Outside rawState.memory initialMemory scratch n)
    (htfit : scratch + 32 * n < B) (hcfit : candidate + 32 * n < B)
    (houtfit : out + 32 * n < B)
    (houtT : addr < scratch ∨ scratch + 32 * (n + 2) ≤ addr)
    (houtC : addr < candidate ∨ candidate + 32 * n ≤ addr)
    (houtOut : addr < out ∨ out + 32 * n ≤ addr) :
    (finishReturned rawState out modulus n reduceRet reduceRest copyRet copyRest).memory[addr]?.getD 0 =
      initialMemory[addr]?.getD 0 := by
  let reduced := MontgomeryReduceBlock.reduceReturned rawState (UInt256.ofNat scratch)
    (UInt256.ofNat modulus) (highWord rawState n) n reduceRet reduceRest
  exact (copyMemory_byte_outside reduced.memory out scratch n addr houtfit houtOut).trans
    ((MontgomeryReduceBlock.reduceReturned_byte_outside rawState scratch modulus n addr
      (highWord rawState n) reduceRet reduceRest htfit hcfit (by omega) houtC).trans
        (hraw addr houtT))

/-- The preserved region may have any limb count, not just the output count. -/
theorem finishReturned_preserves_region (initialMemory : ByteArray) (rawState : State)
    (out modulus n ptr regionCount value : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256)
    (hraw : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Outside rawState.memory initialMemory scratch n)
    (htfit : scratch + 32 * n < B) (hcfit : candidate + 32 * n < B)
    (houtfit : out + 32 * n < B)
    (hptrT : ptr + 32 * regionCount ≤ scratch ∨ scratch + 32 * (n + 2) ≤ ptr)
    (hptrC : ptr + 32 * regionCount ≤ candidate ∨ candidate + 32 * n ≤ ptr)
    (hptrOut : ptr + 32 * regionCount ≤ out ∨ out + 32 * n ≤ ptr)
    (hrep : Represents initialMemory ptr regionCount value) :
    Represents (finishReturned rawState out modulus n reduceRet reduceRest copyRet copyRest).memory
      ptr regionCount value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [readPadded_congr _ initialMemory (ptr + 32 * j) 32 (by
    intro i hi
    exact finishReturned_byte_outside initialMemory rawState out modulus n (ptr + 32 * j + i)
      reduceRet reduceRest copyRet copyRest hraw htfit hcfit houtfit
      (by omega) (by omega) (by omega))]

/-- Extract both reducer operands from the accepted full raw memory recurrence. -/
theorem rawState_low_high (initialMemory : ByteArray) (rawState : State)
    (a b modulus n : Nat) (np : UInt256) (aValue bValue m : Nat)
    (ha : Represents initialMemory a n aValue) (hb : Represents initialMemory b n bValue)
    (hmemory : Represents initialMemory modulus n m) (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % B = 0)
    (hafit : a + 32 * n < B) (hbfit : b + 32 * n < B)
    (hmfit : modulus + 32 * n < B) (htfit : scratch + 32 * (n + 2) < B)
    (hadis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint a scratch n)
    (hbdis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint b scratch n)
    (hmdis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint modulus scratch n)
    (hraw : rawState.memory = Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress
      initialMemory a b modulus scratch n np n) :
    let total := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n
    Represents rawState.memory scratch n (total % B ^ n) ∧
      (highWord rawState n).toNat = total / B ^ n ∧ total < 2 * m ∧
      Represents rawState.memory modulus n m ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Outside rawState.memory initialMemory scratch n := by
  have hp := Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress_correct initialMemory a b modulus scratch n
    np aValue bValue m ha hb hmemory hm hb_le hinv hafit hbfit hmfit htfit
    hadis hbdis hmdis n (Nat.le_refl n)
  dsimp only at hp ⊢
  rw [← hraw] at hp
  have hdiv : Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n / B ^ n < 2 := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos radix_pos n)).2
    have hmR := hmemory.1
    omega
  have hhigh := Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.represented_digit hp.1 (show n < n + 2 by omega)
  have hB : 2 ≤ B := by exact Nat.succ_le_of_lt radix_gt_one
  rw [Nat.mod_eq_of_lt (hdiv.trans_le hB)] at hhigh
  exact ⟨represented_low hp.1 (by omega), hhigh, hp.2.1, hp.2.2.2.2.2, hp.2.2.1⟩

/-- Functional finishing only: Task 14 must supply the actual raw memory equality. -/
theorem coreResult_correct (initialMemory : ByteArray) (rawState : State)
    (a b out modulus n : Nat) (np : UInt256) (aValue bValue m : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256)
    (ha : Represents initialMemory a n aValue) (hb : Represents initialMemory b n bValue)
    (hmemory : Represents initialMemory modulus n m) (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % B = 0)
    (hafit : a + 32 * n < B) (hbfit : b + 32 * n < B)
    (hmfit : modulus + 32 * n < B) (htfit : scratch + 32 * (n + 2) < B)
    (hadis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint a scratch n)
    (hbdis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint b scratch n)
    (hmdis : Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.Disjoint modulus scratch n)
    (hraw : rawState.memory = Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress
      initialMemory a b modulus scratch n np n)
    (layout : MontgomeryReduceBlock.Layout scratch modulus n)
    (houtfit : out + 32 * n < B)
    (houtT : out + 32 * n ≤ scratch ∨ scratch + 32 * n ≤ out) :
    let total := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n
    let result := finishReturned rawState out modulus n reduceRet reduceRest copyRet copyRest
    Represents result.memory out n (total % m) ∧
      Represents result.memory out n (Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.reduce total m) ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.reduce total m < m ∧
      (Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.reduce total m * B ^ n) % m = (aValue * bValue) % m ∧
      (∀ addr, (addr < scratch ∨ scratch + 32 * (n + 2) ≤ addr) →
        (addr < candidate ∨ candidate + 32 * n ≤ addr) →
        (addr < out ∨ out + 32 * n ≤ addr) →
        result.memory[addr]?.getD 0 = initialMemory[addr]?.getD 0) := by
  have hr := rawState_low_high initialMemory rawState a b modulus n np aValue bValue m
    ha hb hmemory hm hb_le hinv hafit hbfit hmfit htfit hadis hbdis hmdis hraw
  let total := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.run aValue bValue m np.toNat n
  let reduced := MontgomeryReduceBlock.reduceReturned rawState (UInt256.ofNat scratch)
    (UInt256.ofNat modulus) (highWord rawState n) n reduceRet reduceRest
  have hred : Represents reduced.memory scratch n (total % m) :=
    MontgomeryReduceBlock.reduceReturned_represents_mod rawState scratch modulus n total m
      (highWord rawState n) reduceRet reduceRest layout hm hmemory.1 hr.2.2.1 hr.1 hr.2.2.2.1 hr.2.1
  have hcopy := BigHelpers.copyMemory_represents reduced.memory out scratch n (total % m)
    hred houtfit layout.dstFit houtT
  have hnorm := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.reduce_eq_mod hm hr.2.2.1
  have hcontract := Challenge.Modexp.Submission.Proofs.Montgomery.CIOS.normalized_contract_of_le aValue bValue m np.toNat n
    hm hb_le ha.1 hinv
  refine ⟨hcopy, ?_, hcontract.1, hcontract.2, ?_⟩
  · rw [hnorm]
    exact hcopy
  · intro addr hT hC hOut
    exact finishReturned_byte_outside initialMemory rawState out modulus n addr
      reduceRet reduceRest copyRet copyRest hr.2.2.2.2 layout.dstFit layout.candidateFit houtfit
      hT hC hOut

end Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult
