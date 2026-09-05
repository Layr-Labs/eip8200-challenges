import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult
import Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory
import Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop
import Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Montgomery.CoreState

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

abbrev B : Nat := Limbs.radix
abbrev fixedT : Nat := 9216
abbrev candidate : Nat := 5120

/-- A leaf keeps the caller frame and replaces only machine memory fields. -/
def flatLeaf (s result : State) : State :=
  { s with memory := result.memory, activeWords := result.activeWords }

/-- The actual MLOAD memory-expansion touch. -/
def loadLeaf (s : State) (address : Nat) : State :=
  { s with activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) }

/-- The actual clear helper, with its returned memory fields flattened. -/
def clearLeaf (s : State) (n : Nat) (ret : UInt256) (rest : List UInt256) : State :=
  flatLeaf s
    (BigHelpers.clearReturned s (UInt256.ofNat fixedT) (n + 2) ret rest)

/-- One first-product leaf. The source digit is read from the current memory. -/
def firstLeaf (s : State) (a b : UInt256) (n i : Nat) (_np : UInt256)
    (ret : UInt256) (rest : List UInt256) : State :=
  let loaded := loadLeaf s (a.toNat + 32 * i)
  let digit := MachineState.readWord loaded.memory (a.toNat + 32 * i)
  flatLeaf loaded
    (MontgomeryWordBlock.returned loaded (UInt256.ofNat fixedT) b digit n ret rest)

/-- One quotient-product leaf. q is the word value times np, not an address. -/
def secondLeaf (first : State) (modulus np : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  let loaded := loadLeaf first fixedT
  let q := MachineState.readWord loaded.memory fixedT * np
  flatLeaf loaded
    (MontgomeryWordBlock.returned loaded (UInt256.ofNat fixedT) modulus q n ret rest)

/-- The actual overlapping copy helper used by the shift. -/
def copyLeaf (s : State) (n : Nat) (ret : UInt256) (rest : List UInt256) : State :=
  flatLeaf s
    (BigHelpers.copyReturned s (UInt256.ofNat fixedT)
      (UInt256.ofNat (fixedT + 32)) (n + 1) ret rest)

/-- The actual top-zero MSTORE and its memory-expansion touch. -/
def zeroLeaf (s : State) (address : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) address
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat address 32) }

/-- One shift leaf: overlapping copy first, then the top-word zero store. -/
def shiftLeaf (second : State) (n : Nat) (ret : UInt256) (rest : List UInt256) : State :=
  zeroLeaf (copyLeaf second n ret rest) (fixedT + 32 * (n + 1))

/-- The actual high-word MLOAD touch followed by the raw reducer only. -/
def reducedLeaf (raw : State) (modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256) : State :=
  let loaded := loadLeaf raw (fixedT + 32 * n)
  flatLeaf loaded
    (MontgomeryReduceBlock.reduceReturned loaded (UInt256.ofNat fixedT) modulus
      (Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.highWord loaded n) n reduceRet reduceRest)

/-- The actual high-word MLOAD touch followed by raw reduction and output copy. -/
def finishLeaf (raw : State) (out modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) : State :=
  let reduced := reducedLeaf raw modulus n reduceRet reduceRest
  flatLeaf reduced
    (BigHelpers.copyReturned reduced (UInt256.ofNat out.toNat)
      (UInt256.ofNat fixedT) n copyRet copyRest)

/-- One complete first-product, quotient-product, and shift iteration. -/
def step (s : State) (a b modulus : UInt256) (n i : Nat) (np : UInt256)
    (ret : UInt256) (rest : List UInt256) : State :=
  let first := firstLeaf s a b n i np ret rest
  let second := secondLeaf first modulus np n ret rest
  shiftLeaf second n ret rest

/-- Clear once, then perform the exact core iteration count. -/
def progress (s : State) (a b modulus : UInt256) (n : Nat) (np : UInt256)
    (ret : UInt256) (rest : List UInt256) : Nat → State
  | 0 => clearLeaf s n ret rest
  | i + 1 => step (progress s a b modulus n np ret rest i)
      a b modulus n i np ret rest

theorem flatLeaf_frame (s result : State) :
    { flatLeaf s result with memory := s.memory, activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem loadLeaf_frame (s : State) (address : Nat) :
    { loadLeaf s address with activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem zeroLeaf_frame (s : State) (address : Nat) :
    { zeroLeaf s address with memory := s.memory, activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem clearLeaf_returned (s : State) (n : Nat) (ret : UInt256)
    (rest : List UInt256) :
    BigHelpers.clearReturned s (UInt256.ofNat fixedT) (n + 2) ret rest =
      { clearLeaf s n ret rest with pc := ret, stack := rest } := by
  cases s
  rfl

theorem firstLeaf_returned (s : State) (a b : UInt256) (n i : Nat)
    (np ret : UInt256) (rest : List UInt256) :
    let loaded := loadLeaf s (a.toNat + 32 * i)
    MontgomeryWordBlock.returned loaded (UInt256.ofNat fixedT) b
        (MachineState.readWord loaded.memory (a.toNat + 32 * i)) n ret rest =
      { firstLeaf s a b n i np ret rest with pc := ret, stack := rest } := by
  cases s
  rfl

theorem secondLeaf_returned (first : State) (modulus np : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) :
    let loaded := loadLeaf first fixedT
    MontgomeryWordBlock.returned loaded (UInt256.ofNat fixedT) modulus
        (MachineState.readWord loaded.memory fixedT * np) n ret rest =
      { secondLeaf first modulus np n ret rest with pc := ret, stack := rest } := by
  cases first
  rfl

theorem copyLeaf_returned (s : State) (n : Nat) (ret : UInt256)
    (rest : List UInt256) :
    BigHelpers.copyReturned s (UInt256.ofNat fixedT)
        (UInt256.ofNat (fixedT + 32)) (n + 1) ret rest =
      { copyLeaf s n ret rest with pc := ret, stack := rest } := by
  cases s
  rfl

theorem reducedLeaf_returned (raw : State) (modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256) :
    let loaded := loadLeaf raw (fixedT + 32 * n)
    MontgomeryReduceBlock.reduceReturned loaded (UInt256.ofNat fixedT) modulus
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.highWord loaded n) n reduceRet reduceRest =
      { reducedLeaf raw modulus n reduceRet reduceRest with
          pc := reduceRet, stack := reduceRest } := by
  cases raw
  rfl

private theorem ofNat_toNat (word : UInt256) :
    UInt256.ofNat word.toNat = word := by
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat word).symm

theorem production_highWord_eq (x y : UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic.fullHighWord x y =
      Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic.fullHighWord x y := by
  rfl

theorem production_wordStep_eq (memory : ByteArray) (x t j : Nat)
    (word carry : UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep
        memory x t j word carry =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.wordStep memory x t j word carry := by
  rfl

theorem production_foldTop_eq (memory : ByteArray) (t n : Nat) (carry : UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop
        memory t n carry = Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory.foldTop memory t n carry := by
  rfl

theorem production_memoryCarry_eq (memory : ByteArray) (x t : Nat)
    (word : UInt256) (j : Nat) :
    MontgomeryWordBlock.memoryCarry memory x t word j =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.wordProgress memory x t word 0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [MontgomeryWordBlock.memoryCarry, Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.wordProgress]
      rw [ih, production_wordStep_eq]

theorem production_returned_memory_eq (s : State) (t x word : UInt256)
    (n : Nat) (ret : UInt256) (rest : List UInt256) :
    (MontgomeryWordBlock.returned s t x word n ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory s.memory x.toNat t.toNat n word 0 := by
  simp only [MontgomeryWordBlock.returned, Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory]
  rw [production_memoryCarry_eq, production_foldTop_eq]

theorem clearMemory_eq_clearProgress (memory : ByteArray) (count : Nat)
    (hfit : fixedT + 32 * count < B) :
    BigHelpers.clearMemory memory (UInt256.ofNat fixedT) count =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.clearProgress memory fixedT count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : fixedT + 32 * count < B := by omega
      have hprevEq := ih hprev
      rw [BigHelpers.clearMemory, Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.clearProgress, hprevEq]
      rw [BigHelpers.clearOffset_toNat fixedT count (by
        simpa [B, Limbs.radix] using hprev)]

theorem clearLeaf_memory_eq (s : State) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hfit : fixedT + 32 * (n + 2) < B) :
    (clearLeaf s n ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.clearScratch s.memory fixedT n := by
  change BigHelpers.clearMemory s.memory (UInt256.ofNat fixedT) (n + 2) = _
  exact clearMemory_eq_clearProgress s.memory (n + 2) (by omega)

theorem firstLeaf_memory_eq (s : State) (a b : UInt256) (n i : Nat)
    (np ret : UInt256) (rest : List UInt256) :
    (firstLeaf s a b n i np ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory s.memory b.toNat fixedT n
        (MachineState.readWord s.memory (a.toNat + 32 * i)) 0 := by
  have hT : (UInt256.ofNat fixedT).toNat = fixedT := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num [fixedT])
  simpa [firstLeaf, flatLeaf, loadLeaf, hT] using
    (production_returned_memory_eq
      (loadLeaf s (a.toNat + 32 * i)) (UInt256.ofNat fixedT) b
        (MachineState.readWord s.memory (a.toNat + 32 * i)) n ret rest)

theorem secondLeaf_memory_eq (first : State) (modulus np : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (secondLeaf first modulus np n ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.addMulMemory first.memory modulus.toNat fixedT n
        (MachineState.readWord first.memory fixedT * np) 0 := by
  have hT : (UInt256.ofNat fixedT).toNat = fixedT := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num [fixedT])
  simpa [secondLeaf, flatLeaf, loadLeaf, hT] using
    (production_returned_memory_eq
      (loadLeaf first fixedT) (UInt256.ofNat fixedT) modulus
        (MachineState.readWord first.memory fixedT * np) n ret rest)

/-- The actual overlapping copy has the same memory recurrence as shiftProgress. -/
theorem copyMemory_shiftProgress (memory : ByteArray) (count : Nat)
    (hfit : fixedT + 32 * (count + 1) < B) :
    BigHelpers.copyMemory memory (UInt256.ofNat fixedT)
        (UInt256.ofNat (fixedT + 32)) count =
      Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftProgress memory fixedT count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : fixedT + 32 * (count + 1) < B := by omega
      have hsrc : fixedT + 32 + 32 * count < B := by omega
      have hdst : fixedT + 32 * count < B := by omega
      have hsrcAddr :
          (BigHelpers.clearOffset (UInt256.ofNat (fixedT + 32)) count).toNat =
            fixedT + 32 * (count + 1) := by
        rw [BigHelpers.clearOffset_toNat (fixedT + 32) count (by
          simpa [B, Limbs.radix] using hsrc)]
        omega
      have hdstAddr :
          (BigHelpers.clearOffset (UInt256.ofNat fixedT) count).toNat =
            fixedT + 32 * count := by
        exact BigHelpers.clearOffset_toNat fixedT count (by
          simpa [B, Limbs.radix] using hdst)
      rw [BigHelpers.copyMemory, Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftProgress, ih hprev,
        hsrcAddr, hdstAddr]

theorem shiftLeaf_memory_eq (second : State) (n : Nat) (ret : UInt256)
    (rest : List UInt256) (hfit : fixedT + 32 * (n + 2) < B) :
    (shiftLeaf second n ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown second.memory fixedT n := by
  have hcopy := copyMemory_shiftProgress second.memory (n + 1) (by omega)
  simp only [shiftLeaf, zeroLeaf, copyLeaf, flatLeaf, BigHelpers.copyReturned,
    Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown]
  rw [hcopy]

theorem step_memory_eq (s : State) (a b modulus : UInt256) (n i : Nat)
    (np : UInt256) (ret : UInt256) (rest : List UInt256)
    (_hN : n ≤ 32) (_haFit : a.toNat + 32 * n < B)
    (_hbFit : b.toNat + 32 * n < B)
    (_hmFit : modulus.toNat + 32 * n < B)
    (htFit : fixedT + 32 * (n + 2) < B) (_hi : i ≤ n) :
    (step s a b modulus n i np ret rest).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreStep s.memory a.toNat b.toNat modulus.toNat
        fixedT n i np := by
  simp only [step]
  rw [shiftLeaf_memory_eq _ n ret rest htFit]
  rw [secondLeaf_memory_eq _ _ _ n ret rest]
  rw [firstLeaf_memory_eq s a b n i np ret rest]
  rfl

theorem progress_memory_eq (s : State) (a b modulus : UInt256) (n : Nat)
    (np : UInt256) (ret : UInt256) (rest : List UInt256) (i : Nat)
    (hN : n ≤ 32) (haFit : a.toNat + 32 * n < B)
    (hbFit : b.toNat + 32 * n < B)
    (hmFit : modulus.toNat + 32 * n < B)
    (htFit : fixedT + 32 * (n + 2) < B) (hi : i ≤ n) :
    (progress s a b modulus n np ret rest i).memory =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress s.memory a.toNat b.toNat modulus.toNat
        fixedT n np i := by
  induction i with
  | zero =>
      exact clearLeaf_memory_eq s n ret rest htFit
  | succ i ih =>
      have hiPrev : i ≤ n := by omega
      have hprev := ih hiPrev
      have hstep := step_memory_eq
        (progress s a b modulus n np ret rest i) a b modulus n i np ret rest
        hN haFit hbFit hmFit htFit (by omega)
      simpa [progress, Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress, hprev] using hstep

theorem finishLeaf_memory_eq (raw : State) (out modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) :
    (finishLeaf raw out modulus n reduceRet reduceRest copyRet copyRest).memory =
      (Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned raw out.toNat modulus.toNat n
        reduceRet reduceRest copyRet copyRest).memory := by
  let loaded := loadLeaf raw (fixedT + 32 * n)
  have hmem : raw.memory = loaded.memory := rfl
  have hsame := Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned_memory_congr raw loaded
    out.toNat modulus.toNat n reduceRet reduceRet copyRet copyRet
    reduceRest reduceRest copyRest copyRest hmem
  have hmod : UInt256.ofNat modulus.toNat = modulus := ofNat_toNat modulus
  rw [hsame]
  simp only [finishLeaf, reducedLeaf, flatLeaf, loadLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned, hmod]
  rfl

theorem finishLeaf_returned (raw : State) (out modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) :
    let loaded := loadLeaf raw (fixedT + 32 * n)
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned loaded out.toNat modulus.toNat n
        reduceRet reduceRest copyRet copyRest =
      { finishLeaf raw out modulus n reduceRet reduceRest copyRet copyRest with
          pc := copyRet, stack := copyRest } := by
  have hout : UInt256.ofNat out.toNat = out := ofNat_toNat out
  have hmod : UInt256.ofNat modulus.toNat = modulus := ofNat_toNat modulus
  cases raw
  simp only [finishLeaf, reducedLeaf, flatLeaf, loadLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned, hmod, hout]
  rfl

theorem firstLeaf_digit (s : State) (a : UInt256) (_b : UInt256) (_n i : Nat)
    (_np _ret : UInt256) (_rest : List UInt256) :
    MachineState.readWord
        (loadLeaf s (a.toNat + 32 * i)).memory (a.toNat + 32 * i) =
      MachineState.readWord s.memory (a.toNat + 32 * i) := rfl

theorem secondLeaf_quotient (first : State) (_modulus np : UInt256) (_n : Nat)
    (_ret : UInt256) (_rest : List UInt256) :
    MachineState.readWord (loadLeaf first fixedT).memory fixedT * np =
      MachineState.readWord first.memory fixedT * np := rfl

theorem finishLeaf_highWord (raw : State) (_out _modulus : UInt256) (n : Nat)
    (_reduceRet : UInt256) (_reduceRest : List UInt256)
    (_copyRet : UInt256) (_copyRest : List UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.highWord (loadLeaf raw (fixedT + 32 * n)) n =
      MachineState.readWord raw.memory (fixedT + 32 * n) := rfl

end Challenge.Modexp.Submission.Proofs.Montgomery.CoreState
