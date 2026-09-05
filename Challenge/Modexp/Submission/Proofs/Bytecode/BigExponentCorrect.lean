import Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect

open EvmSemantics
open EvmSemantics.EVM

open BigExponent

theorem exponentBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (exponentBit byte j).toNat ≤ 1 := by
  rw [exponentBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem mulOuterProgress_preserves_region (current : State) (a b : UInt256)
    (count steps ptr value : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hsteps : steps ≤ count) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (BigMul.mulOuterProgress current a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest steps).memory
      ptr count value := by
  induction steps with
  | zero => simpa [BigMul.mulOuterProgress] using hrep
  | succ steps ih =>
      let before := BigMul.mulOuterProgress current a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest steps
      let loaded := BigMul.mulLoadedState before b steps
      let word := BigMul.mulLoadedWord before b steps
      have hbefore : Limbs.Represents before.memory ptr count value :=
        ih (by omega)
      have hloaded : Limbs.Represents loaded.memory ptr count value := by
        simpa [loaded, BigMul.mulLoadedState] using hbefore
      simpa [BigMul.mulOuterProgress, before, loaded, word] using
        BigMul.mulWordProgress_preserves_region loaded word a b count steps
          256 ptr value returnDest rest (by omega) hcount hptrOut hptrAddend
          hptrCandidate hloaded

theorem mulResult_preserves_region (s : State) (a b : UInt256)
    (count ptr value : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (mulResult s a b (UInt256.ofNat 3072) (UInt256.ofNat 0) count
        returnDest rest).memory ptr count value := by
  let cleared := BigMul.mulAfterClear s a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count returnDest rest
  let copied := BigMul.mulAfterCopy s a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count returnDest rest
  have hcleared : Limbs.Represents cleared.memory ptr count value := by
    simpa [cleared, BigMul.mulAfterClear] using
      BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 ptr
        count value (by omega) hptrOut hrep
  have hcopied : Limbs.Represents copied.memory ptr count value := by
    simpa [copied, BigMul.mulAfterCopy, cleared,
      WordCorrect.ofNat_toNat a] using
      BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
        a.toNat ptr count value (by omega) hptrAddend hcleared
  have hprogress := mulOuterProgress_preserves_region copied a b count count
    ptr value returnDest rest (by omega) hcount hptrOut hptrAddend
    hptrCandidate hcopied
  simpa [mulResult, copied, BigMul.mulReturned] using hprogress

def bitStepValue (modulus : Nat) (byte : UInt256) (j acc base : Nat) : Nat :=
  let square := (acc * acc) % modulus
  if (exponentBit byte j).toNat = 0 then square
  else (square * base) % modulus

theorem bitStepProgress_represents_bitStep (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) (acc base modulus : Nat)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
        (bitStepProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 2048 count
        (bitStepValue modulus byte j acc base) ∧
      Limbs.Represents
        (bitStepProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 1024 count base ∧
      Limbs.Represents
        (bitStepProgress s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 0 count modulus := by
  let body := innerBody s accumulatorWord count b e m baseOff expOff i offset
    byte rest j
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  let squared := squareReturned s accumulatorWord count b e m baseOff expOff i
    j offset byte rest
  let copied := copiedSquare s accumulatorWord count b e m baseOff expOff i j
    offset byte rest
  let squareValue := (acc * acc) % modulus
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have h1000 : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
  have h1015 : (1015 : UInt256) = UInt256.ofNat 1015 := by decide
  have hbodyAcc : Limbs.Represents body.memory 2048 count acc := by
    simpa [body, innerBody, innerLoop] using hacc
  have hbodyBase : Limbs.Represents body.memory 1024 count base := by
    simpa [body, innerBody, innerLoop] using hbase
  have hbodyModulus : Limbs.Represents body.memory 0 count modulus := by
    simpa [body, innerBody, innerLoop] using hmodulus
  have hsquare : Limbs.Represents squared.memory 3072 count squareValue := by
    simpa [squared, squareReturned, mulResult, body, frame, squareValue,
      h0, h2048, h3072, h1000] using
      BigMul.mulReturned_represents_product body 2048 count acc acc modulus
        (UInt256.ofNat 1000) frame hcount (by omega) hmodulusPos haccReduced
        hbodyAcc hbodyAcc hbodyModulus
  have hsquaredBase : Limbs.Represents squared.memory 1024 count base := by
    simpa [squared, squareReturned, body, frame, h0, h2048, h3072, h1000]
      using
      mulResult_preserves_region body (UInt256.ofNat 2048)
        (UInt256.ofNat 2048) count 1024 base (UInt256.ofNat 1000) frame hcount
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) hbodyBase
  have hsquaredModulus : Limbs.Represents squared.memory 0 count modulus := by
    simpa [squared, squareReturned, body, frame, h0, h2048, h3072, h1000]
      using
      mulResult_preserves_region body (UInt256.ofNat 2048)
        (UInt256.ofNat 2048) count 0 modulus (UInt256.ofNat 1000) frame hcount
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        hbodyModulus
  have hcopiedSquare : Limbs.Represents copied.memory 2048 count squareValue := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.copyMemory_represents squared.memory 2048 3072 count
        squareValue hsquare (by omega) (by omega) (Or.inl (by omega))
  have hcopiedBase : Limbs.Represents copied.memory 1024 count base := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.represents_copyMemory_disjoint_region squared.memory 2048
        3072 1024 count base (by omega) (Or.inr (by omega)) hsquaredBase
  have hcopiedModulus : Limbs.Represents copied.memory 0 count modulus := by
    simpa [copied, copiedSquare, BigHelpers.copyReturned, h2048, h3072,
      h1015] using
      BigHelpers.represents_copyMemory_disjoint_region squared.memory 2048
        3072 0 count modulus (by omega) (Or.inr (by omega)) hsquaredModulus
  by_cases hbit : (exponentBit byte j).toNat = 0
  · refine ⟨?_, ?_, ?_⟩
    · simpa [bitStepProgress, hbit, copied, bitStepValue, squareValue] using
        hcopiedSquare
    · simpa [bitStepProgress, hbit, copied] using hcopiedBase
    · simpa [bitStepProgress, hbit, copied] using hcopiedModulus
  · let tail := bitTailFrame accumulatorWord count b e m baseOff expOff i j
      offset byte rest
    let product := bitProductReturned s accumulatorWord count b e m baseOff
      expOff i j offset byte rest
    let productValue := (squareValue * base) % modulus
    have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
    have h1289 : (1289 : UInt256) = UInt256.ofNat 1289 := by decide
    have h1316 : (1316 : UInt256) = UInt256.ofNat 1316 := by decide
    have hsquareReduced : squareValue < modulus := Nat.mod_lt _ hmodulusPos
    have hproduct : Limbs.Represents product.memory 3072 count productValue := by
      simpa [product, bitProductReturned, mulResult, squareValue, productValue,
        tail, h0, h1024, h2048, h3072, h1316] using
        BigMul.mulReturned_represents_product copied 1024 count squareValue base
          modulus (UInt256.ofNat 1316) tail hcount (by omega) hmodulusPos
          hsquareReduced hcopiedSquare hcopiedBase hcopiedModulus
    have hproductBase : Limbs.Represents product.memory 1024 count base := by
      simpa [product, bitProductReturned, mulResult, squareValue, tail, h0,
        h1024, h2048, h3072, h1316, BigMul.mulReturned] using
        (BigMul.mulOuterProgress_afterCopy_represents_product copied 1024 count
          squareValue base modulus (UInt256.ofNat 1316) tail hcount (by omega)
          hmodulusPos hsquareReduced hcopiedSquare hcopiedBase
          hcopiedModulus).2.1
    have hproductModulus : Limbs.Represents product.memory 0 count modulus := by
      simpa [product, bitProductReturned, mulResult, squareValue, tail, h0,
        h1024, h2048, h3072, h1316, BigMul.mulReturned] using
        (BigMul.mulOuterProgress_afterCopy_represents_product copied 1024 count
          squareValue base modulus (UInt256.ofNat 1316) tail hcount (by omega)
          hmodulusPos hsquareReduced hcopiedSquare hcopiedBase
          hcopiedModulus).2.2
    have hfinalAcc : Limbs.Represents
        (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 2048 count productValue := by
      simpa [bitCopyBack, BigHelpers.copyReturned, product, tail, h2048, h3072,
        h1289] using
        BigHelpers.copyMemory_represents product.memory 2048 3072 count
          productValue hproduct (by omega) (by omega) (Or.inl (by omega))
    have hfinalBase : Limbs.Represents
        (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 1024 count base := by
      simpa [bitCopyBack, BigHelpers.copyReturned, product, tail, h2048, h3072,
        h1289] using
        BigHelpers.represents_copyMemory_disjoint_region product.memory 2048
          3072 1024 count base (by omega) (Or.inr (by omega)) hproductBase
    have hfinalModulus : Limbs.Represents
        (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest).memory 0 count modulus := by
      simpa [bitCopyBack, BigHelpers.copyReturned, product, tail, h2048, h3072,
        h1289] using
        BigHelpers.represents_copyMemory_disjoint_region product.memory 2048
          3072 0 count modulus (by omega) (Or.inr (by omega)) hproductModulus
    refine ⟨?_, ?_, ?_⟩
    · simpa [bitStepProgress, hbit, bitStepValue, squareValue, productValue]
        using hfinalAcc
    · simpa [bitStepProgress, hbit] using hfinalBase
    · simpa [bitStepProgress, hbit] using hfinalModulus

theorem exponentBit_toNat_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = WordCorrect.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (WordCorrect.exponentBit_eq byte j hj)
  have hbit := WordCorrect.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : WordCorrect.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem bitStepValue_eq_natBitStep (modulus : Nat) (byte : UInt256)
    (j acc base : Nat) (hj : j < 8) :
    bitStepValue modulus byte j acc base =
      WordCorrect.natBitStep modulus byte j acc base := by
  simp only [bitStepValue, WordCorrect.natBitStep]
  rw [exponentBit_toNat_eq byte j hj]

theorem exponentBitProgress_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (steps acc base modulus : Nat)
    (hsteps : steps ≤ 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.exponentBitProgress s accumulatorWord count b e
      m baseOff expOff i offset byte rest steps
    Limbs.Represents progress.memory 2048 count
        (WordCorrect.natBitAfter modulus byte base steps acc) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.exponentBitProgress s accumulatorWord count b e
        m baseOff expOff i offset byte rest steps
      let beforeValue := WordCorrect.natBitAfter modulus byte base steps acc
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        WordCorrect.natBitAfter_lt modulus byte base acc steps hmodulusPos
          haccReduced
      have hstep := bitStepProgress_represents_bitStep before accumulatorWord
        count b e m baseOff expOff i steps offset byte rest beforeValue base
        modulus hcount hmodulusPos hbeforeReduced hbefore.1 hbefore.2.1
        hbefore.2.2
      simpa [BigExponent.exponentBitProgress, before, beforeValue,
        WordCorrect.natBitAfter,
        bitStepValue_eq_natBitStep modulus byte steps beforeValue base
          (by omega)] using
        hstep

theorem natBitAfter_eight_eq_natExpStep (modulus : Nat) (byte : UInt256)
    (acc base : Nat) (hacc : acc < modulus) (hbyte : byte.toNat < 256) :
    WordCorrect.natBitAfter modulus byte base 8 acc =
      WordCorrect.natExpStep modulus byte acc base := by
  rw [WordCorrect.natBitAfter_eq modulus byte base acc 8 hacc,
    WordCorrect.bitPrefix_eight byte hbyte]
  norm_num [WordCorrect.natExpStep]

theorem loadedExponentByte_lt (s : State) (expOff i : Nat) :
    (loadedExponentByte s expOff i).toNat < 256 := by
  unfold loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

def exponentValueAfter (s : State) (modulus base expOff : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      WordCorrect.natExpStep modulus (loadedExponentByte s expOff i)
        (exponentValueAfter s modulus base expOff i acc) base

theorem exponentValueAfter_lt (s : State) (modulus base expOff steps acc : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    exponentValueAfter s modulus base expOff steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps ih =>
      rw [exponentValueAfter, WordCorrect.natExpStep]
      exact Nat.mod_lt _ hmodulusPos

theorem exponentByteProgress_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (steps acc base modulus : Nat) (hsteps : steps ≤ e)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.exponentByteProgress s accumulatorWord count b
      e m baseOff expOff rest steps
    Limbs.Represents progress.memory 2048 count
        (exponentValueAfter s modulus base expOff steps acc) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.exponentByteProgress s accumulatorWord count b
        e m baseOff expOff rest steps
      let beforeValue := exponentValueAfter s modulus base expOff steps acc
      let offset := UInt256.ofNat (expOff + steps)
      let byte := loadedExponentByte before expOff steps
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        exponentValueAfter_lt s modulus base expOff steps acc hmodulusPos
          haccReduced
      have hbyteEnv : before.executionEnv = s.executionEnv := by
        exact BigExponent.exponentByteProgress_executionEnv s accumulatorWord
          count b e m baseOff expOff steps rest
      have hbyte : byte = loadedExponentByte s expOff steps := by
        simp only [byte, loadedExponentByte]
        rw [hbyteEnv]
      have hbits := exponentBitProgress_represents before accumulatorWord count
        b e m baseOff expOff steps offset byte rest 8 beforeValue base modulus
        (by omega) hcount hmodulusPos hbeforeReduced hbefore.1 hbefore.2.1
        hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact loadedExponentByte_lt s expOff steps
      have hstepEq := natBitAfter_eight_eq_natExpStep modulus byte beforeValue
        base hbeforeReduced hbyteLt
      rw [hstepEq] at hbits
      simpa [BigExponent.exponentByteProgress, before, beforeValue, offset,
        byte, exponentValueAfter, hbyte] using hbits

theorem loadedExponentByte_header (input : ByteArray) (i : Nat)
    (hoff : Word.expOffset input + i < 2 ^ 256) :
    loadedExponentByte (Main.headerState input) (Word.expOffset input) i =
      WordCorrect.exponentByte input i := by
  unfold loadedExponentByte WordCorrect.exponentByte Word.byteWord
    Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rfl

theorem exponentValueAfter_executionEnv (s t : State)
    (modulus base expOff steps acc : Nat) (henv : s.executionEnv = t.executionEnv) :
    exponentValueAfter s modulus base expOff steps acc =
      exponentValueAfter t modulus base expOff steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedExponentByte s expOff steps =
          loadedExponentByte t expOff steps := by
        unfold loadedExponentByte
        rw [henv]
      rw [exponentValueAfter, exponentValueAfter, ih, hbyte]

theorem exponentValueAfter_header_eq_natExpAfter (input : ByteArray)
    (modulus base steps acc : Nat)
    (hoff : Word.expOffset input + steps < 2 ^ 256) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) steps acc =
      WordCorrect.natExpAfter input modulus base steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [exponentValueAfter, WordCorrect.natExpAfter, ih (by omega),
        loadedExponentByte_header input steps (by omega)]

theorem exponentValueAfter_header_eq (input : ByteArray)
    (modulus base acc : Nat) (hvalid : ValidInput input)
    (hacc : acc < modulus) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) (exponentSize input) acc =
      (acc ^ (256 ^ exponentSize input) *
        base ^ (Precompile.bytesToNatPadded input (Word.expOffset input)
          (exponentSize input))) % modulus := by
  have hoff : Word.expOffset input + exponentSize input < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, _⟩
    simp only [Word.expOffset]
    omega
  rw [exponentValueAfter_header_eq_natExpAfter input modulus base
    (exponentSize input) acc hoff]
  exact WordCorrect.natExpAfter_eq input modulus base acc
    (exponentSize input) hvalid (by omega) hacc


section ColdPath
set_option linter.unusedVariables false

/-! ## S2 cold path: functional correctness -/

/-- `(1 % m) ^ N % m = 1 % m`, uniformly in `m` (including `m = 1`). -/
theorem oneMod_pow (modulus N : Nat) :
    (1 % modulus) ^ N % modulus = 1 % modulus := by
  rw [← Nat.pow_mod, Nat.one_pow]

/-- Leading zero bits leave the accumulator at `1 % modulus`. -/
theorem natBitAfter_of_zero_prefix (modulus : Nat) (byte : UInt256)
    (base j0 : Nat) (hmodulusPos : 0 < modulus)
    (hz : ∀ t, t < j0 → WordCorrect.exponentBitNat byte t = 0) :
    WordCorrect.natBitAfter modulus byte base j0 (1 % modulus) = 1 % modulus := by
  have hacc : 1 % modulus < modulus := Nat.mod_lt _ hmodulusPos
  rw [WordCorrect.natBitAfter_eq modulus byte base (1 % modulus) j0 hacc,
    BigExponent.bitPrefix_eq_zero byte j0 hz, Nat.pow_zero, Nat.mul_one,
    oneMod_pow]

/-- A zero exponent byte leaves the accumulator at `1 % modulus`. -/
theorem natExpStep_of_zero_byte (modulus : Nat) (byte : UInt256) (base : Nat)
    (hmodulusPos : 0 < modulus) (hbyte : byte.toNat = 0) :
    WordCorrect.natExpStep modulus byte (1 % modulus) base = 1 % modulus := by
  have hacc : 1 % modulus < modulus := Nat.mod_lt _ hmodulusPos
  have hlt : byte.toNat < 256 := by omega
  rw [← natBitAfter_eight_eq_natExpStep modulus byte (1 % modulus) base hacc
      hlt,
    WordCorrect.natBitAfter_eq modulus byte base (1 % modulus) 8 hacc,
    WordCorrect.bitPrefix_eight byte hlt, hbyte, Nat.pow_zero, Nat.mul_one,
    oneMod_pow]

/-- A zero exponent-byte prefix leaves the accumulator at `1 % modulus`. -/
theorem exponentValueAfter_of_zero_prefix (s : State)
    (modulus base expOff k : Nat) (hmodulusPos : 0 < modulus)
    (hz : ∀ t, t < k → (loadedExponentByte s expOff t).toNat = 0) :
    exponentValueAfter s modulus base expOff k (1 % modulus) = 1 % modulus := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [exponentValueAfter, ih (fun t ht => hz t (by omega))]
      exact natExpStep_of_zero_byte modulus (loadedExponentByte s expOff k) base
        hmodulusPos (hz k (by omega))

/-! ### Shifted value recursions -/

def natBitFrom (modulus : Nat) (byte : UInt256) (base start acc : Nat) :
    Nat → Nat
  | 0 => acc
  | t + 1 =>
      WordCorrect.natBitStep modulus byte (start + t)
        (natBitFrom modulus byte base start acc t) base

theorem natBitFrom_lt (modulus : Nat) (byte : UInt256) (base start acc t : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    natBitFrom modulus byte base start acc t < modulus := by
  induction t with
  | zero => exact hacc
  | succ t _ =>
      rw [natBitFrom]
      exact WordCorrect.natBitStep_lt modulus byte (start + t) _ base
        hmodulusPos

theorem natBitAfter_split (modulus : Nat) (byte : UInt256)
    (base a t acc : Nat) :
    WordCorrect.natBitAfter modulus byte base (a + t) acc =
      natBitFrom modulus byte base a
        (WordCorrect.natBitAfter modulus byte base a acc) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show a + (t + 1) = (a + t) + 1 from by omega,
        WordCorrect.natBitAfter, ih, natBitFrom]

def expValueFrom (s : State) (modulus base expOff start acc : Nat) :
    Nat → Nat
  | 0 => acc
  | t + 1 =>
      WordCorrect.natExpStep modulus (loadedExponentByte s expOff (start + t))
        (expValueFrom s modulus base expOff start acc t) base

theorem expValueFrom_lt (s : State) (modulus base expOff start acc t : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    expValueFrom s modulus base expOff start acc t < modulus := by
  induction t with
  | zero => exact hacc
  | succ t _ =>
      rw [expValueFrom, WordCorrect.natExpStep]
      exact Nat.mod_lt _ hmodulusPos

theorem expValueFrom_executionEnv (s t : State)
    (modulus base expOff start acc steps : Nat)
    (henv : s.executionEnv = t.executionEnv) :
    expValueFrom s modulus base expOff start acc steps =
      expValueFrom t modulus base expOff start acc steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedExponentByte s expOff (start + steps) =
          loadedExponentByte t expOff (start + steps) := by
        unfold loadedExponentByte
        rw [henv]
      rw [expValueFrom, expValueFrom, ih, hbyte]

theorem exponentValueAfter_split (s : State) (modulus base expOff a t acc : Nat) :
    exponentValueAfter s modulus base expOff (a + t) acc =
      expValueFrom s modulus base expOff a
        (exponentValueAfter s modulus base expOff a acc) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show a + (t + 1) = (a + t) + 1 from by omega, exponentValueAfter, ih,
        expValueFrom]

/-! ### Shifted progress functions preserve the limb invariants -/

theorem bitProgressFrom_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start steps acc base modulus : Nat)
    (hsteps : start + steps ≤ 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.bitProgressFrom s accumulatorWord count b e m
      baseOff expOff i offset byte rest start steps
    Limbs.Represents progress.memory 2048 count
        (natBitFrom modulus byte base start acc steps) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.bitProgressFrom s accumulatorWord count b e m
        baseOff expOff i offset byte rest start steps
      let beforeValue := natBitFrom modulus byte base start acc steps
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        natBitFrom_lt modulus byte base start acc steps hmodulusPos haccReduced
      have hstep := bitStepProgress_represents_bitStep before accumulatorWord
        count b e m baseOff expOff i (start + steps) offset byte rest
        beforeValue base modulus hcount hmodulusPos hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      simpa [BigExponent.bitProgressFrom, before, beforeValue, natBitFrom,
        bitStepValue_eq_natBitStep modulus byte (start + steps) beforeValue base
          (by omega)] using hstep

theorem byteProgressFrom_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start steps acc base modulus : Nat) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigExponent.byteProgressFrom s accumulatorWord count b e m
      baseOff expOff rest start steps
    Limbs.Represents progress.memory 2048 count
        (expValueFrom s modulus base expOff start acc steps) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := BigExponent.byteProgressFrom s accumulatorWord count b e m
        baseOff expOff rest start steps
      let beforeValue := expValueFrom s modulus base expOff start acc steps
      let offset := UInt256.ofNat (expOff + (start + steps))
      let byte := loadedExponentByte before expOff (start + steps)
      have hbefore := ih
      have hbeforeReduced : beforeValue < modulus :=
        expValueFrom_lt s modulus base expOff start acc steps hmodulusPos
          haccReduced
      have hbyteEnv : before.executionEnv = s.executionEnv :=
        BigExponent.byteProgressFrom_executionEnv s accumulatorWord count b e m
          baseOff expOff start steps rest
      have hbyte : byte = loadedExponentByte s expOff (start + steps) := by
        simp only [byte, loadedExponentByte]
        rw [hbyteEnv]
      have hbits := exponentBitProgress_represents before accumulatorWord count
        b e m baseOff expOff (start + steps) offset byte rest 8 beforeValue base
        modulus (by omega) hcount hmodulusPos hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact loadedExponentByte_lt s expOff (start + steps)
      have hstepEq := natBitAfter_eight_eq_natExpStep modulus byte beforeValue
        base hbeforeReduced hbyteLt
      rw [hstepEq] at hbits
      simpa [BigExponent.byteProgressFrom, before, beforeValue, offset, byte,
        expValueFrom, hbyte] using hbits
/-- S2a: the cold search leaves memory untouched, so all three regions pass
through unchanged and the accumulator still holds `1 % modulus`. -/
theorem coldPhaseHit_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (base modulus : Nat) (_hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (_hbaseReduced : base < modulus)
    (_hklt : BigExponent.coldByteIndex s expOff e < e)
    (hacc : Limbs.Represents s.memory 2048 count (1 % modulus))
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
      (BigExponent.coldPhaseHit s accumulatorWord count b e m baseOff expOff
        rest).memory 2048 count
      (WordCorrect.natBitAfter modulus (BigExponent.coldPhaseByte s expOff e)
        base (BigExponent.coldPhaseStart s expOff e) (1 % modulus)) ∧
    Limbs.Represents
      (BigExponent.coldPhaseHit s accumulatorWord count b e m baseOff expOff
        rest).memory 1024 count base ∧
    Limbs.Represents
      (BigExponent.coldPhaseHit s accumulatorWord count b e m baseOff expOff
        rest).memory 0 count modulus := by
  have hzero := natBitAfter_of_zero_prefix modulus
    (BigExponent.coldPhaseByte s expOff e) base
    (BigExponent.coldPhaseStart s expOff e) hmodulusPos
    (by
      intro t ht
      have ht8 : t < 8 :=
        Nat.lt_of_lt_of_le ht
          (by
            simpa [BigExponent.coldPhaseStart, BigExponent.coldPhaseBit] using
              BigExponent.coldBitIndex_le (BigExponent.coldPhaseByte s expOff e))
      rw [← BigExponent.exponentBit_toNat_eq_bitNat _ t ht8]
      exact BigExponent.coldBitIndex_zeros _ t
        (by simpa [BigExponent.coldPhaseStart, BigExponent.coldPhaseBit] using ht))
  rw [hzero]
  exact ⟨by simpa [BigExponent.coldPhaseHit] using hacc,
    by simpa [BigExponent.coldPhaseHit] using hbase,
    by simpa [BigExponent.coldPhaseHit] using hmodulus⟩

/-- End-to-end value of the exponent phase, cold prefix included. -/
theorem exponentPhase_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (base modulus : Nat) (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count (1 % modulus))
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
      (BigExponent.exponentPhaseState s accumulatorWord count b e m baseOff
        expOff rest).memory 2048 count
      (exponentValueAfter s modulus base expOff e (1 % modulus)) := by
  have hkle : BigExponent.coldByteIndex s expOff e ≤ e :=
    BigExponent.coldByteIndex_le s expOff e
  by_cases hk : BigExponent.coldByteIndex s expOff e = e
  · have hval : exponentValueAfter s modulus base expOff e (1 % modulus) =
        1 % modulus :=
      exponentValueAfter_of_zero_prefix s modulus base expOff e hmodulusPos
        (fun t ht => BigExponent.coldByteIndex_zeros s expOff e t (by omega))
    rw [hval]
    simpa [BigExponent.exponentPhaseState, hk] using hacc
  · have hklt' : BigExponent.coldByteIndex s expOff e < e := by omega
    have hprefix : exponentValueAfter s modulus base expOff
        (BigExponent.coldByteIndex s expOff e) (1 % modulus) = 1 % modulus :=
      exponentValueAfter_of_zero_prefix s modulus base expOff
        (BigExponent.coldByteIndex s expOff e) hmodulusPos
        (fun t ht => BigExponent.coldByteIndex_zeros s expOff e t ht)
    have hstartLe : BigExponent.coldPhaseStart s expOff e ≤ 8 := by
      have hj0 : BigExponent.coldPhaseBit s expOff e < 8 :=
        BigExponent.coldBitIndex_lt (BigExponent.coldPhaseByte s expOff e)
          (by
            simpa [BigExponent.coldPhaseByte] using
              BigExponent.loadedExponentByte_lt256 s expOff
                (BigExponent.coldByteIndex s expOff e))
          (by
            simpa [BigExponent.coldPhaseByte] using
              BigExponent.coldByteIndex_hit s expOff e hklt')
      simp only [BigExponent.coldPhaseStart]
      omega
    have hhit := coldPhaseHit_represents s accumulatorWord count b e m baseOff
      expOff rest base modulus hcount hmodulusPos hbaseReduced hklt' hacc hbase
      hmodulus
    have hbitsRep := bitProgressFrom_represents
      (BigExponent.coldPhaseHit s accumulatorWord count b e m baseOff expOff
        rest)
      accumulatorWord count b e m baseOff expOff
      (BigExponent.coldByteIndex s expOff e)
      (BigExponent.coldPhaseOffset s expOff e)
      (BigExponent.coldPhaseByte s expOff e) rest
      (BigExponent.coldPhaseStart s expOff e)
      (8 - BigExponent.coldPhaseStart s expOff e)
      (WordCorrect.natBitAfter modulus (BigExponent.coldPhaseByte s expOff e)
        base (BigExponent.coldPhaseStart s expOff e) (1 % modulus))
      base modulus (by omega) hcount hmodulusPos
      (WordCorrect.natBitAfter_lt modulus _ base (1 % modulus) _ hmodulusPos
        (Nat.mod_lt _ hmodulusPos))
      hhit.1 hhit.2.1 hhit.2.2
    have hsplit : natBitFrom modulus (BigExponent.coldPhaseByte s expOff e) base
        (BigExponent.coldPhaseStart s expOff e)
        (WordCorrect.natBitAfter modulus (BigExponent.coldPhaseByte s expOff e)
          base (BigExponent.coldPhaseStart s expOff e) (1 % modulus))
        (8 - BigExponent.coldPhaseStart s expOff e) =
        WordCorrect.natBitAfter modulus (BigExponent.coldPhaseByte s expOff e)
          base 8 (1 % modulus) := by
      rw [← natBitAfter_split]
      rw [show BigExponent.coldPhaseStart s expOff e +
        (8 - BigExponent.coldPhaseStart s expOff e) = 8 from by omega]
    have hbyteVal : exponentValueAfter s modulus base expOff
        (BigExponent.coldByteIndex s expOff e + 1) (1 % modulus) =
        WordCorrect.natBitAfter modulus (BigExponent.coldPhaseByte s expOff e)
          base 8 (1 % modulus) := by
      rw [natBitAfter_eight_eq_natExpStep modulus
          (BigExponent.coldPhaseByte s expOff e) (1 % modulus) base
          (Nat.mod_lt _ hmodulusPos)
          (by
            simpa [BigExponent.coldPhaseByte] using
              BigExponent.loadedExponentByte_lt256 s expOff
                (BigExponent.coldByteIndex s expOff e)),
        exponentValueAfter, hprefix]
      rfl
    have hbytesRep := byteProgressFrom_represents
      (BigExponent.coldPhaseBits s accumulatorWord count b e m baseOff expOff
        rest)
      accumulatorWord count b e m baseOff expOff rest
      (BigExponent.coldByteIndex s expOff e + 1)
      (e - (BigExponent.coldByteIndex s expOff e + 1))
      (exponentValueAfter s modulus base expOff
        (BigExponent.coldByteIndex s expOff e + 1) (1 % modulus))
      base modulus hcount hmodulusPos
      (exponentValueAfter_lt s modulus base expOff _ (1 % modulus) hmodulusPos
        (Nat.mod_lt _ hmodulusPos))
      (by
        rw [hbyteVal, ← hsplit]
        simpa [BigExponent.coldPhaseBits, BigExponent.bitFinalFrom] using
          hbitsRep.1)
      (by
        simpa [BigExponent.coldPhaseBits, BigExponent.bitFinalFrom] using
          hbitsRep.2.1)
      (by
        simpa [BigExponent.coldPhaseBits, BigExponent.bitFinalFrom] using
          hbitsRep.2.2)
    have henv : (BigExponent.coldPhaseBits s accumulatorWord count b e m baseOff
        expOff rest).executionEnv = s.executionEnv := by simp
    have htail : exponentValueAfter s modulus base expOff e (1 % modulus) =
        expValueFrom
          (BigExponent.coldPhaseBits s accumulatorWord count b e m baseOff
            expOff rest)
          modulus base expOff (BigExponent.coldByteIndex s expOff e + 1)
          (exponentValueAfter s modulus base expOff
            (BigExponent.coldByteIndex s expOff e + 1) (1 % modulus))
          (e - (BigExponent.coldByteIndex s expOff e + 1)) := by
      rw [expValueFrom_executionEnv _ s _ _ _ _ _ _ henv,
        ← exponentValueAfter_split]
      rw [show BigExponent.coldByteIndex s expOff e + 1 +
        (e - (BigExponent.coldByteIndex s expOff e + 1)) = e from by omega]
    rw [htail]
    simpa [BigExponent.exponentPhaseState, hk, BigExponent.coldPhaseTail,
      BigExponent.byteFinalFrom] using hbytesRep.1

end ColdPath

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
