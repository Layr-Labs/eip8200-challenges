import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Reference.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM

theorem activeWordsAfter_eq (active : UInt256) (offset size high : Nat)
    (hactive : active.toNat = high) (hrange : offset + size ≤ 32 * high)
    (hhigh : high < 2 ^ 256) :
    (UInt256.ofNat (MachineState.activeWordsAfter active.toNat offset size)).toNat =
      high := by
  have hafter : MachineState.activeWordsAfter active.toNat offset size = high := by
    rw [hactive, MachineState.activeWordsAfter]
    split
    · rfl
    · apply Nat.max_eq_left
      have hlast : (offset + size - 1) / 32 < high := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      omega
  rw [hafter, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hhigh]

theorem activeWordsAfter_nat_eq (high offset size : Nat)
    (hrange : offset + size ≤ 32 * high) :
    MachineState.activeWordsAfter high offset size = high := by
  rw [MachineState.activeWordsAfter]
  split
  · rfl
  · apply Nat.max_eq_left
    rw [Nat.le_iff_lt_add_one]
    have hlast : (offset + size - 1) / 32 < high := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

theorem addProgress_preserves (memory : ByteArray) (active mask : UInt256)
    (dst src count high : Nat) (hactive : active.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hsrc : src + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitSrc : src + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.addProgress memory active (UInt256.ofNat dst)
      (UInt256.ofNat src) mask count).activeWords.toNat = high := by
  induction count with
  | zero => simpa [BigHelpers.addProgress] using hactive
  | succ count ih =>
      simp only [BigHelpers.addProgress]
      rw [BigHelpers.addOffset_toNat dst count (by omega),
        BigHelpers.addOffset_toNat src count (by omega)]
      have hbefore := ih (by omega) (by omega) (by omega) (by omega)
      have hdstTouch := activeWordsAfter_eq
        (BigHelpers.addProgress memory active (UInt256.ofNat dst)
          (UInt256.ofNat src) mask count).activeWords
        (dst + 32 * count) 32 high hbefore (by omega) hhigh
      rw [hdstTouch]
      have hsrcTouch := activeWordsAfter_nat_eq high (src + 32 * count) 32
        (by omega)
      have hword : (UInt256.ofNat high).toNat = high := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt hhigh]
      rw [hsrcTouch, hword]
      have hdstNat := activeWordsAfter_nat_eq high (dst + 32 * count) 32
        (by omega)
      rw [hdstNat, hword]

theorem subtractProgress_preserves (memory : ByteArray) (active : UInt256)
    (dst modulus count high : Nat) (hactive : active.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hmodulus : modulus + 32 * count ≤ 32 * high)
    (hcandidate : 5120 + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitModulus : modulus + 32 * count < 2 ^ 256)
    (hfitCandidate : 5120 + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.subtractProgress memory active (UInt256.ofNat dst)
      (UInt256.ofNat modulus) count).activeWords.toNat = high := by
  induction count with
  | zero => simpa [BigHelpers.subtractProgress] using hactive
  | succ count ih =>
      simp only [BigHelpers.subtractProgress]
      rw [BigHelpers.addOffset_toNat dst count (by omega),
        BigHelpers.addOffset_toNat modulus count (by omega),
        BigHelpers.addOffset_toNat 5120 count (by omega)]
      have hbefore := ih (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hdstTouch := activeWordsAfter_eq
        (BigHelpers.subtractProgress memory active (UInt256.ofNat dst)
          (UInt256.ofNat modulus) count).activeWords
        (dst + 32 * count) 32 high hbefore (by omega) hhigh
      rw [hdstTouch]
      have hword : (UInt256.ofNat high).toNat = high := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt hhigh]
      have hmodTouch := activeWordsAfter_nat_eq high
        (modulus + 32 * count) 32 (by omega)
      rw [hmodTouch, hword]
      have hcandTouch := activeWordsAfter_nat_eq high
        (5120 + 32 * count) 32 (by omega)
      rw [hcandTouch, hword]

theorem selectProgress_preserves (memory : ByteArray) (active mask : UInt256)
    (dst count high : Nat) (hactive : active.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hcandidate : 5120 + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitCandidate : 5120 + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.selectProgress memory active (UInt256.ofNat dst) mask
      count).activeWords.toNat = high := by
  induction count with
  | zero => simpa [BigHelpers.selectProgress] using hactive
  | succ count ih =>
      simp only [BigHelpers.selectProgress]
      rw [BigHelpers.addOffset_toNat dst count (by omega),
        BigHelpers.addOffset_toNat 5120 count (by omega)]
      have hbefore := ih (by omega) (by omega) (by omega) (by omega)
      have hdstTouch := activeWordsAfter_eq
        (BigHelpers.selectProgress memory active (UInt256.ofNat dst) mask
          count).activeWords
        (dst + 32 * count) 32 high hbefore (by omega) hhigh
      rw [hdstTouch]
      have hword : (UInt256.ofNat high).toNat = high := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt hhigh]
      have hcandTouch := activeWordsAfter_nat_eq high
        (5120 + 32 * count) 32 (by omega)
      rw [hcandTouch, hword]
      have hdstNat := activeWordsAfter_nat_eq high
        (dst + 32 * count) 32 (by omega)
      rw [hdstNat, hword]

theorem addReturned_preserves (s : State) (dst src modulus count high : Nat)
    (take returnDest : UInt256) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hsrc : src + 32 * count ≤ 32 * high)
    (hmodulus : modulus + 32 * count ≤ 32 * high)
    (hcandidate : 5120 + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitSrc : src + 32 * count < 2 ^ 256)
    (hfitModulus : modulus + 32 * count < 2 ^ 256)
    (hfitCandidate : 5120 + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.addReturned s (UInt256.ofNat dst) (UInt256.ofNat src) take
      (UInt256.ofNat modulus) count returnDest rest).activeWords.toNat =
      high := by
  let mask := 0 - take
  let added := BigHelpers.addProgress s.memory s.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat src) mask count
  let subtracted := BigHelpers.subtractProgress added.memory
    added.activeWords (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  let useSub := UInt256.lor added.carry (UInt256.isZero subtracted.borrow)
  change (BigHelpers.selectProgress subtracted.memory subtracted.activeWords
    (UInt256.ofNat dst) (0 - useSub) count).activeWords.toNat = high
  apply selectProgress_preserves
  · apply subtractProgress_preserves
    · apply addProgress_preserves <;> assumption
    all_goals assumption
  all_goals assumption

theorem copyWords_preserves (active : UInt256) (dst src count high : Nat)
    (hactive : active.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hsrc : src + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitSrc : src + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.copyWords active (UInt256.ofNat dst) (UInt256.ofNat src)
      count).toNat = high := by
  induction count with
  | zero => simpa [BigHelpers.copyWords] using hactive
  | succ count ih =>
      rw [BigHelpers.copyWords,
        BigHelpers.clearOffset_toNat src count (by omega),
        BigHelpers.clearOffset_toNat dst count (by omega)]
      have hbefore := ih (by omega) (by omega) (by omega) (by omega)
      have hsrcTouch := activeWordsAfter_eq
        (BigHelpers.copyWords active (UInt256.ofNat dst) (UInt256.ofNat src)
          count) (src + 32 * count) 32 high hbefore (by omega) hhigh
      rw [hsrcTouch]
      have hword : (UInt256.ofNat high).toNat = high := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt hhigh]
      have hdstTouch := activeWordsAfter_nat_eq high (dst + 32 * count) 32
        (by omega)
      rw [hdstTouch, hword]

theorem copyReturned_preserves (s : State) (dst src count high : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high)
    (hdst : dst + 32 * count ≤ 32 * high)
    (hsrc : src + 32 * count ≤ 32 * high)
    (hfitDst : dst + 32 * count < 2 ^ 256)
    (hfitSrc : src + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.copyReturned s (UInt256.ofNat dst) (UInt256.ofNat src)
      count returnDest rest).activeWords.toNat = high := by
  exact copyWords_preserves s.activeWords dst src count high hactive hdst hsrc
    hfitDst hfitSrc hhigh

theorem baseBitProgress_preserves (s : State) (count j high : Nat)
    (byte : UInt256) (hactive : s.activeWords.toNat = high)
    (hcount : count ≤ 32) (hhigh : high = 192 + count) :
    (BigBase.bitProgress count byte j s).activeWords.toNat = high := by
  have hactive' : s.activeWords.toNat = 192 + count := hactive.trans hhigh
  have hresult :
      (BigBase.bitProgress count byte j s).activeWords.toNat =
        192 + count := by
    induction j with
    | zero => exact hactive'
    | succ j ih =>
        let before := BigBase.bitProgress count byte j s
        let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 875 []
        have hdoubled : doubled.activeWords.toNat = 192 + count := by
          apply addReturned_preserves before 1024 1024 0 count (192 + count)
            1 875 [] ih <;> omega
        have hstep := addReturned_preserves doubled 1024 3072 0 count
          (192 + count) (BigBase.baseBit byte j) 900 [] hdoubled
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
        have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
        have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
        have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
        simpa [BigBase.bitProgress, before, doubled, h1024, h3072,
          hzero] using hstep
  exact hresult.trans hhigh.symm

theorem baseProgress_preserves (s : State) (count baseOff steps high : Nat)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hhigh : high = 192 + count) :
    (BigBase.baseProgress count baseOff steps s).activeWords.toNat = high := by
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      apply baseBitProgress_preserves
      · exact ih
      · exact hcount
      · exact hhigh

theorem clearWords_aligned_succ (active : UInt256) (ptrWords i : Nat)
    (hactive : active.toNat ≤ ptrWords)
    (hfit : 32 * (ptrWords + i + 1) < 2 ^ 256) :
    (BigHelpers.clearWords active (UInt256.ofNat (32 * ptrWords))
      (i + 1)).toNat = ptrWords + i + 1 := by
  induction i with
  | zero =>
      rw [show 0 + 1 = Nat.succ 0 by omega, BigHelpers.clearWords,
        BigHelpers.clearOffset_toNat (32 * ptrWords) 0 (by omega)]
      simp only [BigHelpers.clearWords]
      have hafter : MachineState.activeWordsAfter active.toNat
          (32 * ptrWords + 32 * 0) 32 = ptrWords + 1 := by
        rw [MachineState.activeWordsAfter, if_neg (by omega)]
        have hoff : 32 * ptrWords + 32 * 0 + 32 - 1 =
            32 * ptrWords + 31 := by omega
        rw [hoff]
        dsimp
        rw [Nat.mul_add_div (by omega)]
        norm_num
        omega
      rw [hafter, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
  | succ i ih =>
      rw [show i + 1 + 1 = (i + 1) + 1 by omega,
        BigHelpers.clearWords, ih (by omega)]
      rw [BigHelpers.clearOffset_toNat (32 * ptrWords) (i + 1) (by omega)]
      have hafter : MachineState.activeWordsAfter (ptrWords + i + 1)
          (32 * ptrWords + 32 * (i + 1)) 32 = ptrWords + i + 2 := by
        rw [MachineState.activeWordsAfter, if_neg (by omega)]
        have hoff : 32 * ptrWords + 32 * (i + 1) + 32 - 1 =
            32 * (ptrWords + i + 1) + 31 := by omega
        rw [hoff]
        dsimp
        rw [Nat.mul_add_div (by omega)]
        norm_num
      rw [hafter, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega

theorem clearWords_preserves (active : UInt256) (ptr count high : Nat)
    (hactive : active.toNat = high)
    (hrange : ptr + 32 * count ≤ 32 * high)
    (hfit : ptr + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.clearWords active (UInt256.ofNat ptr) count).toNat = high := by
  induction count with
  | zero => simpa [BigHelpers.clearWords] using hactive
  | succ count ih =>
      rw [BigHelpers.clearWords,
        BigHelpers.clearOffset_toNat ptr count (by omega)]
      apply activeWordsAfter_eq
      · exact ih (by omega) (by omega)
      · omega
      · exact hhigh

theorem clearReturned_preserves (s : State) (ptr count high : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high)
    (hrange : ptr + 32 * count ≤ 32 * high)
    (hfit : ptr + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigHelpers.clearReturned s (UInt256.ofNat ptr) count returnDest
      rest).activeWords.toNat = high := by
  exact clearWords_preserves s.activeWords ptr count high hactive hrange hfit
    hhigh

theorem baseLoopEntry_preserves (s : State) (accumulator : UInt256)
    (count high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hhigh : high = 192 + count) :
    (BigBase.baseLoopEntry s accumulator count rest).activeWords.toNat =
      high := by
  let cleared := BigBase.afterClearDouble s accumulator count rest
  let scanned := BigModulus.scanNonzero s count rest
  have hscanned : scanned.activeWords.toNat = high := by
    have aux : ∀ steps : Nat, steps ≤ count →
        (BigModulus.scanWords s.activeWords steps).toNat = high := by
      intro steps hsteps
      induction steps with
      | zero => simpa [BigModulus.scanWords] using hactive
      | succ steps ih =>
          rw [BigModulus.scanWords]
          apply activeWordsAfter_eq
          · exact ih (by omega)
          · omega
          · omega
    have hscanRaw := aux count (by rfl)
    simpa [scanned, BigModulus.scanNonzero] using hscanRaw
  have hcleared : cleared.activeWords.toNat = high := by
    have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
    simpa [cleared, BigBase.afterClearDouble, h3072] using
      clearReturned_preserves scanned 3072 count high 823
        (BigBase.frame accumulator count rest) hscanned (by omega) (by omega)
        (by omega)
  have htouch := activeWordsAfter_eq cleared.activeWords 3072 32 high hcleared
    (by omega) (by omega)
  simpa [BigBase.baseLoopEntry, cleared, BigBase.afterClearDouble] using htouch

theorem initialAccumulator_preserves (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hhigh : high = 192 + count) :
    (BigBaseLoop.initialAccumulator s accumulator count baseSize e m baseOff
      rest).activeWords.toNat = high := by
  let progress := BigBase.baseProgress count baseOff baseSize s
  have hprogress : progress.activeWords.toNat = high :=
    baseProgress_preserves s count baseOff baseSize high hactive hcount hhigh
  let exit := BigBaseLoop.baseConvertedExit s accumulator count baseSize e m
    baseOff rest
  have hexit : exit.activeWords.toNat = high := by
    simpa [exit, BigBaseLoop.baseConvertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogress
  have hresult := addReturned_preserves exit 2048 3072 0 count high 1 944
    ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++
      [UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
    hexit (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [BigBaseLoop.initialAccumulator, exit, h2048, h3072, hzero] using
    hresult

theorem mulWordProgress_preserves (s : State) (word returnDest : UInt256)
    (a b out modulus count i steps high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high)
    (hout : out + 32 * count ≤ 32 * high)
    (hmodulus : modulus + 32 * count ≤ 32 * high)
    (hfitOut : out + 32 * count < 2 ^ 256)
    (hfitModulus : modulus + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) (hshape : high = 192 + count)
    (hcount : count ≤ 32) :
    (BigMul.mulWordProgress s word (UInt256.ofNat a) (UInt256.ofNat b)
      (UInt256.ofNat out) (UInt256.ofNat modulus) count i returnDest rest
      steps).activeWords.toNat = high := by
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      let before := BigMul.mulWordProgress s word (UInt256.ofNat a)
        (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count i
        returnDest rest steps
      let inner := BigMul.mulInnerState before word (UInt256.ofNat a)
        (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count i
        steps returnDest rest
      have hinner : inner.activeWords.toNat = high := by
        simpa [inner, BigMul.mulInnerState, before] using ih
      let afterAdd := BigMul.mulWordAfterAdd before word (UInt256.ofNat a)
        (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count i
        steps returnDest rest
      have hadd : afterAdd.activeWords.toNat = high := by
        have h383 : (383 : UInt256) = UInt256.ofNat 383 := by decide
        simpa [afterAdd, BigMul.mulWordAfterAdd, inner, h383] using
          addReturned_preserves inner out 4096 modulus count high
            (BigMul.mulWordBit word steps) 383
            (BigMul.mulWordRest word (UInt256.ofNat a) (UInt256.ofNat b)
              (UInt256.ofNat out) (UInt256.ofNat modulus) count i steps
              returnDest rest)
            hinner hout (by omega) hmodulus (by omega) hfitOut (by omega)
            hfitModulus (by omega) hhigh
      let doubled := BigMul.mulWordAfterDouble before word (UInt256.ofNat a)
        (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count i
        steps returnDest rest
      have hdouble : doubled.activeWords.toNat = high := by
        have h401 : (401 : UInt256) = UInt256.ofNat 401 := by decide
        have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
        simpa [doubled, BigMul.mulWordAfterDouble, afterAdd, h401, hone] using
          addReturned_preserves afterAdd 4096 4096 modulus count high 1 401
            (BigMul.mulWordRest word (UInt256.ofNat a) (UInt256.ofNat b)
              (UInt256.ofNat out) (UInt256.ofNat modulus) count i steps
              returnDest rest)
            hadd (by omega) (by omega) hmodulus (by omega) (by omega)
            (by omega) hfitModulus (by omega) hhigh
      simpa [BigMul.mulWordProgress, doubled] using hdouble

theorem mulOuterProgress_preserves (s : State) (returnDest : UInt256)
    (a b out modulus count steps high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high) (hsteps : steps ≤ count)
    (hb : b + 32 * count ≤ 32 * high)
    (hout : out + 32 * count ≤ 32 * high)
    (hmodulus : modulus + 32 * count ≤ 32 * high)
    (hfitB : b + 32 * count < 2 ^ 256)
    (hfitOut : out + 32 * count < 2 ^ 256)
    (hfitModulus : modulus + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) (hshape : high = 192 + count)
    (hcount : count ≤ 32) :
    (BigMul.mulOuterProgress s (UInt256.ofNat a) (UInt256.ofNat b)
      (UInt256.ofNat out) (UInt256.ofNat modulus) count returnDest rest
      steps).activeWords.toNat = high := by
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      let before := BigMul.mulOuterProgress s (UInt256.ofNat a)
        (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count
        returnDest rest steps
      have hbefore : before.activeWords.toNat = high := ih (by omega)
      let loaded := BigMul.mulLoadedState before (UInt256.ofNat b) steps
      have hloaded : loaded.activeWords.toNat = high := by
        have hoff := BigHelpers.addOffset_toNat b steps (by omega)
        have htouch := activeWordsAfter_eq before.activeWords (b + 32 * steps)
          32 high hbefore (by omega) hhigh
        simpa [loaded, BigMul.mulLoadedState, hoff] using htouch
      have hword := mulWordProgress_preserves loaded
        (BigMul.mulLoadedWord before (UInt256.ofNat b) steps) returnDest a b
        out modulus count steps 256 high rest hloaded hout hmodulus hfitOut
        hfitModulus hhigh hshape hcount
      simpa [BigMul.mulOuterProgress, before, loaded] using hword

theorem loadWords_preserves (active : UInt256) (dst length steps high : Nat)
    (hactive : active.toNat = high) (hsteps : steps ≤ length)
    (hlength : length < 2 ^ 256)
    (hrange : dst + 32 * Limbs.limbCount length ≤ 32 * high)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hhigh : high < 2 ^ 256) :
    (BigLoad.loadWords active (UInt256.ofNat dst) length steps).toNat =
      high := by
  induction steps with
  | zero => simpa [BigLoad.loadWords] using hactive
  | succ steps ih =>
      rw [BigLoad.loadWords,
        BigLoadCorrect.loadAt_ofNat dst length steps hlength (by omega) hfit]
      have hoff : dst + 32 * BigLoad.loadLimb length steps + 32 ≤
          32 * high := by
        have hlimb : BigLoad.loadLimb length steps <
            Limbs.limbCount length := by
          unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
          omega
        omega
      have hfirst := activeWordsAfter_eq
        (BigLoad.loadWords active (UInt256.ofNat dst) length steps)
        (dst + 32 * BigLoad.loadLimb length steps) 32 high
        (ih (by omega)) hoff hhigh
      rw [hfirst]
      have hsecond : MachineState.activeWordsAfter high
          (dst + 32 * BigLoad.loadLimb length steps) 32 = high := by
        rw [MachineState.activeWordsAfter, if_neg (by omega)]
        apply Nat.max_eq_left
        rw [Nat.le_iff_lt_add_one]
        have hlast :
            (dst + 32 * BigLoad.loadLimb length steps + 32 - 1) / 32 <
              high := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega
      rw [hsecond, Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hhigh]

theorem scanWords_preserves (active : UInt256) (steps high : Nat)
    (hactive : active.toNat = high) (hsteps : steps ≤ high)
    (hhigh : high < 2 ^ 256) :
    (BigModulus.scanWords active steps).toNat = high := by
  induction steps with
  | zero => simpa [BigModulus.scanWords] using hactive
  | succ steps ih =>
      rw [BigModulus.scanWords]
      apply activeWordsAfter_eq
      · exact ih (by omega)
      · omega
      · exact hhigh

theorem mulResult_preserves (s : State) (returnDest : UInt256)
    (a b out modulus count high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high)
    (ha : a + 32 * count ≤ 32 * high)
    (hb : b + 32 * count ≤ 32 * high)
    (hout : out + 32 * count ≤ 32 * high)
    (hmodulus : modulus + 32 * count ≤ 32 * high)
    (hfitA : a + 32 * count < 2 ^ 256)
    (hfitB : b + 32 * count < 2 ^ 256)
    (hfitOut : out + 32 * count < 2 ^ 256)
    (hfitModulus : modulus + 32 * count < 2 ^ 256)
    (hhigh : high < 2 ^ 256) (hshape : high = 192 + count)
    (hcount : count ≤ 32) :
    (BigExponent.mulResult s (UInt256.ofNat a) (UInt256.ofNat b)
      (UInt256.ofNat out) (UInt256.ofNat modulus) count returnDest
      rest).activeWords.toNat = high := by
  let cleared := BigMul.mulAfterClear s (UInt256.ofNat a) (UInt256.ofNat b)
    (UInt256.ofNat out) (UInt256.ofNat modulus) count returnDest rest
  have hcleared : cleared.activeWords.toNat = high := by
    simpa [cleared, BigMul.mulAfterClear] using
      clearWords_preserves s.activeWords out count high hactive hout hfitOut
        hhigh
  let copied := BigMul.mulAfterCopy s (UInt256.ofNat a) (UInt256.ofNat b)
    (UInt256.ofNat out) (UInt256.ofNat modulus) count returnDest rest
  have hcopied : copied.activeWords.toNat = high := by
    simpa [copied, BigMul.mulAfterCopy, cleared] using
      copyWords_preserves cleared.activeWords 4096 a count high hcleared
        (by omega) ha (by omega) hfitA hhigh
  let progress := BigMul.mulOuterProgress copied (UInt256.ofNat a)
    (UInt256.ofNat b) (UInt256.ofNat out) (UInt256.ofNat modulus) count
    returnDest rest count
  have hprogress : progress.activeWords.toNat = high := by
    exact mulOuterProgress_preserves copied returnDest a b out modulus count
      count high rest hcopied (by rfl) hb hout hmodulus hfitB hfitOut
      hfitModulus hhigh hshape hcount
  simpa [BigExponent.mulResult, copied, progress, BigMul.mulReturned] using
    hprogress

theorem exponentSelectWords_preserves (active : UInt256)
    (steps count high : Nat)
    (hactive : active.toNat = high) (hsteps : steps ≤ count)
    (hcount : count ≤ 32)
    (hshape : high = 192 + count) :
    (BigExponent.selectWords active steps).toNat = high := by
  induction steps with
  | zero => simpa [BigExponent.selectWords] using hactive
  | succ steps ih =>
      rw [BigExponent.selectWords]
      have hbefore := ih (by omega)
      have haddr2048 :
          (2048 + BigExponent.selectOffset steps).toNat =
            2048 + 32 * steps := by
        rw [show (2048 : UInt256) = UInt256.ofNat 2048 by decide]
        exact BigHelpers.addOffset_toNat 2048 steps (by omega)
      have haddr3072 :
          (3072 + BigExponent.selectOffset steps).toNat =
            3072 + 32 * steps := by
        rw [show (3072 : UInt256) = UInt256.ofNat 3072 by decide]
        exact BigHelpers.addOffset_toNat 3072 steps (by omega)
      rw [haddr2048, haddr3072]
      have hsquare := activeWordsAfter_eq
        (BigExponent.selectWords active steps) (2048 + 32 * steps) 32 high
        hbefore (by omega) (by omega)
      rw [hsquare]
      have hword : (UInt256.ofNat high).toNat = high := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      rw [activeWordsAfter_nat_eq high (3072 + 32 * steps) 32 (by omega),
        hword,
        activeWordsAfter_nat_eq high (2048 + 32 * steps) 32 (by omega),
        hword]

theorem exponentSelectProgress_preserves (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) (high : Nat)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hshape : high = 192 + count) :
    (BigExponent.selectProgress s accumulatorWord count b e m baseOff expOff
      i j offset byte rest count).activeWords.toNat = high := by
  let inner := BigExponent.innerBody s accumulatorWord count b e m baseOff
    expOff i offset byte rest j
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hinner : inner.activeWords.toNat = high := by
    simpa [inner, BigExponent.innerBody, BigExponent.innerLoop] using hactive
  let square := BigExponent.squareReturned s accumulatorWord count b e m
    baseOff expOff i j offset byte rest
  have hsquare : square.activeWords.toNat = high := by
    have h := mulResult_preserves inner 1000 2048 2048 3072 0 count high
      (BigExponent.bitFrame accumulatorWord count b e m baseOff expOff i j
        offset byte (BigExponent.exponentBit byte j) rest)
      hinner (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hshape hcount
    simpa [square, BigExponent.squareReturned, inner, h0, h2048, h3072]
      using h
  let copied := BigExponent.copiedSquare s accumulatorWord count b e m
    baseOff expOff i j offset byte rest
  have hcopied : copied.activeWords.toNat = high := by
    have h := copyReturned_preserves square 2048 3072 count high 1015
      (BigExponent.bitFrame accumulatorWord count b e m baseOff expOff i j
        offset byte (BigExponent.exponentBit byte j) rest)
      hsquare (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [copied, BigExponent.copiedSquare, square, h2048, h3072] using h
  let product := BigExponent.productReturned s accumulatorWord count b e m
    baseOff expOff i j offset byte rest
  have hproduct : product.activeWords.toNat = high := by
    have h := mulResult_preserves copied 1034 2048 1024 3072 0 count high
      (BigExponent.bitFrame accumulatorWord count b e m baseOff expOff i j
        offset byte (BigExponent.exponentBit byte j) rest)
      hcopied (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hshape hcount
    simpa [product, BigExponent.productReturned, copied, h0, h1024, h2048,
      h3072] using h
  have hselect := exponentSelectWords_preserves product.activeWords count count
    high hproduct (by rfl) hcount hshape
  simpa [BigExponent.selectProgress, product] using hselect

theorem exponentBitProgress_preserves (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (steps high : Nat)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hshape : high = 192 + count) :
    (BigExponent.exponentBitProgress s accumulatorWord count b e m baseOff
      expOff i offset byte rest steps).activeWords.toNat = high := by
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      simpa [BigExponent.exponentBitProgress] using
        exponentSelectProgress_preserves
          (BigExponent.exponentBitProgress s accumulatorWord count b e m
            baseOff expOff i offset byte rest steps)
          accumulatorWord count b e m baseOff expOff i steps offset byte rest
          high ih hcount hshape

theorem exponentByteProgress_preserves (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (steps high : Nat)
    (hactive : s.activeWords.toNat = high) (hcount : count ≤ 32)
    (hshape : high = 192 + count) :
    (BigExponent.exponentByteProgress s accumulatorWord count b e m baseOff
      expOff rest steps).activeWords.toNat = high := by
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      let before := BigExponent.exponentByteProgress s accumulatorWord count b
        e m baseOff expOff rest steps
      let offset := UInt256.ofNat (expOff + steps)
      let byte := BigExponent.loadedExponentByte before expOff steps
      simpa [BigExponent.exponentByteProgress, before, offset, byte] using
        exponentBitProgress_preserves before accumulatorWord count b e m
          baseOff expOff steps offset byte rest 8 high ih hcount hshape

theorem serializeWords_preserves (active : UInt256)
    (m steps count high : Nat) (hactive : active.toNat = high)
    (hsteps : steps ≤ m) (hm : m ≤ 1024)
    (hcount : count = Limbs.limbCount m)
    (hshape : high = 192 + count) :
    (BigSerialize.serializeWords active m steps).toNat = high := by
  induction steps with
  | zero => simpa [BigSerialize.serializeWords] using hactive
  | succ steps ih =>
      rw [BigSerialize.serializeWords]
      have hbefore : (BigSerialize.serializeWords active m steps).toNat =
          high := ih (by omega)
      have hm256 : m < 2 ^ 256 := by omega
      have hlimbEq := BigSerializeCorrect.serializerLimb_eq m steps hm256
        (by omega)
      let limb := BigLoad.loadLimb m steps
      have hlimb : limb < Limbs.limbCount m := by
        simp only [limb, BigLoad.loadLimb, BigLoad.loadReverse,
          Limbs.limbCount]
        omega
      have hlimb32 : limb < 32 := by
        have hn := Limbs.limbCount_le_32 m hm
        omega
      have hcount32 : count ≤ 32 := by
        rw [hcount]
        exact Limbs.limbCount_le_32 m hm
      have haddr :
          (2048 + UInt256.shiftLeft (BigSerialize.serializerLimb m steps)
            (UInt256.ofNat 5)).toNat = 2048 + 32 * limb := by
        rw [show (2048 : UInt256) = UInt256.ofNat 2048 by decide, hlimbEq]
        exact BigHelpers.addOffset_toNat 2048 limb (by omega)
      have hkaddr : (6144 + UInt256.ofNat steps).toNat = 6144 + steps := by
        rw [show (6144 : UInt256) = UInt256.ofNat 6144 by decide,
          Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      rw [haddr, hkaddr]
      have hrangeLoad : 2048 + 32 * limb + 32 ≤ 32 * high := by
        omega
      have hhigh256 : high < 2 ^ 256 := by omega
      have hload :
          (UInt256.ofNat (MachineState.activeWordsAfter
            (BigSerialize.serializeWords active m steps).toNat
            (2048 + 32 * limb) 32)).toNat = high :=
        activeWordsAfter_eq (BigSerialize.serializeWords active m steps)
          (2048 + 32 * limb) 32 high hbefore hrangeLoad hhigh256
      rw [hload]
      have hwidth := Limbs.width_le_limbs m
      rw [activeWordsAfter_nat_eq high (6144 + steps) 1 (by omega),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt hhigh256]

theorem bigReturned_preserves (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff high : Nat) (rest : List UInt256)
    (hactive : s.activeWords.toNat = high) (hm : m ≤ 1024)
    (hcount : count = Limbs.limbCount m)
    (hshape : high = 192 + count) :
    (BigSerialize.bigReturned s accumulatorWord count b e m baseOff expOff
      rest).activeWords.toNat = high := by
  have hserialized := serializeWords_preserves s.activeWords m m count high
    hactive (by rfl) hm hcount hshape
  simp only [BigSerialize.bigReturned, BigSerialize.serializeProgress]
  have hmWidth := Limbs.width_le_limbs m
  have hcount32 : count ≤ 32 := by
    rw [hcount]
    exact Limbs.limbCount_le_32 m hm
  have hrange : 6144 + m ≤ 32 * high := by omega
  have hhigh256 : high < 2 ^ 256 := by omega
  rw [hserialized, activeWordsAfter_nat_eq high 6144 m hrange,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hhigh256]

theorem setupState_activeWords (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (BigComplete.setupState (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) ReferenceCorrect.bigReturnDest
      (ReferenceCorrect.bigRest input)).activeWords.toNat =
        192 + Limbs.limbCount (modulusSize input) := by
  simp only [BigComplete.setupState, BigSetup.setupReturned,
    BigSetup.afterClear6144, BigSetup.afterClear2048,
    BigSetup.afterClear1024, BigSetup.afterClear0, BigHelpers.clearReturned,
    BigLoad.loadReturned, BigLoad.loadLoop]
  let m := modulusSize input
  let n := Limbs.limbCount m
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hm256 : m < 2 ^ 256 := by omega
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hnpos : 0 < n := by
    simp only [n, Limbs.limbCount]
    omega
  have hn256 : 192 + n < 2 ^ 256 := by omega
  have h0 :
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n).toNat =
        n := by
    have h := clearWords_aligned_succ
      (Main.headerState input).activeWords 0 (n - 1) (by rfl) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 0) = 0 by decide] at h
    omega
  have h1024 :
      (BigHelpers.clearWords
        (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
        1024 n).toNat = 32 + n := by
    have h := clearWords_aligned_succ
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n) 32
      (n - 1) (by rw [h0]; omega) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 32) = 1024 by decide] at h
    omega
  have h2048 :
      (BigHelpers.clearWords
        (BigHelpers.clearWords
          (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
          1024 n) 2048 n).toNat = 64 + n := by
    have h := clearWords_aligned_succ
      (BigHelpers.clearWords
        (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
        1024 n) 64 (n - 1) (by rw [h1024]; omega) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 64) = 2048 by decide] at h
    omega
  let before6144 := BigHelpers.clearWords
    (BigHelpers.clearWords
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
      1024 n) 2048 n
  have h6144 :
      (BigHelpers.clearWords before6144 6144 n).toNat = 192 + n := by
    have hprior : before6144.toNat ≤ 192 := by
      rw [show before6144.toNat = 64 + n by
        simpa [before6144] using h2048]
      omega
    have h := clearWords_aligned_succ before6144 192 (n - 1) hprior
      (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 192) = 6144 by decide] at h
    omega
  let cleared := BigHelpers.clearWords before6144 6144 n
  have hload : (BigLoad.loadWords cleared 0 m m).toNat = 192 + n := by
    apply loadWords_preserves cleared 0 m m (192 + n)
    · simpa [cleared] using h6144
    · rfl
    · exact hm256
    · omega
    · omega
    · exact hn256
  rw [show modulusSize input = m by rfl]
  have hmword : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm256]
  rw [hmword]
  simpa [before6144, cleared, m, n] using hload

theorem bigZeroFinalState_activeWords (input : ByteArray)
    (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (ReferenceCorrect.bigZeroFinalState input).activeWords.toNat =
      192 + Limbs.limbCount (modulusSize input) := by
  simp only [ReferenceCorrect.bigZeroFinalState, BigZeroCorrect.zeroFinalState,
    BigComplete.setupState, BigSetup.setupReturned, BigSetup.afterClear6144,
    BigSetup.afterClear2048, BigSetup.afterClear1024, BigSetup.afterClear0,
    BigHelpers.clearReturned, BigLoad.loadReturned, BigLoad.loadLoop,
    BigModulus.scanZeroFinal]
  let m := modulusSize input
  let n := Limbs.limbCount m
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hm256 : m < 2 ^ 256 := by omega
  have hn : n ≤ 32 := by
    exact Limbs.limbCount_le_32 m hm
  have hnpos : 0 < n := by
    simp only [n, Limbs.limbCount]
    omega
  have hn256 : 192 + n < 2 ^ 256 := by omega
  have h0 :
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n).toNat =
        n := by
    have h := clearWords_aligned_succ
      (Main.headerState input).activeWords 0 (n - 1) (by rfl) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 0) = 0 by decide] at h
    omega
  have h1024 :
      (BigHelpers.clearWords
        (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
        1024 n).toNat = 32 + n := by
    have h := clearWords_aligned_succ
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n) 32
      (n - 1) (by rw [h0]; omega) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 32) = 1024 by decide] at h
    omega
  have h2048 :
      (BigHelpers.clearWords
        (BigHelpers.clearWords
          (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
          1024 n) 2048 n).toNat = 64 + n := by
    have h := clearWords_aligned_succ
      (BigHelpers.clearWords
        (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
        1024 n) 64 (n - 1) (by rw [h1024]; omega) (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 64) = 2048 by decide] at h
    omega
  let before6144 := BigHelpers.clearWords
    (BigHelpers.clearWords
      (BigHelpers.clearWords (Main.headerState input).activeWords 0 n)
      1024 n) 2048 n
  have h6144 :
      (BigHelpers.clearWords before6144 6144 n).toNat = 192 + n := by
    have hprior : before6144.toNat ≤ 192 := by
      rw [show before6144.toNat = 64 + n by simpa [before6144] using h2048]
      omega
    have h := clearWords_aligned_succ before6144 192 (n - 1)
      hprior (by omega)
    rw [show n - 1 + 1 = n by omega] at h
    rw [show UInt256.ofNat (32 * 192) = 6144 by decide] at h
    omega
  let cleared := BigHelpers.clearWords before6144 6144 n
  have hload : (BigLoad.loadWords cleared 0 m m).toNat = 192 + n := by
    apply loadWords_preserves cleared 0 m m (192 + n)
    · simpa [cleared] using h6144
    · rfl
    · exact hm256
    · omega
    · omega
    · exact hn256
  let loaded := BigLoad.loadWords cleared 0 m m
  have hscan : (BigModulus.scanWords loaded n).toNat = 192 + n := by
    apply scanWords_preserves loaded n (192 + n)
    · simpa [loaded] using hload
    · omega
    · exact hn256
  rw [show modulusSize input = m by rfl]
  have hmword : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hm256]
  rw [hmword]
  change (UInt256.ofNat (MachineState.activeWordsAfter
      (BigModulus.scanWords
        (BigLoad.loadWords
          (BigHelpers.clearWords before6144 6144 n) 0 m m) n).toNat
      6144 m)).toNat = 192 + n
  rw [show BigHelpers.clearWords before6144 6144 n = cleared by rfl,
    show BigLoad.loadWords cleared 0 m m = loaded by rfl, hscan]
  have hmWidth : m ≤ 32 * n := by
    exact Limbs.width_le_limbs m
  have hafter : MachineState.activeWordsAfter (192 + n) 6144 m =
      192 + n := by
    rw [MachineState.activeWordsAfter]
    split
    · rfl
    · apply Nat.max_eq_left
      rw [Nat.le_iff_lt_add_one]
      have hlast : (6144 + m - 1) / 32 < 192 + n := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      omega
  rw [hafter, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hn256]

theorem bigCompletedState_activeWords (input : ByteArray)
    (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input) :
    (ReferenceCorrect.bigCompletedState input).activeWords.toNat =
      192 + Limbs.limbCount (modulusSize input) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let n := Limbs.limbCount m
  let high := 192 + n
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let ret := ReferenceCorrect.bigReturnDest
  let rest := ReferenceCorrect.bigRest input
  let setup := BigComplete.setupState (Main.headerState input) b e m 96 expOff
    modOff ret rest
  let accumulator := BigComplete.modulusOr (Main.headerState input) b e m 96
    expOff modOff ret rest
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hsetup : setup.activeWords.toNat = high := by
    simpa [setup, b, e, m, n, high, expOff, modOff, ret, rest] using
      setupState_activeWords input hvalid hbig
  let base := BigComplete.baseState (Main.headerState input) b e m 96 expOff
    modOff ret rest
  have hbase : base.activeWords.toNat = high := by
    have h := baseLoopEntry_preserves setup accumulator n high
      (BigComplete.scanRest b e m 96 expOff modOff ret rest) hsetup hn rfl
    simpa [base, BigComplete.baseState, setup, accumulator,
      BigComplete.limbCount, n] using h
  let exponent := BigComplete.exponentState (Main.headerState input) b e m 96
    expOff modOff ret rest
  have hexponent : exponent.activeWords.toNat = high := by
    have h := initialAccumulator_preserves base accumulator n b e m 96 high
      (BigComplete.baseRest expOff modOff ret rest) hbase hn rfl
    simpa [exponent, BigComplete.exponentState, base, accumulator,
      BigComplete.limbCount, n] using h
  let progress := BigComplete.exponentProgressState (Main.headerState input) b
    e m 96 expOff modOff ret rest
  have hprogress : progress.activeWords.toNat = high := by
    have h := exponentByteProgress_preserves exponent accumulator n b e m 96
      expOff (BigComplete.exponentRest modOff ret rest) e high hexponent hn rfl
    simpa [progress, BigComplete.exponentProgressState, exponent, accumulator,
      BigComplete.limbCount, n] using h
  have hreturned := bigReturned_preserves progress accumulator n b e m 96
    expOff high (BigComplete.exponentRest modOff ret rest) hprogress hm rfl rfl
  simpa [ReferenceCorrect.bigCompletedState, BigComplete.completedState,
    BigComplete.limbCount, progress, accumulator, b, e, m, n, high, expOff,
    modOff, ret, rest] using
    hreturned

end Challenge.Modexp.Reference.Proofs.Bytecode
