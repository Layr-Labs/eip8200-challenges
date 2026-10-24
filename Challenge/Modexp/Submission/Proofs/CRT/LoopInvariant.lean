import Challenge.Modexp.Submission.Proofs.CRT.PureLoop
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopFrames
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.LoopInvariant
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.PureLoop

/-- Saved arithmetic/configuration fields; control-flow frame fields are
excluded because retained rounds keep their saved values until ordinary exit. -/
structure Static (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame) (N : Nat) : Prop where
  s32 : MachineState.readWord mem 2688 = UInt256.ofNat 256
  tlw : MachineState.readWord mem 2784 = UInt256.ofNat 2336
  ml : MachineState.readWord mem 2752 = UInt256.ofNat 224
  w3 : MachineState.readWord mem 192 = f.w3
  tl : MachineState.readWord mem 224 = f.tl
  inv : MachineState.readWord mem 2720 = f.inv
  m0 : MachineState.readWord mem 160 = f.m0
  m96 : MachineState.readWord mem 96 = f.m96
  m64 : MachineState.readWord mem 64 = f.m64
  m32 : MachineState.readWord mem 32 = f.m32
  m128 : MachineState.readWord mem 128 = f.m128
  cachedDigits : ∀ i < 9, n i = inputWord mem 0 i
  cachedInverse : minv = MachineState.readWord mem 2720
  modulus : Model.FastRepresents mem 0 8 N
  positive : 0 < N
  odd : Odd N
  inverse : (N*minv.toNat+1)%2^256=0
  inverseGuard : f.inv ≠ UInt256.ofNat 1

theorem inputWord_live {after before : ByteArray} (h : Live after before) (i : Nat) :
    inputWord after 0 i = inputWord before 0 i := by
  unfold inputWord
  split
  · unfold CRTInputMemory.inputDigitWord
    rw [h _ (Or.inl (by unfold CRTInputMemory.loadOffset; omega))]
  · rw [h 0 (Or.inl (by decide))]

theorem Static.transport {before after : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N : Nat} (h : Static before n minv f N) (hl : Live after before) :
    Static after n minv f N where
  s32 := (hl 2688 (Or.inr (by decide))).trans h.s32
  tlw := (hl 2784 (Or.inr (by decide))).trans h.tlw
  ml := (hl 2752 (Or.inr (by decide))).trans h.ml
  w3 := (hl 192 (Or.inl (by decide))).trans h.w3
  tl := (hl 224 (Or.inl (by decide))).trans h.tl
  inv := (hl 2720 (Or.inr (by decide))).trans h.inv
  m0 := (hl 160 (Or.inl (by decide))).trans h.m0
  m96 := (hl 96 (Or.inl (by decide))).trans h.m96
  m64 := (hl 64 (Or.inl (by decide))).trans h.m64
  m32 := (hl 32 (Or.inl (by decide))).trans h.m32
  m128 := (hl 128 (Or.inl (by decide))).trans h.m128
  cachedDigits := fun i hi => (h.cachedDigits i hi).trans (inputWord_live hl i).symm
  cachedInverse := h.cachedInverse.trans (hl 2720 (Or.inr (by decide))).symm
  modulus := hl.modulus N h.modulus
  positive := h.positive
  odd := h.odd
  inverse := h.inverse
  inverseGuard := h.inverseGuard

theorem Static.flow {mem : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N : Nat} (h : Static mem n minv f N)
    (aprev counter ret : UInt256) (rest : List UInt256) :
    Static mem n minv {f with aprev := aprev, counter := counter, ret := ret, rest := rest} N := by
  rcases h with ⟨hs32, htlw, hml, hw3, htl, hinv, hm0, hm96, hm64, hm32, hm128, hdigits, hcached, hmod, hpos, hodd, hinverse, hguard⟩
  exact ⟨hs32, htlw, hml, hw3, htl, hinv, hm0, hm96, hm64, hm32, hm128, hdigits, hcached, hmod, hpos, hodd, hinverse, hguard⟩

theorem Static.nlow {mem : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N : Nat} (h : Static mem n minv f N) :
    ∀ i < 8, (n i).toNat = N/2^(244*i)%2^244 := by
  intro i hi
  rw [h.cachedDigits i (by omega)]
  exact inputWord_low h.modulus i hi

theorem Static.nhigh {mem : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N : Nat} (h : Static mem n minv f N) :
    (n 8).toNat = N/2^1952 := by
  rw [h.cachedDigits 8 (by decide)]
  exact inputWord_high h.modulus

/-- `k` is the number of squares remaining, including the current round.
The mutable counter is its natural value minus one; saved f.counter can be stale. -/
structure Invariant (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (N k A : Nat) : Prop extends Static mem n minv f N where
  operand : Represents mem A
  counter : (MachineState.readWord mem 1728).toNat = k-1
  countPositive : 1 ≤ k
  countBound : k ≤ 16

theorem Invariant.flow {mem : ByteArray} {n : Nat → UInt256} {minv : UInt256}
    {f : CRTLoopFrames.Frame} {N k A : Nat} (h : Invariant mem n minv f N k A)
    (aprev counter ret : UInt256) (rest : List UInt256) :
    Invariant mem n minv {f with aprev := aprev, counter := counter, ret := ret, rest := rest} N k A where
  toStatic := h.toStatic.flow aprev counter ret rest
  operand := h.operand
  counter := h.counter
  countPositive := h.countPositive
  countBound := h.countBound

variable (s : State) (minv : UInt256) (n : Nat → UInt256)

theorem checked_counter (mem : ByteArray) :
    MachineState.readWord (checked s minv n mem) 1728 = MachineState.readWord mem 1728 := by
  rw [checked, checked_word _ 1728 (Or.inl (by decide))]
  exact SequencePreservation.word_live {s with memory := mem} minv n [] 17 (by decide) 1728 (Or.inr (by decide))

theorem next_counter (k : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16) (mem : ByteArray)
    (hc : (MachineState.readWord mem 1728).toNat = k) :
    (MachineState.readWord (next s minv n k mem) 1728).toNat = k-1 := by
  unfold next
  split
  · rw [retained_counter_toNat _ (by rw [checked_counter s minv n mem, hc]; omega),
      checked_counter s minv n mem, hc]
  · rw [OverflowHandlerMeaning.handler_counter_toNat _ _ _ (by rw [checked_counter s minv n mem, hc]; omega),
      checked_counter s minv n mem, hc]

theorem round_invariant (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (hk : 1 ≤ k) (h : Invariant mem n minv f N (k+1) A) :
    ∃ v, Invariant (next s minv n k mem) n minv f N k v ∧
      v%N = Model.montMul N R A A := by
  have hr := one_round s minv n mem A N h.operand h.modulus h.positive h.odd h.toStatic.nlow h.toStatic.nhigh h.inverse
  let v := HistoricalSearch.MixedMontgomery.normalize R N (Q s minv n mem)
  refine ⟨v, ?_, hr.2.2⟩
  refine {h.toStatic.transport (next_live s minv n k mem) with
    operand := hr.2.1 k
    counter := ?_
    countPositive := hk
    countBound := by have := h.countBound; omega}
  exact next_counter s minv n k hk (by have := h.countBound; omega) mem (by simpa using h.counter)

#print axioms Static.transport
#print axioms Invariant.flow
#print axioms checked_counter
#print axioms next_counter
#print axioms round_invariant
end HistoricalSearch.LoopInvariant
