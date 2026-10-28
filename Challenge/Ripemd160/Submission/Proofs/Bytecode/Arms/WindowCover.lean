import Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 40000000

/-!
# Calldata window equalities pin long patterned prefixes

The 376- and 1000-byte arms do not compare every word with a literal.  The
first 256 bytes are checked against the eight shared chain literals; every
later window is checked equal to an *earlier* calldata window at a distance at
which the pattern itself repeats (and the 1000-byte arm adds one literal
window at offset 369).  By strong induction on the byte index this determines
every byte.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.WindowCover
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PatternedInputData PatternedWordData RecognitionAccumulator

abbrev bf (a : ByteArray) (i : Nat) : UInt8 := YulSemantics.EVM.byteFrom a.toList i

theorem bf_of_readWord (a b : ByteArray) (o o' t : Nat) (ht : t < 32)
    (h : MachineState.readWord a o = MachineState.readWord b o') :
    bf a (o + t) = bf b (o' + t) := by
  have hb := congrArg (UInt256.byteAt (UInt256.ofNat t)) h
  rw [Bytes.byteAt_readWord a o t ht, Bytes.byteAt_readWord b o' t ht] at hb
  apply UInt8.ext
  have hv := congrArg UInt256.toNat hb
  rw [Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (bf a (o + t)).toNat_lt (by norm_num)),
    Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (bf b (o' + t)).toNat_lt (by norm_num))] at hv
  exact hv

theorem bf_patterned (i : Nat) (hi : i < 1000) : bf patternedInput i = expectedByte i := by
  rw [bf, TailProjection.byteFrom_getElem patternedInput i (by rw [patternedInput_size]; exact hi),
    patternedInput_getElem]

/-- First window of `plan` containing byte `i`. -/
def findSrc (plan : List (Nat × Nat)) (i : Nat) : Option (Nat × Nat) :=
  plan.find? (fun p => decide (p.1 ≤ i ∧ i < p.1 + 32))

theorem findSrc_spec (plan : List (Nat × Nat)) (i : Nat) (p : Nat × Nat)
    (h : findSrc plan i = some p) : p ∈ plan ∧ p.1 ≤ i ∧ i < p.1 + 32 := by
  unfold findSrc at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

/-- The cover side conditions, checked by evaluation for each concrete plan. -/
structure Cover (n : Nat) (plan : List (Nat × Nat)) (anchors : List Nat) : Prop where
  bound : n ≤ 1000
  base : 256 ≤ n
  covered : ∀ i, i < n → 256 ≤ i →
    (findSrc plan i).isSome = true ∨ ∃ a ∈ anchors, a ≤ i ∧ i < a + 32
  earlier : ∀ i, i < n → ∀ p ∈ plan, p.1 ≤ i → i < p.1 + 32 →
    p.2 + (i - p.1) < i ∧ expectedByte (p.2 + (i - p.1)) = expectedByte i
  windows : ∀ p ∈ plan, p.1 + 32 ≤ n
  anchorBound : ∀ a ∈ anchors, a + 32 ≤ n

theorem bytes_of_checks (input : ByteArray) (n : Nat) (plan : List (Nat × Nat))
    (anchors : List Nat) (hc : Cover n plan anchors)
    (h0 : ∀ k, k < 8 → MachineState.readWord input (32 * k) =
      MachineState.readWord patternedInput (32 * k))
    (heq : ∀ p ∈ plan, MachineState.readWord input p.1 = MachineState.readWord input p.2)
    (hanc : ∀ a ∈ anchors, MachineState.readWord input a = MachineState.readWord patternedInput a) :
    ∀ i, i < n → bf input i = bf patternedInput i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  by_cases hlow : i < 256
  · have hb := bf_of_readWord input patternedInput (32 * (i / 32)) (32 * (i / 32)) (i % 32)
      (Nat.mod_lt _ (by omega)) (h0 (i / 32) (by omega))
    rwa [show 32 * (i / 32) + i % 32 = i by omega] at hb
  · rcases hc.covered i hi (by omega) with hs | ⟨a, ha, hlo, hhi⟩
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨hmem, hlo, hhi⟩ := findSrc_spec plan i p hp
      obtain ⟨hlt, hexp⟩ := hc.earlier i hi p hmem hlo hhi
      have hw := bf_of_readWord input input p.1 p.2 (i - p.1) (by omega) (heq p hmem)
      rw [show p.1 + (i - p.1) = i by omega] at hw
      have hn := hc.bound
      rw [hw, ih _ hlt (by omega), bf_patterned _ (by omega), bf_patterned _ (by omega), hexp]
    · have hb := bf_of_readWord input patternedInput a a (i - a) (by omega) (hanc a ha)
      rwa [show a + (i - a) = i by omega] at hb

theorem eq_reference (input : ByteArray) (n : Nat) (plan : List (Nat × Nat))
    (anchors : List Nat) (hc : Cover n plan anchors) (hsize : input.size = n)
    (h0 : ∀ k, k < 8 → MachineState.readWord input (32 * k) =
      MachineState.readWord patternedInput (32 * k))
    (heq : ∀ p ∈ plan, MachineState.readWord input p.1 = MachineState.readWord input p.2)
    (hanc : ∀ a ∈ anchors, MachineState.readWord input a = MachineState.readWord patternedInput a) :
    input = reference n := by
  have hb := bytes_of_checks input n plan anchors hc h0 heq hanc
  have hn := hc.bound
  apply ByteArray.ext_getElem
  · rw [hsize, reference_size n hn]
  · intro j hj hjr
    have hjn : j < n := by omega
    have h := hb j hjn
    rw [bf, TailProjection.byteFrom_getElem input j hj, bf_patterned j (by omega)] at h
    rw [h]
    simp only [reference, ByteArray.getElem_extract, Nat.zero_add]
    exact (patternedInput_getElem j (by rw [patternedInput_size]; omega)).symm

/-! ## Concrete plans -/

def plan376 : List (Nat × Nat) := [(256, 111), (288, 143), (320, 175), (344, 199)]

def plan1000 : List (Nat × Nat) :=
  [(256, 111), (288, 143), (320, 175), (352, 207), (401, 0), (433, 32), (465, 64), (502, 212),
   (546, 0), (578, 32), (610, 64), (642, 96), (674, 128), (706, 160), (753, 62), (785, 94),
   (817, 126), (849, 158), (881, 190), (947, 0), (910, 219), (968, 21), (721, 175), (364, 219),
   (509, 219), (470, 69), (514, 369), (915, 369)]

def anchors1000 : List Nat := [369]

theorem cover376 : Cover 376 plan376 [] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem cover1000 : Cover 1000 plan1000 anchors1000 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.WindowCover
