import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Compression
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWord
open EvmSemantics PairedLaneUInt256Bridge Paired144Core
open Paired80WordRound (WordLane bitLane liftLane bitLane_liftLane bitLane_injective)
open Paired144WordRound (packCrypto lowerWord wordShift)
open Paired80Compression (low32 unpackLeft)
open StaggerScalarWide (bits_wordShift)
open Paired80CryptoBridge (CryptoLane)

def rawF (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => (UInt256.xor (UInt256.xor b c) d)
  | 1 => (UInt256.xor d (UInt256.land b (UInt256.xor c d)))
  | 2 => (UInt256.xor (UInt256.lor b (UInt256.lnot c)) d)
  | 3 => (UInt256.xor c (UInt256.land d (UInt256.xor b c)))
  | _ => (UInt256.xor b (UInt256.lor c (UInt256.lnot d)))

theorem bits_rawF (j : Nat) (b c d : UInt256) :
    bits (rawF j b c d) = StaggerScalar.rawF j (bits b) (bits c) (bits d) := by
  rcases Nat.lt_or_ge j 4 with hj | hj
  · interval_cases j <;> simp only [rawF, StaggerScalar.rawF, bits_xor, bits_lor, bits_land, bits_lnot]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_comm 4 n, rawF, StaggerScalar.rawF, bits_xor, bits_lor, bits_land, bits_lnot]

def mask (x : UInt256) : UInt256 := UInt256.land x lowerWord

def sum (j : Nat) (a b c d message k : UInt256) : UInt256 :=
  mask (UInt256.add (UInt256.add (UInt256.add a (rawF j b c d)) message) k)

def t (maskB : Bool) (j r : Nat) (message k : UInt256) (q : WordLane) : UInt256 :=
  let raw := UInt256.add (wordShift (sum j q.a q.b q.c q.d message k) (38 - r)) q.e
  if maskB then mask raw else raw

def step (maskB maskD : Bool) (j r : Nat) (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, t maskB j r message k q, q.b,
    if maskD then mask (wordShift q.c 28) else wordShift q.c 28, q.d⟩

theorem bits_mask (x : UInt256) : bits (mask x) = StaggerScalar.mask (bits x) := by
  simp only [mask, StaggerScalar.mask, bits_land, Paired144WordRound.lowerWord, bits_word]

theorem bits_sum (j : Nat) (a b c d message k : UInt256) :
    bits (sum j a b c d message k) =
      StaggerScalar.sum j (bits a) (bits b) (bits c) (bits d) (bits message) (bits k) := by
  simp only [sum, StaggerScalar.sum, bits_mask, bits_add, bits_rawF]

theorem bits_t (maskB : Bool) (j r : Nat) (message k : UInt256) (q : WordLane) :
    bits (t maskB j r message k q) =
      StaggerScalar.t maskB j r (bits message) (bits k) (bitLane q) := by
  cases maskB <;>
    simp only [t, StaggerScalar.t, Bool.false_eq_true, ite_true, ite_false,
      bits_mask, bits_add, bits_wordShift _ (38-r) (Nat.lt_of_le_of_lt (Nat.sub_le 38 r) (by decide)), bits_sum, bitLane]


def embed (q : CryptoLane) : WordLane := packCrypto q ⟨0,0,0,0,0⟩
def Clean (q : WordLane) : Prop := StaggerScalar.Clean (bitLane q)

theorem bits_unpackLeft (q : WordLane) :
    Paired80CryptoBridge.bits (unpackLeft q) = StaggerScalar.project (bitLane q) := by
  rfl

theorem crypto_bits_inj {a b : CryptoLane} (h : Paired80CryptoBridge.bits a = Paired80CryptoBridge.bits b) :
    a = b := by
  cases a; cases b
  simp only [Paired80CryptoBridge.bits, PairedLaneCryptoBridge.bits,
    PairedLaneRoundSemantic.Lane.mk.injEq] at h
  rcases h with ⟨ha,hb,hc,hd,he⟩
  simp only [UInt32.toBitVec_inj] at ha hb hc hd he
  subst_vars
  rfl

theorem low_t_bits (maskB : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt256) (q : WordLane) :
    (low32 (t maskB j r message k q)).toBitVec =
      Paired80RoundSemantic.scalarT j r (low (bits q.a)) (low (bits q.b))
        (low (bits q.c)) (low (bits q.d)) (low (bits q.e)) (low (bits message)) (low (bits k)) := by
  change low (bits (t maskB j r message k q)) = _
  rw [bits_t]
  exact StaggerScalar.low_t maskB j r hr0 (Nat.lt_trans hr (by decide)) _ _ _
#print axioms low_t_bits

theorem low_c_rotate (c : UInt256) (hc : mask c = c) :
    low (bits (wordShift c 28)) = (low (bits c)).rotateLeft 10 := by
  have hqc : bits c = pack (low (bits c)) 0#32 := by
    have h := congrArg bits hc
    rw [bits_mask, StaggerScalar.mask_eq] at h
    exact h.symm
  rw [bits_wordShift _ 28 (by decide)]
  conv_lhs => rw [hqc]
  exact StaggerScalarWide.low_rotate (low (bits c)) 0#32 10 (by decide) (by decide)
#print axioms low_c_rotate

theorem low_optional_mask (flag : Bool) (x : UInt256) :
    low (bits (if flag then mask x else x)) = low (bits x) := by
  cases flag
  · rfl
  · exact (congrArg low (bits_mask x)).trans (StaggerScalar.low_mask _)
#print axioms low_optional_mask

theorem project_step (maskB maskD : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 17)
    (message k : UInt256) (q : WordLane) (hc : mask q.c = q.c) :
    unpackLeft (step maskB maskD j r message k q) =
      Paired80CryptoBridge.cryptoStep j r (low32 message) (low32 k) (unpackLeft q) := by
  have ht := low_t_bits maskB j r hr0 hr message k q
  have hd := (low_optional_mask maskD (wordShift q.c 28)).trans (low_c_rotate q.c hc)
  apply crypto_bits_inj
  rw [Paired80CryptoBridge.cryptoStep_bits j r hr0 hr]
  exact congrArg₂ (fun b d : BitVec 32 =>
    (⟨low (bits q.e), b, low (bits q.b), d, low (bits q.d)⟩ : Paired80RoundSemantic.Lane 32)) ht hd

theorem embed_clean (q : CryptoLane) : Clean (embed q) := by
  exact ⟨StaggerScalar.mask_pack _, StaggerScalar.mask_pack _, StaggerScalar.mask_pack _,
    StaggerScalar.mask_pack _, StaggerScalar.mask_pack _⟩

theorem step_clean (j r : Nat) (message k : UInt256) (q : WordLane) (hq : Clean q) :
    Clean (step true true j r message k q) := by
  rcases hq with ⟨ha,hb,hc,hd,he⟩
  simp only [Clean, bitLane, step, t, ite_true, bits_mask, StaggerScalar.Clean]
  exact ⟨he, StaggerScalar.mask_clean _, hb, StaggerScalar.mask_clean _, hd⟩

theorem step_b_clean (maskD : Bool) (j r : Nat) (message k : UInt256) (q : WordLane) :
    mask (step true maskD j r message k q).b = (step true maskD j r message k q).b := by
  apply bits_injective
  rw [bits_mask]
  change StaggerScalar.mask (bits (mask _)) = bits (mask _)
  rw [bits_mask]
  exact StaggerScalar.mask_clean _

theorem mask_eq (x : UInt256) : mask x = word (pack ((bits x).setWidth 32) 0#32) := by
  apply bits_injective
  rw [bits_mask, bits_word]
  exact StaggerScalar.mask_eq _

theorem clean_eq_embed (q : WordLane) (hq : Clean q) : q = embed (unpackLeft q) := by
  apply bitLane_injective
  rcases hq with ⟨ha,hb,hc,hd,he⟩
  rw [StaggerScalar.mask_eq] at ha hb hc hd he
  cases q
  simp only [bitLane] at ha hb hc hd he
  simp only [embed, unpackLeft, Paired144WordRound.packCrypto, bitLane, bits_word]
  congr 1 <;> first | exact ha.symm | exact hb.symm | exact hc.symm | exact hd.symm | exact he.symm

theorem low32_packWord (a b : UInt32) : low32 (word (pack a.toBitVec b.toBitVec)) = a := by
  apply UInt32.eq_of_toBitVec_eq
  change low (bits (word (pack a.toBitVec b.toBitVec))) = a.toBitVec
  rw [bits_word, low_pack]

theorem unpackLeft_packCrypto (l r : CryptoLane) : unpackLeft (packCrypto l r) = l := by
  cases l; cases r
  simp only [unpackLeft, Paired144WordRound.packCrypto, low32_packWord]

#print axioms unpackLeft_packCrypto

#print axioms project_step
#print axioms clean_eq_embed
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWord
