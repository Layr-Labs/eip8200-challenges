import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.FusedMemory

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
A proved integration interface for a replacement eight-word retained square loop.
The execution and repeated-square contracts remain explicit inputs. This file
does not prove those contracts for the experimental bytecode.
-/
namespace Challenge.Modexp.Submission.Proofs.Fast.CRTLoopInterface

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

abbrev R : Nat := Limbs.radix ^ 8

theorem square_congr (modulus a b : Nat) (h : a % modulus = b % modulus) :
    Model.montMul modulus R a a = Model.montMul modulus R b b := by
  have hc : (a : ZMod modulus) = (b : ZMod modulus) :=
    (ZMod.natCast_eq_natCast_iff a b modulus).2 h
  unfold Model.montMul
  rw [hc]

theorem iterate_congr (modulus count a b : Nat) (h : a % modulus = b % modulus) :
    ((fun x => Model.montMul modulus R x x)^[count] a) % modulus =
      ((fun x => Model.montMul modulus R x x)^[count] b) % modulus := by
  induction count with
  | zero => exact h
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        square_congr modulus _ _ ih]

/-- The representation may be the nine retained 244-bit digits, ordinary EVM
words, or a disjunction covering both the direct and overflow-reentry states.
The theorem requires only one normalized square per transition; it does not
require a particular scratch layout or an input smaller than the modulus. -/
theorem iterate_value {α : Type} (states : Nat → α) (rep : α → Nat → Prop)
    (modulus a count : Nat) (hzero : rep (states 0) a)
    (hstep : ∀ i, i < count → ∀ v, rep (states i) v →
      ∃ w, rep (states (i+1)) w ∧
        w % modulus = Model.montMul modulus R v v % modulus) :
    ∃ v, rep (states count) v ∧
      v % modulus = ((fun x => Model.montMul modulus R x x)^[count] a) % modulus := by
  induction count with
  | zero => exact ⟨a, hzero, rfl⟩
  | succ count ih =>
      obtain ⟨v, hv, heq⟩ := ih (fun i hi => hstep i (by omega))
      obtain ⟨w, hw, hweq⟩ := hstep count (by omega) v hv
      refine ⟨w, hw, ?_⟩
      rw [hweq, square_congr modulus v _ heq, Function.iterate_succ_apply']

/-- One retained batch plus its ordinary overflow/copy continuation. A batch
may consume several squares; its counter strictly decreases. The last batch
lands at the existing final-product entry instead of another square entry. -/
structure Chunk (head : Nat → ByteArray → State) (done : ByteArray → State)
    (rep : ByteArray → Nat → Prop) (keep : ByteArray → ByteArray → Prop)
    (modulus count : Nat) (mem : ByteArray) (a : Nat) where
  remaining : Nat
  remaining_lt : remaining < count
  memory : ByteArray
  value : Nat
  represented : rep memory value
  preserved : keep memory mem
  residue : value % modulus =
    ((fun x => Model.montMul modulus R x x)^[count - remaining] a) % modulus
  trace : Challenge.EvmProof.GasSteps (head count mem)
    (if remaining = 0 then done memory else head remaining memory)

structure Completed (head : Nat → ByteArray → State) (done : ByteArray → State)
    (rep : ByteArray → Nat → Prop) (keep : ByteArray → ByteArray → Prop)
    (modulus count : Nat) (mem : ByteArray) (a : Nat) where
  memory : ByteArray
  value : Nat
  represented : rep memory value
  preserved : keep memory mem
  residue : value % modulus =
    ((fun x => Model.montMul modulus R x x)^[count] a) % modulus
  trace : Challenge.EvmProof.GasSteps (head count mem) (done memory)

/-- Strong induction composes exact variable-length batches. The preserved
relation can be byte observation rather than full memory equality. Every step
premise is an actual GasSteps trace, so the result makes no assumption that
tested execution or arithmetic congruence alone establishes EVM behavior. -/
noncomputable def runChunks
    (head : Nat → ByteArray → State) (done : ByteArray → State)
    (rep : ByteArray → Nat → Prop) (keep : ByteArray → ByteArray → Prop)
    (keep_trans : ∀ {a b c}, keep a b → keep b c → keep a c)
    (modulus maxCount : Nat)
    (step : ∀ count mem a, 0 < count → count ≤ maxCount → rep mem a →
      Chunk head done rep keep modulus count mem a)
    (count : Nat) (mem : ByteArray) (a : Nat) (hcount : 0 < count)
    (hbounded : count ≤ maxCount) (ha : rep mem a) :
    Completed head done rep keep modulus count mem a := by
  let chunk := step count mem a hcount hbounded ha
  by_cases hz : chunk.remaining = 0
  · refine ⟨chunk.memory, chunk.value, chunk.represented, chunk.preserved, ?_, ?_⟩
    · simpa only [hz, Nat.sub_zero] using chunk.residue
    · simpa only [if_pos hz] using chunk.trace
  · let tail := runChunks head done rep keep keep_trans modulus maxCount step
      chunk.remaining chunk.memory chunk.value (by omega)
      (Nat.le_trans (Nat.le_of_lt chunk.remaining_lt) hbounded) chunk.represented
    refine ⟨tail.memory, tail.value, tail.represented,
      keep_trans tail.preserved chunk.preserved, ?_, ?_⟩
    · have hc := iterate_congr modulus chunk.remaining chunk.value
        ((fun x => Model.montMul modulus R x x)^[count - chunk.remaining] a) chunk.residue
      have hadd : chunk.remaining + (count - chunk.remaining) = count := by
        have := chunk.remaining_lt
        omega
      rw [← Function.iterate_add_apply, hadd] at hc
      exact tail.residue.trans hc
    · have first : Challenge.EvmProof.GasSteps (head count mem)
          (head chunk.remaining chunk.memory) := by
        simpa only [if_neg hz] using chunk.trace
      exact first.trans tail.trace
termination_by count
decreasing_by exact chunk.remaining_lt

/-- Observable requirements after the complete square chain, before its final
mixed-domain product. The scratch contents and byte-array length are unrestricted. -/
structure SquareMemory where
  memory : Nat → ByteArray → ByteArray
  low : ∀ (k : Nat) (mem : ByteArray) (addr : Nat), addr + 32 ≤ 512 →
    MachineState.readWord (memory k mem) addr = MachineState.readWord mem addr
  inverse : ∀ (k : Nat) (mem : ByteArray),
    MachineState.readWord (memory k mem) 2720 = MachineState.readWord mem 2720
  value : ∀ (k : Nat) (mem : ByteArray) (a modulus : Nat), 1 ≤ k →
    Model.FastRepresents mem 2112 8 a → Model.FastRepresents mem 0 8 modulus →
    modulus % 2 = 1 → a < modulus →
    ((MachineState.readWord mem 224).toNat * (MachineState.readWord mem 2720).toNat + 1)
      % 2^256 = 0 →
    ∃ v, Model.FastRepresents (memory k mem) 2368 8 v ∧
      v % modulus = ((fun x => Model.montMul modulus R x x)^[k] a) % modulus

def finished (model : SquareMemory) (s : State) (k : Nat) (mem : ByteArray) : ByteArray :=
  StagedProduct.memory s (model.memory k mem) 8

theorem keep_low (model : SquareMemory) (k : Nat) (mem : ByteArray) (ptr value : Nat)
    (hptr : ptr + 256 ≤ 512) (hvalue : Model.FastRepresents mem ptr 8 value) :
    Model.FastRepresents (model.memory k mem) ptr 8 value := by
  apply (Model.fastRepresents_congr (a := mem) (b := model.memory k mem) ?_ value).1 hvalue
  intro j hj
  exact (model.low k mem (ptr + 32*j) (by omega)).symm

/-- The existing final product accepts any new square-chain representation that
exports the staged value and these few preserved words. -/
theorem finished_value (model : SquareMemory) (s : State) (k : Nat)
    (mem : ByteArray) (a b modulus : Nat) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 2112 8 a)
    (hb : Model.FastRepresents mem 256 8 b)
    (hm : Model.FastRepresents mem 0 8 modulus)
    (hodd : modulus % 2 = 1) (ham : a < modulus) (hbm : b < modulus)
    (hminv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (finished model s k mem) 256 8
      (Model.montMul modulus R ((fun x => Model.montMul modulus R x x)^[k] a) b) := by
  obtain ⟨v, hv, heq⟩ := model.value k mem a modulus hk ha hm hodd ham hminv
  have hb' := keep_low model k mem 256 b (by decide) hb
  have hm' := keep_low model k mem 0 modulus (by decide) hm
  have hi' : ((MachineState.readWord (model.memory k mem) 224).toNat *
      (MachineState.readWord (model.memory k mem) 2720).toNat + 1) % 2^256 = 0 := by
    rw [model.low k mem 224 (by decide), model.inverse k mem]
    exact hminv
  have h := LazyMixedProduct.represents s (model.memory k mem) 6 v b modulus
    (by decide) hv hb' hm' hodd hbm hi'
  rw [FusedMemory.mont_mul_congr_left modulus R v _ b heq] at h
  exact h

/-- Full-call obligations for replacing only the accelerated eight-word loop.
An inhabitant still requires an actual bytecode execution theorem. -/
structure Implementation (s : State) (bsize modulus minv : Nat) where
  memory : Nat → ByteArray → ByteArray
  run : ∀ (k : Nat) (ret : UInt256) (tail : List UInt256) (mem : ByteArray) (a : Nat),
    minv ≠ 1 → 1 ≤ k → k ≤ 16 → tail.length ≤ 982 →
    tail[1]? = some (UInt256.ofNat 256) → tail[2]? = some (UInt256.ofNat 8) →
    Exp.Frame mem 8 bsize minv → Model.FastRepresents mem 0 8 modulus →
    Model.FastRepresents mem 2112 8 a → a < modulus →
    Challenge.EvmProof.GasSteps (Exp.sqLoopCall s mem k ret tail)
      (Exp.retTo s (memory k mem) (UInt256.ofNat 690) tail)
  value : ∀ (k : Nat) (mem : ByteArray) (a b : Nat), 1 ≤ k →
    Exp.Frame mem 8 bsize minv → Model.FastRepresents mem 0 8 modulus →
    Model.FastRepresents mem 2112 8 a → Model.FastRepresents mem 256 8 b →
    a < modulus → b < modulus →
    Model.FastRepresents (memory k mem) 256 8
      (Model.montMul modulus R ((fun x => Model.montMul modulus R x x)^[k] a) b)

/-- Assemble the full public loop contract from the new memory invariant and
an exact execution theorem. The existing scalar inverse supplies the unchanged
final product's inverse premise. -/
def ofModel (model : SquareMemory) (s : State) (bsize modulus minv : Nat)
    (hodd : modulus % 2 = 1) (hminvlt : minv < 2^256)
    (hminvA : (modulus % Limbs.radix * minv + 1) % 2^256 = 0)
    (trace : ∀ (k : Nat) (ret : UInt256) (tail : List UInt256)
      (mem : ByteArray) (a : Nat), minv ≠ 1 → 1 ≤ k → k ≤ 16 → tail.length ≤ 982 →
      tail[1]? = some (UInt256.ofNat 256) → tail[2]? = some (UInt256.ofNat 8) →
      Exp.Frame mem 8 bsize minv → Model.FastRepresents mem 0 8 modulus →
      Model.FastRepresents mem 2112 8 a → a < modulus →
      Challenge.EvmProof.GasSteps (Exp.sqLoopCall s mem k ret tail)
        (Exp.retTo s (finished model s k mem) (UInt256.ofNat 690) tail)) :
    Implementation s bsize modulus minv where
  memory := finished model s
  run := trace
  value k mem a b hk hf hm ha hb ham hbm := by
    have hlow : (MachineState.readWord mem 224).toNat = modulus % Limbs.radix := by
      have h := Model.readWord_of_fastRepresents hm (j := 7) (by decide)
      norm_num at h
      exact h
    have hi : (MachineState.readWord mem 2720).toNat = minv := by
      rw [hf.minvW, Exp.toNat_ofNat_self hminvlt]
    exact finished_value model s k mem a b modulus hk ha hb hm hodd ham hbm
      (by rw [hlow, hi]; exact hminvA)

/-- All generic multiplication, addition, and nonaccelerated square contracts
are definitionally retained. No existing scratch-memory equality is required. -/
def install (s : State) (bsize modulus minv : Nat)
    (old : Exp.Subroutines s 8 bsize modulus minv)
    (replacement : Implementation s bsize modulus minv) :
    Exp.Subroutines s 8 bsize modulus minv :=
  { old with
    sqLoopMem := replacement.memory
    squareLoop := fun k ret tail mem a hfast hk hk16 hcap hw hn hf hm ha ham =>
      replacement.run k ret tail mem a hfast.2 hk hk16 hcap hw hn hf hm ha ham
    sqLoopValue := fun k mem a b _ hk hf hm ha hb ham hbm =>
      replacement.value k mem a b hk hf hm ha hb ham hbm }

theorem install_spec (s : State) (bsize modulus minv : Nat)
    (old : Exp.Subroutines s 8 bsize modulus minv)
    (replacement : Implementation s bsize modulus minv)
    (h : Exp.SubSpec old.mpMem old.amMem 8 modulus R minv) :
    Exp.SubSpec (install s bsize modulus minv old replacement).mpMem
      (install s bsize modulus minv old replacement).amMem 8 modulus R minv := h

#print axioms finished_value
#print axioms iterate_value
#print axioms runChunks
#print axioms ofModel
#print axioms install_spec

end Challenge.Modexp.Submission.Proofs.Fast.CRTLoopInterface
