import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.ProductAccumulate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.CRTWordBridge
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def lowProgram : List Instr := [.op .MUL, .op .ADD]
def residueProgram : List Instr := [.op .MULMOD, .op .ADD]

theorem runLow (s : State) (pc a b lo : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1020) :
    runInstructions lowProgram {s with pc := pc, stack := a :: b :: lo :: rest} =
      some {s with pc := advancePC 2 pc, stack := (a*b+lo) :: rest} := by
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  simp [lowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, advancePC, h2, h3]

theorem runResidue (s : State) (pc a b P H : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019) :
    runInstructions residueProgram {s with pc := pc, stack := a :: b :: P :: H :: rest} =
      some {s with pc := advancePC 2 pc, stack := (UInt256.mulMod a b P+H) :: rest} := by
  have h2 : rest.length+2 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  simp [residueProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, advancePC, h2, h4]

theorem mul_toNat (a b : UInt256) : (a*b).toNat = (a.toNat*b.toNat) % 2^256 := by
  change (a.val*b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem mulMod_toNat (a b P : UInt256) (hP : 0 < P.toNat) :
    (UInt256.mulMod a b P).toNat = (a.toNat*b.toNat) % P.toNat := by
  have hPn : P.val.val ≠ 0 := by change P.toNat ≠ 0; omega
  unfold UInt256.mulMod
  rw [if_neg hPn, word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ hP).trans P.val.isLt

/-- Adding one product updates the wrapped low accumulator exactly. -/
theorem lowAccumulate (a b lo : UInt256) (S : Nat) (hlo : lo.toNat = S % wordRadix) :
    (a*b+lo).toNat = (S+a.toNat*b.toNat) % wordRadix := by
  rw [word_toNat_add, mul_toNat, hlo]
  change ((a.toNat*b.toNat) % wordRadix + S % wordRadix) % wordRadix = _
  rw [← Nat.add_mod, Nat.add_comm]

/-- A residue-product append stays unwrapped whenever one more full residue
fits; operands are arbitrary words, including zero and their maximal values. -/
theorem residueAccumulate (a b P H : UInt256) (hP : 0 < P.toNat)
    (hroom : H.toNat+P.toNat ≤ wordRadix) :
    (UInt256.mulMod a b P+H).toNat = H.toNat+(a.toNat*b.toNat) % P.toNat := by
  rw [word_toNat_add, mulMod_toNat a b P hP, Nat.add_comm]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (a.toNat*b.toNat) hP
  change H.toNat+(a.toNat*b.toNat) % P.toNat < wordRadix
  omega

/-- Appending one residue preserves both its accumulated range and congruence.
Repeated use gives the hypotheses of the CRT reconstruction macro. -/
theorem appendInvariant (P k H S x y : Nat) (hP : 0 < P)
    (hbound : H ≤ k*(P-1)) (hres : H % P = S % P) :
    H+(x*y)%P ≤ (k+1)*(P-1) ∧
    (H+(x*y)%P) % P = (S+x*y) % P := by
  have hr := Nat.mod_lt (x*y) hP
  have hr' : (x*y) % P ≤ P-1 := by omega
  constructor
  · nlinarith
  · rw [Nat.add_mod, Nat.mod_mod, hres, ← Nat.add_mod]

theorem doubleInvariant (P k H S : Nat)
    (hbound : H ≤ k*(P-1)) (hres : H % P = S % P) :
    2*H ≤ (2*k)*(P-1) ∧ (2*H) % P = (2*S) % P := by
  constructor
  · nlinarith
  · rw [Nat.mul_mod, hres, ← Nat.mul_mod]

/-- Combined word invariant for the separate MUL/ADD and MULMOD/ADD passes. -/
theorem accumulateInvariant (a b P H lo : UInt256) (k S : Nat)
    (hP : 0 < P.toNat) (hroom : H.toNat+P.toNat ≤ wordRadix)
    (hbound : H.toNat ≤ k*(P.toNat-1))
    (hres : H.toNat % P.toNat = S % P.toNat) (hlo : lo.toNat = S % wordRadix) :
    let H' := UInt256.mulMod a b P+H
    let lo' := a*b+lo
    H'.toNat ≤ (k+1)*(P.toNat-1) ∧
    H'.toNat % P.toNat = (S+a.toNat*b.toNat) % P.toNat ∧
    lo'.toNat = (S+a.toNat*b.toNat) % wordRadix := by
  dsimp
  rw [residueAccumulate a b P H hP hroom]
  have hi := appendInvariant P.toNat k H.toNat S a.toNat b.toNat hP hbound hres
  exact ⟨hi.1, hi.2, lowAccumulate a b lo S hlo⟩

/-- The first product can seed both accumulators without adding zero. -/
theorem seededInvariant (a b P : UInt256) (hP : 0 < P.toNat) :
    (UInt256.mulMod a b P).toNat ≤ P.toNat-1 ∧
    (UInt256.mulMod a b P).toNat % P.toNat = (a.toNat*b.toNat) % P.toNat ∧
    (a*b).toNat = (a.toNat*b.toNat) % wordRadix := by
  rw [mulMod_toNat a b P hP, Nat.mod_mod]
  have hr := Nat.mod_lt (a.toNat*b.toNat) hP
  exact ⟨by omega, rfl, mul_toNat a b⟩

/-- Doubling the off-diagonal square sum preserves both representations and
doubles its residue-term budget when the high accumulator cannot overflow. -/
theorem doubleWordInvariant (P H lo : UInt256) (k S : Nat)
    (hroom : 2*H.toNat < wordRadix) (hbound : H.toNat ≤ k*(P.toNat-1))
    (hres : H.toNat % P.toNat = S % P.toNat) (hlo : lo.toNat = S % wordRadix) :
    (H+H).toNat ≤ (2*k)*(P.toNat-1) ∧
    (H+H).toNat % P.toNat = (2*S) % P.toNat ∧
    (lo+lo).toNat = (2*S) % wordRadix := by
  have hH : (H+H).toNat = 2*H.toNat := by
    rw [word_toNat_add, ← Nat.two_mul]
    exact Nat.mod_eq_of_lt hroom
  rw [hH]
  have hi := doubleInvariant P.toNat k H.toNat S hbound hres
  refine ⟨hi.1, hi.2, ?_⟩
  rw [word_toNat_add, hlo]
  change (S % wordRadix+S % wordRadix) % wordRadix = _
  rw [← Nat.add_mod, ← Nat.two_mul]

/-- A residue-term budget below twenty guarantees room for the next append
with P=2^251-1; this is the actual column kernel's maximum budget. -/
theorem fixedModulusRoom (k H : Nat) (hk : k ≤ 19)
    (hH : H ≤ k*(residueModulus-1)) : H+residueModulus ≤ wordRadix := by
  have hh := hH.trans (Nat.mul_le_mul_right (residueModulus-1) hk)
  norm_num [residueModulus, wordRadix] at *
  omega

#print axioms runLow
#print axioms runResidue
#print axioms lowAccumulate
#print axioms residueAccumulate
#print axioms appendInvariant
#print axioms doubleInvariant
#print axioms accumulateInvariant
#print axioms seededInvariant
#print axioms doubleWordInvariant
#print axioms fixedModulusRoom

end HistoricalSearch.ProductAccumulate
