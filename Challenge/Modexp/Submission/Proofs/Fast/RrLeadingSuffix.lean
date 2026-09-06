import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingExpBridge

set_option warningAsError true
set_option maxHeartbeats 16000000

/-!
# General RR suffix after the direct leading-one handover

This private module reuses the inherited one-round and final-round execution
certificates.  It generalizes only the iteration index: the initial counter is
an arbitrary `start ≤ 5`, and the initial RR value is arbitrary below the
modulus.  The direct-counter specialization is therefore a thin corollary.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingSuffix

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Exp
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingMemory
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingExpBridge

/-- Memory after `i` RR rounds beginning at counter `start`. -/
def rrSuffixMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (n start : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rrStep mpMem n (start - i) (rrSuffixMem mpMem n start mem i)

def rrSuffixFamily (s : State)
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (n bsize esize msize start i : Nat) : State :=
  rrHead s (rrSuffixMem mpMem n start mem i)
    n bsize esize msize (start - i)

theorem rrSuffixValue_lt {mm R n start initial : Nat}
    (hm : 0 < mm) (hinitial : initial < mm) : ∀ i,
    rrSuffixValue mm R n start initial i < mm := by
  intro i
  cases i with
  | zero => exact hinitial
  | succ i =>
      rw [rrSuffixValue_succ]
      exact Model.montMul_lt hm _ _ _

theorem readWord_rrSuffixMem
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 6144 mem') 9376 =
        MachineState.readWord mem' 9376)
    (n start : Nat) (mem : ByteArray) : ∀ i,
    MachineState.readWord (rrSuffixMem mpMem n start mem i) 9376 =
      MachineState.readWord mem 9376 := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord
        (rrStep mpMem n (start - i) (rrSuffixMem mpMem n start mem i)) 9376 = _
      unfold rrStep
      split
      · rw [hkeep 6144 6144 _, ih]
      · rw [hkeep 6144 5120 _, hkeep 6144 6144 _, ih]

theorem rrSuffixMem_frame {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (start : Nat)
    (mem : ByteArray) (hframe : Frame mem n bsize minv) : ∀ i,
    Frame (rrSuffixMem sub.mpMem n start mem i) n bsize minv := by
  intro i
  induction i with
  | zero => exact hframe
  | succ i ih =>
      show Frame
        (rrStep sub.mpMem n (start - i) (rrSuffixMem sub.mpMem n start mem i))
        n bsize minv
      unfold rrStep
      split
      · exact sub.mpFrame 6144 6144 6144 _ (by omega) ih
      · exact sub.mpFrame 6144 5120 6144 _ (by omega)
          (sub.mpFrame 6144 6144 6144 _ (by omega) ih)

theorem rrSuffixMem_preserves {s : State} {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv) (start ptr value : Nat)
    (mem : ByteArray) (hbefore : ptr + 32 * n ≤ 6144)
    (hrep : Model.FastRepresents mem ptr n value) : ∀ i,
    Model.FastRepresents (rrSuffixMem sub.mpMem n start mem i) ptr n value := by
  intro i
  induction i with
  | zero => exact hrep
  | succ i ih =>
      show Model.FastRepresents
        (rrStep sub.mpMem n (start - i) (rrSuffixMem sub.mpMem n start mem i))
        ptr n value
      unfold rrStep
      split
      · exact spec.mpFrame 6144 6144 6144 ptr value _ (by omega)
          (Or.inr hbefore) ih
      · exact spec.mpFrame 6144 5120 6144 ptr value _ (by omega)
          (Or.inr hbefore)
          (spec.mpFrame 6144 6144 6144 ptr value _ (by omega)
            (Or.inr hbefore) ih)

/-- Generalized memory invariant for an arbitrary starting counter/value. -/
theorem rrSuffixMem_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv start initial : Nat}
    (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hn32 : n ≤ 32) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R initial) (hinitial : initial < mm) : ∀ i,
    RrInv (rrSuffixMem mpMem n start mem i) n mm R
      (rrSuffixValue mm R n start initial i) := by
  intro i
  induction i with
  | zero => exact hinv
  | succ i ih =>
      have hv := rrSuffixValue_lt (R := R) (n := n) (start := start) hm hinitial i
      have hmi : MachineState.readWord (rrSuffixMem mpMem n start mem i) 9376 =
          UInt256.ofNat minv :=
        (readWord_rrSuffixMem mpMem
          (fun pa pb m => spec.mpMinv pa pb 6144 m (by omega)) n start mem i).trans hminv
      have hmi1 : MachineState.readWord
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i)) 9376 =
            UInt256.ofNat minv :=
        (spec.mpMinv 6144 6144 6144 _ (by omega)).trans hmi
      have hsq : Model.FastRepresents
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i)) 6144 n
          (Model.montMul mm R
            (rrSuffixValue mm R n start initial i)
            (rrSuffixValue mm R n start initial i)) :=
        spec.mpValue 6144 6144 6144 _ _ _ (by omega) (by omega) (by omega)
          ih.modulus hmi ih.rr ih.rr hv hv
      have hmod1 : Model.FastRepresents
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i)) 0 n mm :=
        spec.mpFrame 6144 6144 6144 0 mm _ (by omega) (Or.inr (by omega)) ih.modulus
      have hr11 : Model.FastRepresents
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i)) 4096 n (R % mm) :=
        spec.mpFrame 6144 6144 6144 4096 _ _ (by omega) (Or.inr (by omega)) ih.r1
      have hcc1 : Model.FastRepresents
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i)) 5120 n
            (Limbs.radix * R % mm) :=
        spec.mpFrame 6144 6144 6144 5120 _ _ (by omega) (Or.inr (by omega)) ih.cc
      have hsel : Model.FastRepresents
          (mpMem 6144 6144 6144 (rrSuffixMem mpMem n start mem i))
          (selOf n (start - i)) n
          (if Exp.bitAt n (start - i) = 0 then R % mm
            else Limbs.radix * R % mm) := by
        by_cases h0 : Exp.bitAt n (start - i) = 0
        · rw [if_pos h0, selOf, h0]
          simpa using hr11
        · have h1 : Exp.bitAt n (start - i) = 1 := by
            have := Exp.bitAt_le_one n (start - i)
            omega
          rw [if_neg h0, selOf, h1]
          simpa using hcc1
      have hsellt :
          (if Exp.bitAt n (start - i) = 0 then R % mm
            else Limbs.radix * R % mm) < mm := by
        by_cases h0 : Exp.bitAt n (start - i) = 0
        · rw [if_pos h0]; exact Nat.mod_lt _ hm
        · rw [if_neg h0]; exact Nat.mod_lt _ hm
      show RrInv
        (rrStep mpMem n (start - i) (rrSuffixMem mpMem n start mem i)) n mm R
        (rrSuffixValue mm R n start initial (i + 1))
      rw [rrSuffixValue_succ, logic_bitAt_eq]
      by_cases h0 : Exp.bitAt n (start - i) = 0
      · rw [rrStep, if_pos h0, if_pos h0,
          montMul_by_one hm hcop (Model.montMul_lt hm _ _ _)]
        exact ⟨hmod1, hr11, hcc1, hsq⟩
      · have h1 : selOf n (start - i) = 5120 := by
          have := Exp.bitAt_le_one n (start - i)
          unfold selOf
          omega
        rw [h1, if_neg h0] at hsel
        rw [if_neg h0] at hsellt
        rw [rrStep, if_neg h0, if_neg h0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact spec.mpFrame 6144 5120 6144 0 mm _ (by omega)
            (Or.inr (by omega)) hmod1
        · exact spec.mpFrame 6144 5120 6144 4096 _ _ (by omega)
            (Or.inr (by omega)) hr11
        · exact spec.mpFrame 6144 5120 6144 5120 _ _ (by omega)
            (Or.inr (by omega)) hcc1
        · exact spec.mpValue 6144 5120 6144 _ _ _ (by omega)
            (by omega) (by omega) hmod1 hmi1 hsq hsel
            (Model.montMul_lt hm _ _ _) hsellt

/-- The non-final rounds from counter `start` down to counter zero. -/
def gasSteps_rrSuffixLoop (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize start initial : Nat)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn32 : n ≤ 32)
    (hstart : start ≤ 5) (hinitial : initial < mm)
    (hframe : Frame mem n bsize minv) (hinv : RrInv mem n mm R initial)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize start)
      (rrHead s (rrSuffixMem sub.mpMem n start mem start)
        n bsize esize msize 0) :=
  by
    simpa [rrSuffixFamily, rrSuffixMem] using
      (Challenge.EvmProof.GasSteps.iterateBounded
        (I := rrSuffixFamily s sub.mpMem mem n bsize esize msize start) start
        (fun i hi => gasSteps_rrBody s sub spec
          (rrSuffixMem sub.mpMem n start mem i) esize msize
          (start - i) (start - (i + 1))
          (rrSuffixValue mm R n start initial i) hm hn32 (by omega) (by omega)
          (by omega)
          (rrSuffixValue_lt (R := R) (n := n) (start := start) hm hinitial i)
          (rrSuffixMem_frame sub start mem hframe i)
          (rrSuffixMem_inv spec hm hcop hn32 mem hframe.minvW hinv hinitial i)
          hcode hfork hrun hnp))

/-- All rounds including counter zero. -/
def gasSteps_rrSuffixChain (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize start initial : Nat)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hn32 : n ≤ 32)
    (hstart : start ≤ 5) (hinitial : initial < mm)
    (hframe : Frame mem n bsize minv) (hinv : RrInv mem n mm R initial)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rrHead s mem n bsize esize msize start)
      (rrDone s (rrSuffixMem sub.mpMem n start mem (start + 1))
        n bsize esize msize) :=
  by
    simpa [rrSuffixMem] using
      ((gasSteps_rrSuffixLoop s sub spec mem esize msize start initial hm hcop hn32
          hstart hinitial hframe hinv hcode hfork hrun hnp).trans
        (gasSteps_rrLastBody s sub spec
          (rrSuffixMem sub.mpMem n start mem start) esize msize
          (rrSuffixValue mm R n start initial start) hm hn32
          (rrSuffixValue_lt (R := R) (n := n) (start := start) hm hinitial start)
          (rrSuffixMem_frame sub start mem hframe start)
          (rrSuffixMem_inv spec hm hcop hn32 mem hframe.minvW hinv hinitial start)
          hcode hfork hrun hnp))

/-- Direct-counter specialization of the generalized execution chain. -/
def gasSteps_directSuffix (s : State) {n bsize mm minv R : Nat}
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (esize msize : Nat)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm R (Limbs.radix * R % mm))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rrHead s mem n bsize esize msize (directCounter n))
      (rrDone s
        (rrSuffixMem sub.mpMem n (directCounter n) mem (directCounter n + 1))
        n bsize esize msize) :=
  gasSteps_rrSuffixChain s sub spec mem esize msize (directCounter n)
    (Limbs.radix * R % mm) hm hcop hn32
    (Nat.le_trans (directCounter_le_four hn2 hn32) (by omega))
    (Nat.mod_lt _ hm) hframe hinv hcode hfork hrun hnp

/-- The exact final invariant and modular value produced by the direct RR
suffix. -/
theorem directSuffix_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat}
    (spec : SubSpec mpMem amMem n mm R minv)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (mem : ByteArray)
    (hminv : MachineState.readWord mem 9376 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R (Limbs.radix * R % mm)) :
    RrInv
        (rrSuffixMem mpMem n (directCounter n) mem (directCounter n + 1))
        n mm R
        (rrSuffixValue mm R n (directCounter n) (Limbs.radix * R % mm)
          (directCounter n + 1)) ∧
      rrSuffixValue mm R n (directCounter n) (Limbs.radix * R % mm)
          (directCounter n + 1) ≡ Limbs.radix ^ n * R [MOD mm] := by
  exact ⟨rrSuffixMem_inv spec hm hcop hn32 mem hminv hinv
      (Nat.mod_lt _ hm) (directCounter n + 1),
    rrSuffixValue_direct_final hm hcop hn2 hn32⟩

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingSuffix

