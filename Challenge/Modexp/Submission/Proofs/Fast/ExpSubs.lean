import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.CarryFull
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.SquareFull
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoop

-- Keep the caller proofs in their original word normal form.
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The concrete subroutine instance of the driver

`Fast.Exp` states the driver against the abstract record `Exp.Subroutines`
(`MONPRO`, `ADDMOD` and the in-place `SQUARE(0x800) → 0x800`).  This module
instantiates it: `MONPRO` from `Fast.CarryFull.gasSteps_monproFull`, `ADDMOD`
from the pair `Fast.Csub.gasSteps_addmod` / `gasSteps_csub` (packaged in `Exp`
as `gasSteps_addmodFull`), and `SQUARE` from `Fast.SquareFull.gasSteps_squareFull`
(the widths the kernel does not accelerate) together with
`Fast.SquareLoop.gasSteps_squareLoop` (the in-kernel square loop for `n ∈ {4, 8}`),
with the arithmetic of `Fast.SquareResult`.  Keeping the instance out of `Exp`
means that `Exp` and every abstract consumer (the fixed-exponent chain, the
shift / RR-leading / full-base continuations) compile without the kernel
developments; only the modules that pick the concrete `subs` import this one.

The declarations stay in namespace `Exp`, so `Exp.subs`, `Exp.specOf_subs`, … keep
their names.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

/-- `MONPRO` writes only below `5184`, so the configuration words survive. -/
theorem monproMem_frame' {s : State} {mem : ByteArray} {n bsize minv : Nat}
    (pa pb pd : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8) (hpd : pd + 32 * n ≤ 4096)
    (hf : Frame mem n bsize minv) :
    Frame (CarryResult.monproMem s mem pa pb n pd) n bsize minv :=
  have key := CarryResult.monproMem_frame s mem pa pb n pd hn (by omega) hpd
  ⟨by rw [key.1]; exact hf.s32, by rw [key.2.1]; exact hf.minvW,
   by rw [key.2.2.1]; exact hf.ml, by rw [key.2.2.2.1]; exact hf.tl,
   by rw [key.2.2.2.2]; exact hf.eoff⟩

/-- The `MONPRO` step of the concrete instance. -/
def subsMonpro (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    ∀ (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256)
      (mem : ByteArray) (a b : Nat), tail.length ≤ 998 →
      32 ≤ pa → pa + 32 * n ≤ 4096 → 32 ≤ pb → pb + 32 * n ≤ 4096 →
      pd + 32 * n ≤ 4096 →
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
      Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b → a < mm →
      Challenge.EvmProof.GasSteps (mpCall s mem pa pb pd ret tail)
        (retTo s (CarryResult.monproMem s mem pa pb n pd) ret tail) := by
  intro pa pb pd ret tail mem a b hcap hpa hpaFit hpb hpbFit hpdFit hjump hf hm ha hb ham
  -- `GasSteps` lives in `Type`, so the limb count has to be split by `cases`.
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n1 =>
    cases n1 with
    | zero => exact absurd hn (by omega)
    | succ p =>
      have hpdN : (UInt256.ofNat pd).toNat = pd :=
        toNat_ofNat_self (Nat.lt_of_le_of_lt (show pd ≤ 4096 by omega) (by norm_num))
      have hlow : (MachineState.readWord mem (32 * (p + 2) - 32)).toNat =
          mm % Limbs.radix := by
        have h := Model.readWord_of_fastRepresents hm (j := p + 1) (by omega)
        rw [show (0 : Nat) + 32 * (p + 1) = 32 * (p + 2) - 32 from by omega,
          show p + 1 + 1 - 1 - (p + 1) = 0 from by omega, pow_zero, Nat.div_one] at h
        exact h
      have hmi : (MachineState.readWord mem 5280).toNat = minv := by
        rw [hf.minvW, toNat_ofNat_self hminvlt]
      exact Challenge.EvmProof.GasSteps.cast
        (CarryFull.gasSteps_monproFull s mem pa pb p a b mm (UInt256.ofNat pd) ret tail
          (by omega) hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb hpbFit hcds
          hf.s32 hf.tl hf.ml hjump (by omega) ha hb hm ham hmpos
          (by rw [hlow, hmi]; exact hminvA))
        rfl
        (by simp only [Csub.csReturnedState_eq_result, retTo, CarryResult.monproMem_def, hpdN])

/-- The Montgomery-inverse side condition forces an odd modulus. -/
theorem odd_of_minvA {mm minv : Nat}
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) : mm % 2 = 1 := by
  have h2 : (mm % Limbs.radix * minv + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd (mm % Limbs.radix * minv + 1)
      (show 2 ∣ 2 ^ 256 from dvd_pow_self 2 (by norm_num)), hminvA]
  have hr : mm % Limbs.radix % 2 = mm % 2 :=
    Nat.mod_mod_of_dvd mm (show 2 ∣ Limbs.radix from dvd_pow_self 2 (by norm_num))
  rcases Nat.mod_two_eq_zero_or_one mm with h0 | h1
  · rw [Nat.add_mod, Nat.mul_mod, hr, h0] at h2
    simp at h2
  · exact h1

/-- `SQUARE` writes only below `5184`, so the configuration words survive. -/
theorem sqMem_frame' {s : State} {mem : ByteArray} {n bsize minv : Nat}
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hf : Frame mem n bsize minv) :
    Frame (SquareResult.sqMem s mem n) n bsize minv :=
  have key := SquareResult.sqMem_frame s mem n hn (by omega)
  ⟨by rw [key.1]; exact hf.s32, by rw [key.2.1]; exact hf.minvW,
   by rw [key.2.2.1]; exact hf.ml, by rw [key.2.2.2.1]; exact hf.tl,
   by rw [key.2.2.2.2]; exact hf.eoff⟩

/-- The `SQUARE` step of the concrete instance, for the widths the kernel does
not accelerate: `common` with `hd = sq_row` falls back to the generic `MONPRO`
(`Fast.SquareFull.gasSteps_squareFull`). -/
def subsSquare (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    ∀ (ret : UInt256) (tail : List UInt256) (mem : ByteArray) (a : Nat),
      ¬ (n = 4 ∨ n = 8) → tail.length ≤ 998 →
      Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
      Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
      Model.FastRepresents mem 512 n a → a < mm →
      Challenge.EvmProof.GasSteps (sqCall s mem ret tail)
        (retTo s (SquareResult.sqMem s mem n) ret tail) := by
  intro ret tail mem a hslow hcap hjump hf hm ha ham
  -- `GasSteps` lives in `Type`, so the limb count has to be split by `cases`.
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n1 =>
    cases n1 with
    | zero => exact absurd hn (by omega)
    | succ p =>
      have hlow : (MachineState.readWord mem (32 * (p + 2) - 32)).toNat =
          mm % Limbs.radix := by
        have h := Model.readWord_of_fastRepresents hm (j := p + 1) (by omega)
        rw [show (0 : Nat) + 32 * (p + 1) = 32 * (p + 2) - 32 from by omega,
          show p + 1 + 1 - 1 - (p + 1) = 0 from by omega, pow_zero, Nat.div_one] at h
        exact h
      have hmi : (MachineState.readWord mem 5280).toNat = minv := by
        rw [hf.minvW, toNat_ofNat_self hminvlt]
      exact Challenge.EvmProof.GasSteps.cast
        (SquareFull.gasSteps_squareFull s mem p a mm ret tail hcap hrun hcode hfork hnp
          hact (by omega) hslow hcds hf.s32 hf.tl hf.ml hjump ha hm ham hmpos
          (by rw [hlow, hmi]; exact hminvA))
        rfl rfl

/-- The in-kernel square loop writes only below `5216`, so the configuration
words survive. -/
theorem sqLoopMem_frame' {s : State} {mem : ByteArray} {n bsize minv : Nat} (k : Nat)
    (hfast : n = 4 ∨ n = 8) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hf : Frame mem n bsize minv) :
    Frame (SquareLoop.sqLoopMem s n k mem) n bsize minv :=
  have key := SquareLoop.sqLoopMem_frame s mem n k hfast hn (by omega)
  ⟨by rw [key.1]; exact hf.s32, by rw [key.2.1]; exact hf.minvW,
   by rw [key.2.2.1]; exact hf.ml, by rw [key.2.2.2.1]; exact hf.tl,
   by rw [key.2.2.2.2]; exact hf.eoff⟩

/-- The in-kernel square-loop step of the concrete instance: for `n ∈ {4, 8}`
the kernel performs all `k` squares without leaving its row frame and returns to
the caller's `after_sq` (pc 3243) (`Fast.SquareLoop.gasSteps_squareLoop`). -/
def subsSquareLoop (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    ∀ (k : Nat) (ret : UInt256) (tail : List UInt256) (mem : ByteArray) (a : Nat),
      n = 4 ∨ n = 8 → 1 ≤ k → k ≤ 16 → tail.length ≤ 982 →
      MachineState.readWord mem 5184 = UInt256.ofNat k →
      Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
      Model.FastRepresents mem 512 n a → a < mm →
      Challenge.EvmProof.GasSteps (sqCall s mem ret tail)
        (retTo s (SquareLoop.sqLoopMem s n k mem) (UInt256.ofNat 3366) tail) := by
  intro k ret tail mem a hfast hk hk16 hcap hcount hf hm ha ham
  -- `GasSteps` lives in `Type`, so the limb count has to be split by `cases`.
  cases n with
  | zero => exact absurd hn (by omega)
  | succ n1 =>
    cases n1 with
    | zero => exact absurd hn (by omega)
    | succ p =>
      have hlow : (MachineState.readWord mem (32 * (p + 2) - 32)).toNat =
          mm % Limbs.radix := by
        have h := Model.readWord_of_fastRepresents hm (j := p + 1) (by omega)
        rw [show (0 : Nat) + 32 * (p + 1) = 32 * (p + 2) - 32 from by omega,
          show p + 1 + 1 - 1 - (p + 1) = 0 from by omega, pow_zero, Nat.div_one] at h
        exact h
      have hmi : (MachineState.readWord mem 5280).toNat = minv := by
        rw [hf.minvW, toNat_ofNat_self hminvlt]
      exact Challenge.EvmProof.GasSteps.cast
        (SquareLoop.gasSteps_squareLoop s mem p a mm k ret tail hcap hrun hcode hfork
          hnp hact (by omega) hfast hk hk16 hcount hcds hf.s32 hf.tl hf.ml ha hm ham hmpos
          (odd_of_minvA hminvA) (by rw [hlow, hmi]; exact hminvA))
        rfl rfl

/-- The concrete subroutine contracts. -/
def subs (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    Subroutines s n bsize mm minv where
  mpMem pa pb pd mem := CarryResult.monproMem s mem pa pb n pd
  amMem pa pb pd mem := amMemOf mem pa pb n pd
  mpFrame pa pb pd mem hpd hf := monproMem_frame' pa pb pd (by omega) (by omega) (by omega) hf
  amFrame pa pb pd mem hpd hf := amMemOf_frame pa pb pd (by omega) (by omega) (by omega) hf
  monpro := subsMonpro s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
    hminvlt hminvA
  addmod := subsAddmod s n bsize minv hcode hfork hrun hnp hact hn (by omega)
  sqMem mem := SquareResult.sqMem s mem n
  sqFrame _ hf := sqMem_frame' (by omega) (by omega) hf
  square := subsSquare s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
    hminvlt hminvA
  sqValue mem a hf hm ha ham := by
    have hlow : (MachineState.readWord mem (32 * n - 32)).toNat = mm % Limbs.radix := by
      have h := Model.readWord_of_fastRepresents hm (j := n - 1) (by omega)
      rw [show (0 : Nat) + 32 * (n - 1) = 32 * n - 32 from by omega,
        show n - 1 - (n - 1) = 0 from by omega, pow_zero, Nat.div_one] at h
      exact h
    have hmi : (MachineState.readWord mem 5280).toNat = minv := by
      rw [hf.minvW, toNat_ofNat_self hminvlt]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact SquareResult.sqMem_represents s mem p a mm (by omega) ha hm (odd_of_minvA hminvA) ham
      (by rw [hlow, hmi]; exact hminvA)
  sqKeep ptr v mem hptr hdisj hrep :=
    SquareResult.sqMem_fastRepresents_outside s mem n ptr n v (by omega) (by omega)
      (Or.inl hptr) (Or.inl (by omega)) hdisj.symm hrep
  sqLoopMem k mem := SquareLoop.sqLoopMem s n k mem
  sqLoopFrame k _ hfast hf := sqLoopMem_frame' k hfast (by omega) (by omega) hf
  squareLoop := subsSquareLoop s n bsize mm minv hcode hfork hrun hnp hact hcds hn
    (by omega) hmpos hminvlt hminvA
  sqLoopValue k mem a hfast hf hm ha ham := by
    have hlow : (MachineState.readWord mem (32 * n - 32)).toNat = mm % Limbs.radix := by
      have h := Model.readWord_of_fastRepresents hm (j := n - 1) (by omega)
      rw [show (0 : Nat) + 32 * (n - 1) = 32 * n - 32 from by omega,
        show n - 1 - (n - 1) = 0 from by omega, pow_zero, Nat.div_one] at h
      exact h
    have hmi : (MachineState.readWord mem 5280).toNat = minv := by
      rw [hf.minvW, toNat_ofNat_self hminvlt]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact SquareLoop.sqLoopMem_represents s mem p a mm k hfast (by omega) ha hm
      (odd_of_minvA hminvA) ham hmpos (by rw [hlow, hmi]; exact hminvA)
  sqLoopKeep k ptr v mem hfast hptr hdisj hrep :=
    SquareLoop.sqLoopMem_fastRepresents_outside s mem n k ptr n v hfast (by omega)
      (by omega) (Or.inl hptr) (Or.inl (by omega)) hdisj.symm hrep

/-- The value-level contract the concrete pair satisfies. -/
theorem specOf (s : State) (n mm minv : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    SubSpec (fun pa pb pd mem => CarryResult.monproMem s mem pa pb n pd)
      (fun pa pb pd mem => amMemOf mem pa pb n pd) n mm (Limbs.radix ^ n) minv where
  mpValueRaw pa pb pd mem a b hpa hpb hpd hm hminv ha hb ham := by
    have hlow : (MachineState.readWord mem (32 * n - 32)).toNat = mm % Limbs.radix := by
      have h := Model.readWord_of_fastRepresents hm (j := n - 1) (by omega)
      rw [show (0 : Nat) + 32 * (n - 1) = 32 * n - 32 from by omega,
        show n - 1 - (n - 1) = 0 from by omega, pow_zero, Nat.div_one] at h
      exact h
    have hmi : (MachineState.readWord mem 5280).toNat = minv := by
      rw [hminv, toNat_ofNat_self hminvlt]
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    exact CarryResult.monproMem_represents s mem pa pb p pd a b mm (by omega) hpa hpb hpd ha hb hm hodd
      ham (by rw [hlow, hmi]; exact hminvA)
  mpFrame pa pb pd ptr v mem hptr hdisj hrep :=
    CarryResult.monproMem_fastRepresents_outside s mem pa pb n pd ptr n v (by omega) (by omega)
      (by omega) (by omega) (by omega) hrep
  mpMinv pa pb pd mem hpd :=
    CarryResult.monproMem_readWord_high s mem pa pb n pd 5280 (by omega) (by omega) (by omega)
      (by omega)
  amValue pa pb pd mem a b hpa hpb hpd hm ha hb hab :=
    Csub.addmod_csub_correct mem pa pb n a b mm pd hn (by omega) hpa hpb ha hb hm hmpos hab
  amFrame pa pb pd ptr v mem hptr hdisj hrep :=
    Csub.addmod_csub_preserves_region mem pa pb n pd ptr n v hn (by omega) (by omega)
      (by omega) hrep
  amMinv pa pb pd mem hpd :=
    amMemOf_readWord_high mem pa pb n pd 5280 (by omega) (by omega) (by omega) (by omega)

/-- `specOf` transported onto a `Subroutines` record, so no call site ever has
to unify a projection of `subs` with a lambda. -/
theorem specOf_of {s : State} {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv)
    (hmp : sub.mpMem = fun pa pb pd mem => CarryResult.monproMem s mem pa pb n pd)
    (ham : sub.amMem = fun pa pb pd mem => amMemOf mem pa pb n pd)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hodd : mm % 2 = 1) (hmpos : 0 < mm)
    (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv := by
  rw [hmp, ham]
  exact specOf s n mm minv hn (by omega) hodd hmpos hminvlt hminvA

/-- The two memory transformers of `subs`, read off by `iota` rather than by
unification: `unfold` turns the projection into a projection *of a
constructor*, which `whnfCore` reduces without ever unfolding
`CarryResult.monproMem` into its `writeBytes` / `rowsMem` recursion. -/
theorem subs_mpMem (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
      hminvlt hminvA).mpMem =
      fun pa pb pd mem => CarryResult.monproMem s mem pa pb n pd := by
  delta subs
  rfl

theorem subs_amMem (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
      hminvlt hminvA).amMem =
      fun pa pb pd mem => amMemOf mem pa pb n pd := by
  delta subs
  rfl

/-- The value contract of the concrete instance, at the concrete instance. -/
theorem specOf_subs (s : State) (n bsize mm minv : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hminvlt : minv < 2 ^ 256)
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) (hodd : mm % 2 = 1) :
    SubSpec (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
        hminvlt hminvA).mpMem
      (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos hminvlt
        hminvA).amMem n mm (Limbs.radix ^ n) minv :=
  specOf_of (subs s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos
    hminvlt hminvA)
    (subs_mpMem s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos hminvlt
      hminvA)
    (subs_amMem s n bsize mm minv hcode hfork hrun hnp hact hcds hn (by omega) hmpos hminvlt
      hminvA)
    hn (by omega) hodd hmpos hminvlt hminvA

end Challenge.Modexp.Submission.Proofs.Fast.Exp

#print axioms Challenge.Modexp.Submission.Proofs.Fast.Exp.subs
#print axioms Challenge.Modexp.Submission.Proofs.Fast.Exp.specOf_subs
