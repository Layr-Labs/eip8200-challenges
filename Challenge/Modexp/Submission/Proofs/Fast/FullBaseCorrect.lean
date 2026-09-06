import Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseValueBridge
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Full-width-base dispatcher closure

This module restores the public `handled_of_baseHead` boundary after pc1639
was redirected.  A miss reuses the relocated legacy Horner proof; a hit copies
the exact full-width base, reduces it once, converts it to Montgomery form and
then rejoins the already proved exponent tail at `bDone`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem handled_of_baseHead (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv rr : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (he : esize ≤ 1024) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hrrlt : rr < mm)
    (hrrmod : rr ≡ Limbs.radix ^ n * Limbs.radix ^ n [MOD mm])
    (hframe : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ n % mm))
    (hcc : Model.FastRepresents mem 5120 n (Limbs.radix * Limbs.radix ^ n % mm))
    (hrrb : Model.FastRepresents mem 6144 n rr)
    (hacc : Model.FastRepresents mem 1024 n 0)
    (hone : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (baseHead s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm :=
    Model.coprime_radix_pow_of_odd hodd n
  have hbword : bsize < 2 ^ 256 :=
    lt_of_le_of_lt hb (by norm_num)
  have hredirect : Challenge.EvmProof.GasSteps
      (baseHead s mem n bsize esize msize)
      (FullBase.entryState s mem n bsize esize msize) :=
    Challenge.EvmProof.GasSteps.cast
      (Bytecode.FullBaseHitTrace.gasSteps_redirect s mem n bsize esize msize
        hcode hfork hrun hnp) rfl rfl
  have hguard := Bytecode.FullBaseHitTrace.gasSteps_guard
    s mem n bsize esize msize hn32 hbword hact hcode hfork hrun hnp
  by_cases hmatch : FullBase.Matches mem n bsize
  · have hbEq : bsize = 32 * n := hmatch.1
    have htop : R1.TopBitSet mem := hmatch.2
    have hguardHit : Challenge.EvmProof.GasSteps
        (FullBase.entryState s mem n bsize esize msize)
        (FullBase.copyState s mem n bsize esize msize) := by
      simpa [hmatch] using hguard
    let copied := FullBase.copyBaseMem mem input n
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let baseM := base * Limbs.radix ^ n % mm
    have hframeCopy : Frame copied n bsize minv := by
      dsimp only [copied]
      exact FullBase.copyBaseMem_frame hn32 hframe
    have hcopy := Bytecode.FullBaseHitTrace.gasSteps_copyAdd
      s mem input n bsize esize msize hn32 hact hdata hcode hfork hrun hnp
    have hj3644 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
        (UInt256.ofNat 3644).toNat = true := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (show 3644 < 2 ^ 256 by norm_num)]
      exact jumpDest3644
    by_cases hbaseTop : FullBase.BaseTopBitSet copied
    · let reduced := sub.amMem 1024 3072 1024 copied
      let converted := sub.mpMem 1024 6144 2048 reduced
      have hvalues := FullBase.reduceThenMonpro sub spec mem input hn hn32 hmpos hodd
        hcop hrrmod hrrlt hframe hmod hr1 hone hrrb htop
      dsimp only at hvalues
      rcases hvalues with
        ⟨hred, hframeRed, hmodRed, hrrRed, hbaseConv, hmodConv, hrrConv,
          hr1Conv, honeConv, hframeConv⟩
      have hdispatch := Bytecode.FullBaseHitTrace.gasSteps_dispatch_hit
        s mem input n bsize esize msize hbaseTop hcode hfork hrun hnp
      have hadd : Challenge.EvmProof.GasSteps
          (FullBase.addCallState s mem input n bsize esize msize)
          (FullBase.afterAddState s reduced n bsize esize msize) := by
        exact Challenge.EvmProof.GasSteps.cast
          (sub.addmod 1024 3072 1024 (UInt256.ofNat 3644)
            (outer n bsize esize msize) copied (by simp [outer])
            (by omega) (by omega) (by omega) (by omega) (by omega) hj3644 hframeCopy)
          rfl rfl
      have hafter := Bytecode.FullBaseHitTrace.gasSteps_afterAdd
        s reduced n bsize esize msize hcode hfork hrun hnp
      have hredlt : base % mm < mm := Nat.mod_lt _ hmpos
      have hmonpro : Challenge.EvmProof.GasSteps
          (FullBase.monproCallState s reduced n bsize esize msize)
          (FullBase.rejoinState s converted n bsize esize msize) := by
        exact Challenge.EvmProof.GasSteps.cast
          (sub.monpro 1024 6144 2048 (UInt256.ofNat 1755)
            (outer n bsize esize msize) reduced (base % mm) rr
            (by simp [outer]) (by omega) (by omega) (by omega) (by omega) (by omega)
            jumpD1755 hframeRed hmodRed hred hrrRed hredlt) rfl rfl
      have hrejoin : Challenge.EvmProof.GasSteps
          (FullBase.rejoinState s converted n bsize esize msize)
          (bDone s converted n bsize esize msize) := by
        exact Challenge.EvmProof.GasSteps.cast
          (gasSteps_bRejoin s converted n bsize esize msize hcode hfork hrun hnp)
          rfl rfl
      have hEb : EbInv (mcopyMem converted 1024 4096 (32 * n)) n mm baseM
          (expAcc mm (Limbs.radix ^ n) baseM (expBits input bsize) 0) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm
            (by omega) hmodConv
        · exact Csub.fastRepresents_mcopy _ 4096 1024 n
            (Limbs.radix ^ n % mm) (by omega) hr1Conv
        · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n
            baseM (by omega) hbaseConv
        · exact ⟨0, Limbs.radix_pos,
            Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n 0
              (by omega) honeConv⟩
      have hbaseForm : baseM ≡
          Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm] := by
        dsimp only [baseM, base]
        rw [hbEq]
        exact Nat.mod_modEq _ _
      obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
        handled_of_bDone input s converted n bsize esize msize mm minv baseM sub spec
          hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize
          hmsz hmm hodd hradix (Nat.mod_lt _ hmpos) hbaseForm hframeConv hEb
      have hroute := hredirect.trans hguardHit
      have hroute := hroute.trans hcopy
      have hroute := hroute.trans hdispatch
      have hroute := hroute.trans hadd
      have hroute := hroute.trans hafter
      have hroute := hroute.trans hmonpro
      have hroute := hroute.trans hrejoin
      exact ⟨final, ⟨hroute.trans tr⟩, hdone, hres⟩
    · have hready := FullBase.copyBaseReady (memory := mem) (input := input)
        (n := n) (bsize := bsize) (minv := minv) (mm := mm)
        (R := Limbs.radix ^ n) (rr := rr) hn32 hframe hmod hr1 hone hrrb
      rcases hready with
        ⟨hbaseCopy, hframeCopyLow, hmodCopy, hrrCopy, hr1Copy, honeCopy⟩
      have hbaseLt : base < mm :=
        FullBase.baseValue_lt_modulus_of_not_top (memory := mem) (input := input)
          (n := n) (mm := mm) (by omega) hmod htop hbaseCopy hbaseTop
      let converted := sub.mpMem 1024 6144 2048 copied
      have hbaseAcc : Model.FastRepresents copied 1024 n (base % mm) := by
        simpa [Nat.mod_eq_of_lt hbaseLt] using hbaseCopy
      have hbaseConv : Model.FastRepresents converted 2048 n
          (base * Limbs.radix ^ n % mm) :=
        Exp.blMem_base spec hmpos hn32 hcop hrrmod hrrlt copied
          hframeCopyLow.minvW hmodCopy hbaseAcc hrrCopy
      have hmodConv : Model.FastRepresents converted 0 n mm :=
        spec.mpFrame 1024 6144 2048 0 mm copied (by omega) (Or.inr (by omega)) hmodCopy
      have hrrConv : Model.FastRepresents converted 6144 n rr :=
        spec.mpFrame 1024 6144 2048 6144 rr copied (by omega) (Or.inl (by omega)) hrrCopy
      have hr1Conv : Model.FastRepresents converted 4096 n
          (Limbs.radix ^ n % mm) :=
        spec.mpFrame 1024 6144 2048 4096 (Limbs.radix ^ n % mm)
          copied (by omega) (Or.inl (by omega)) hr1Copy
      have honeConv : Model.FastRepresents converted 3072 n 0 :=
        spec.mpFrame 1024 6144 2048 3072 0 copied (by omega)
          (Or.inl (by omega)) honeCopy
      have hframeConv : Frame converted n bsize minv :=
        sub.mpFrame 1024 6144 2048 copied (by omega) hframeCopyLow
      have hdispatch := Bytecode.FullBaseHitTrace.gasSteps_dispatch_skip
        s mem input n bsize esize msize hbaseTop hcode hfork hrun hnp
      have hafter := Bytecode.FullBaseHitTrace.gasSteps_afterAdd
        s copied n bsize esize msize hcode hfork hrun hnp
      have hmonpro : Challenge.EvmProof.GasSteps
          (FullBase.monproCallState s copied n bsize esize msize)
          (FullBase.rejoinState s converted n bsize esize msize) := by
        exact Challenge.EvmProof.GasSteps.cast
          (sub.monpro 1024 6144 2048 (UInt256.ofNat 1755)
            (outer n bsize esize msize) copied (base % mm) rr
            (by simp [outer]) (by omega) (by omega) (by omega) (by omega) (by omega)
            jumpD1755 hframeCopyLow hmodCopy hbaseAcc hrrCopy
            (Nat.mod_lt _ hmpos)) rfl rfl
      have hEb : EbInv (mcopyMem converted 1024 4096 (32 * n)) n mm
          (base * Limbs.radix ^ n % mm)
          (expAcc mm (Limbs.radix ^ n)
            (base * Limbs.radix ^ n % mm) (expBits input bsize) 0) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm
            (by omega) hmodConv
        · exact Csub.fastRepresents_mcopy _ 4096 1024 n
            (Limbs.radix ^ n % mm) (by omega) hr1Conv
        · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n
            (by omega) hbaseConv
        · exact ⟨0, Limbs.radix_pos,
            Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n 0
              (by omega) honeConv⟩
      have hbaseForm : base * Limbs.radix ^ n % mm ≡
          Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm] := by
        dsimp only [base]
        rw [hbEq]
        exact Nat.mod_modEq _ _
      obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
        handled_of_bDone input s converted n bsize esize msize mm minv
          (base * Limbs.radix ^ n % mm) sub spec
          hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize
          hmsz hmm hodd hradix (Nat.mod_lt _ hmpos) hbaseForm hframeConv hEb
      have hroute := hredirect.trans hguardHit
      have hroute := hroute.trans hcopy
      have hroute := hroute.trans hdispatch
      have hroute := hroute.trans hafter
      have hroute := hroute.trans hmonpro
      have hroute := hroute.trans hrejoin
      exact ⟨final, ⟨hroute.trans tr⟩, hdone, hres⟩
  · have hguardMiss : Challenge.EvmProof.GasSteps
        (FullBase.entryState s mem n bsize esize msize)
        (FullBase.fallbackState s mem n bsize esize msize) := by
      simpa [hmatch] using hguard
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_baseFallback input s mem n bsize esize msize mm minv rr sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb hb0 he hmz hm32 hbsize
        hesize hmsz hmm hodd hradix hrrlt hrrmod hframe hmod hr1 hcc hrrb hacc hone
    exact ⟨final, ⟨(hredirect.trans hguardMiss).trans tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.Exp
