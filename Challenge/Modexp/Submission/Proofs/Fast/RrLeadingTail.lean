import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingSuffix
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseCorrect

set_option warningAsError true
set_option maxHeartbeats 16000000

/-!
# Unchanged post-RR tail

This private theorem factors the existing `handled_of_rrHead` proof at its
`rrDone` boundary.  It accepts any RR value satisfying the same range and
modular-value contracts, so the direct leading-one suffix can reuse the base,
exponent, and return proof without changing their premises.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTail

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Exp
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingSuffix

theorem handled_of_rrDone (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv rr : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hrrlt : rr < mm)
    (hrrmod : rr ≡ Limbs.radix ^ n * Limbs.radix ^ n [MOD mm])
    (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm (Limbs.radix ^ n) rr)
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (rrDone s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  rcases Nat.eq_zero_or_pos bsize with hb0 | hb0
  · subst hb0
    have hEb : EbInv (mcopyMem mem 1024 4096 (32 * n)) n mm 0
        (expAcc mm (Limbs.radix ^ n) 0 (expBits input 0) 0) := by
      refine ⟨?_, ?_, ?_, ⟨0, Limbs.radix_pos, ?_⟩⟩
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 0 n mm
          (by omega) hinv.modulus
      · exact Csub.fastRepresents_mcopy _ 4096 1024 n (Limbs.radix ^ n % mm)
          (by omega) hinv.r1
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 2048 n 0
          (by omega) hbase0
      · exact Csub.fastRepresents_mcopy_disjoint _ 4096 1024 (32 * n) 3072 n 0
          (by omega) hone0
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_bDone input s mem n 0 esize msize mm minv 0 sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 (by omega) he hmz hm32
        hbsize hesize hmsz hmm hodd hradix hmpos (by simpa using Nat.ModEq.refl 0)
        hframe hEb
    exact ⟨final,
      ⟨(gasSteps_rrDone_skip s mem n esize msize hcode hfork hrun hnp).trans tr⟩,
      hdone, hres⟩
  · obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_baseHead input s mem n bsize esize msize mm minv rr sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb hb0 he hmz hm32
        hbsize hesize hmsz hmm hodd hradix hrrlt hrrmod hframe
        hinv.modulus hinv.r1 hinv.cc hinv.rr hacc0 hone0
    exact ⟨final,
      ⟨(gasSteps_rrDone_base s mem n bsize esize msize hb (by omega)
        hcode hfork hrun hnp).trans tr⟩,
      hdone, hres⟩

/-- Everything after the direct helper's rejoin, with exactly the public
premises of the old RR-head theorem. -/
theorem handled_of_directRR (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hframe : Frame mem n bsize minv)
    (hinv : RrInv mem n mm (Limbs.radix ^ n)
      (Limbs.radix * Limbs.radix ^ n % mm))
    (hacc0 : Model.FastRepresents mem 1024 n 0)
    (hbase0 : Model.FastRepresents mem 2048 n 0)
    (hone0 : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (rrHead s mem n bsize esize msize (directCounter n)) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm :=
    Model.coprime_radix_pow_of_odd hodd n
  let finalMem := rrSuffixMem sub.mpMem n (directCounter n) mem (directCounter n + 1)
  let finalValue := rrSuffixValue mm (Limbs.radix ^ n) n (directCounter n)
    (Limbs.radix * Limbs.radix ^ n % mm) (directCounter n + 1)
  have hrr := gasSteps_directSuffix s sub spec mem esize msize hmpos hcop hn hn32
    hframe hinv hcode hfork hrun hnp
  have hfinal := directSuffix_final spec hmpos hcop hn hn32 mem hframe.minvW hinv
  have hframeFinal : Frame finalMem n bsize minv :=
    rrSuffixMem_frame sub (directCounter n) mem hframe (directCounter n + 1)
  have haccFinal : Model.FastRepresents finalMem 1024 n 0 :=
    rrSuffixMem_preserves sub spec (directCounter n) 1024 0 mem (by omega) hacc0
      (directCounter n + 1)
  have hbaseFinal : Model.FastRepresents finalMem 2048 n 0 :=
    rrSuffixMem_preserves sub spec (directCounter n) 2048 0 mem (by omega) hbase0
      (directCounter n + 1)
  have honeFinal : Model.FastRepresents finalMem 3072 n 0 :=
    rrSuffixMem_preserves sub spec (directCounter n) 3072 0 mem (by omega) hone0
      (directCounter n + 1)
  obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
    handled_of_rrDone input s finalMem n bsize esize msize mm minv finalValue
      sub spec hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32
      hbsize hesize hmsz hmm hodd hradix (rrSuffixValue_lt hmpos
        (Nat.mod_lt _ hmpos) (directCounter n + 1)) hfinal.2 hframeFinal
      hfinal.1 haccFinal hbaseFinal honeFinal
  exact ⟨final, ⟨hrr.trans tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTail
