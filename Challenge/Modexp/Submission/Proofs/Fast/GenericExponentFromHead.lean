import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Generic exponent continuation after the relocated `BDONE` dispatcher

The cc628 miss path performs the old R1-to-ACC copy and lands directly at
`Exp.ebHead`. This file factors the unchanged exponent loop, Montgomery decode,
and return proof from precisely that state.

It imports `Fast.Exp`; `Fast.Exp` must not import this file. The eventual
aggregate driver lives in a later module, preserving an acyclic dependency
graph.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The inherited generic exponent chain with only the now-replaced `BDONE`
initialization removed. -/
def gasSteps_ebChainFromHead (s : State) {n bsize mm minv R : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem input : ByteArray) (esize msize bM : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (_hradix : Limbs.radix ≤ mm) (hbM : bM < mm)
    (hact : 298 ≤ s.activeWords.toNat)
    (hframe : Exp.Frame mem n bsize minv)
    (hinv : Exp.EbInv (Exp.mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (Exp.expAcc mm R bM (Exp.expBits input bsize) 0))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Exp.ebHead s (Exp.mcopyMem mem 1024 4096 (32 * n))
        n bsize esize msize 0)
      (Exp.returnedState s
        (sub.mpMem 1024 3072 1024
          (Exp.storeWord
            (Exp.ebMems sub.mpMem input bsize n
              (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
            (3040 + 32 * n) (UInt256.ofNat 1)))
        n bsize esize msize) := by
  have hframe0 : Exp.Frame (Exp.mcopyMem mem 1024 4096 (32 * n))
      n bsize minv := Exp.frame_mcopyMem (by omega) hframe
  have hloop := Exp.ebMems_inv spec hm hcop hn hn32 bM hbM input bsize
    (Exp.mcopyMem mem 1024 4096 (32 * n)) hframe0.minvW hinv esize
  have hframeE : Exp.Frame
      (Exp.ebMems sub.mpMem input bsize n
        (Exp.mcopyMem mem 1024 4096 (32 * n)) esize) n bsize minv :=
    Exp.ebMems_frame sub input (Exp.mcopyMem mem 1024 4096 (32 * n))
      hn32 hframe0 esize
  have hframeS : Exp.Frame
      (Exp.storeWord
        (Exp.ebMems sub.mpMem input bsize n
          (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
        (3040 + 32 * n) (UInt256.ofNat 1)) n bsize minv :=
    Exp.frame_storeWord (UInt256.ofNat 1) (by omega) hframeE
  have hone : Model.FastRepresents
      (Exp.storeWord
        (Exp.ebMems sub.mpMem input bsize n
          (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
        (3040 + 32 * n) (UInt256.ofNat 1)) 3072 n 1 := by
    obtain ⟨one, honelt, honerep⟩ := hloop.oneBlock
    have h := Exp.write_low_limb (UInt256.ofNat 1) (by omega) honerep honelt
    rwa [show (UInt256.ofNat 1).toNat = 1 from by decide] at h
  have hmodS := Exp.storeWord_frame
    (Exp.ebMems sub.mpMem input bsize n
      (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
    (3040 + 32 * n) 0 n mm (UInt256.ofNat 1) (Or.inr (by omega))
    hloop.modulus
  have haccS := Exp.storeWord_frame
    (Exp.ebMems sub.mpMem input bsize n
      (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
    (3040 + 32 * n) 1024 n
    (Exp.expAcc mm R bM (Exp.expBits input bsize) (8 * esize))
    (UInt256.ofNat 1) (Or.inr (by omega)) hloop.accBlock
  exact (((Exp.gasSteps_ebLoop s sub spec
      (Exp.mcopyMem mem 1024 4096 (32 * n)) input esize msize bM
      hdata hm hcop hn hn32 hb he hbM hact hframe0 hinv hcode hfork hrun hnp).trans
    (Exp.gasSteps_ebHeadExit s
      (Exp.ebMems sub.mpMem input bsize n
        (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
      n bsize esize msize esize he (by omega) rfl
      hcode hfork hrun hnp)).trans
    ((Exp.gasSteps_ebEnd s
      (Exp.ebMems sub.mpMem input bsize n
        (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
      n bsize esize msize esize hn hn32 hact hcode hfork hrun hnp).trans
    (sub.monpro 1024 3072 1024 (UInt256.ofNat 1619)
      (Exp.outer n bsize esize msize)
      (Exp.storeWord
        (Exp.ebMems sub.mpMem input bsize n
          (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
        (3040 + 32 * n) (UInt256.ofNat 1))
      (Exp.expAcc mm R bM (Exp.expBits input bsize) (8 * esize)) 1
      (by simp [Exp.outer]) (by omega) (by omega) (by omega) (by omega)
      (by omega) Exp.jumpD1876 hframeS hmodS haccS hone
      (Exp.expAcc_lt hm _ _)))).trans
    (Exp.gasSteps_return s
      (sub.mpMem 1024 3072 1024
        (Exp.storeWord
          (Exp.ebMems sub.mpMem input bsize n
            (Exp.mcopyMem mem 1024 4096 (32 * n)) esize)
          (3040 + 32 * n) (UInt256.ofNat 1)))
      n bsize esize msize hn hn32 hmz hm32 hact hcode hfork hrun hnp)

/-- Semantic packaging of `gasSteps_ebChainFromHead`, in the exact form the
cc628 miss branch requires. -/
theorem handled_of_ebHead (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv bM : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize *
      Limbs.radix ^ n [MOD mm])
    (hframe : Exp.Frame mem n bsize minv)
    (hEb : Exp.EbInv (Exp.mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (Exp.expAcc mm (Limbs.radix ^ n) bM (Exp.expBits input bsize) 0)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (Exp.ebHead s (Exp.mcopyMem mem 1024 4096 (32 * n))
          n bsize esize msize 0) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm :=
    Model.coprime_radix_pow_of_odd hodd n
  have hframeC : Exp.Frame (Exp.mcopyMem mem 1024 4096 (32 * n))
      n bsize minv := Exp.frame_mcopyMem (by omega) hframe
  have htrace := gasSteps_ebChainFromHead s sub spec mem input esize msize bM
    hdata hmpos hcop hn hn32 hb he hmz hm32 hradix hbMlt hact hframe hEb
    hcode hfork hrun hnp
  have hfinal := Exp.ebMem_final spec hmpos hn hn32 hcop hradix hbMlt hbMform
    input bsize esize rfl (Exp.mcopyMem mem 1024 4096 (32 * n))
    hframeC.minvW hEb
  refine Exp.handled_of_trace input
    (Exp.ebHead s (Exp.mcopyMem mem 1024 4096 (32 * n))
      n bsize esize msize 0) s _ n bsize esize msize _ hstack htrace hn hm32
      (by omega) hbsize hesize hmsz hfinal ?_
  rw [hmm]

end Challenge.Modexp.Submission.Proofs.Fast
