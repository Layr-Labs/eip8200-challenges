import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCorrect
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Semantic correctness of a fixed-exponent hit
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentHitCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentChainCorrect
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Correctness of either minimal fixed addition chain (`3` or `65537`). -/
theorem handled_of_fixed (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv R bM count : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : s.callStack = []) (hactive : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmz : 32 < msize)
    (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hm : 0 < mm) (hcop : Nat.Coprime R mm) (hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize * R [MOD mm])
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hexp : Precompile.bytesToNatPadded input (96 + bsize) esize =
      2 ^ count + 1)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2048 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 3072 n one) :
    FixedExponentRoute.Handled input
      (special s memory n bsize esize msize count) := by
  let memSq := fixedMems sub.mpMem n memory count
  let sqVal := fixedValue mm R bM count
  let prodVal := Model.montMul mm R sqVal bM
  let memProd := sub.mpMem 1024 2048 1024 memSq
  let memOne := Exp.storeWord memProd (3040 + 32 * n) (UInt256.ofNat 1)
  let memOut := sub.mpMem 1024 3072 1024 memOne
  have hsqInv : Exp.EbInv memSq n mm bM sqVal := by
    simpa [memSq, sqVal] using
      fixedMems_inv sub spec memory hm hn hn32 hbMlt hframe hmod hbase hone count
  have hframeSq : Exp.Frame memSq n bsize minv := by
    simpa [memSq] using fixedMems_frame sub memory hn32 hframe count
  have hsqLt : sqVal < mm := by
    simpa [sqVal] using fixedValue_lt hm hbMlt count
  have htraceSq := gasSteps_fixedSquares s sub spec memory esize msize count bM
    hm hn hn32 hcount hcount16 hbMlt hactive hframe hmod hbase hone
    hcode hfork hrun hnp
  have htraceProdCall := FixedExponentChainTrace.gasSteps_product
    s memSq n bsize esize msize hcode hfork hrun hnp
  have htraceProdMp := sub.monpro 1024 2048 1024 (UInt256.ofNat 3808)
    (Exp.outer n bsize esize msize) memSq sqVal bM
    (by simp [Exp.outer]) (by omega) (by omega) (by omega) (by omega)
    (by omega) jumpD3808 hframeSq hsqInv.modulus hsqInv.accBlock
    hsqInv.baseBlock hsqLt
  have htraceProd : Challenge.EvmProof.GasSteps
      (product s memSq n bsize esize msize)
      (decode s memProd n bsize esize msize) :=
    htraceProdCall.trans htraceProdMp
  have hframeProd : Exp.Frame memProd n bsize minv :=
    sub.mpFrame 1024 2048 1024 memSq (by omega) hframeSq
  have hmodProd : Model.FastRepresents memProd 0 n mm :=
    spec.mpFrame 1024 2048 1024 0 mm memSq (by omega) (Or.inr (by omega))
      hsqInv.modulus
  have haccProd : Model.FastRepresents memProd 1024 n prodVal :=
    spec.mpValue 1024 2048 1024 memSq sqVal bM (by omega) (by omega)
      (by omega) hsqInv.modulus hframeSq.minvW hsqInv.accBlock
      hsqInv.baseBlock hsqLt hbMlt
  obtain ⟨one, honeLt, honeRep⟩ := hsqInv.oneBlock
  have honeProd : Model.FastRepresents memProd 3072 n one :=
    spec.mpFrame 1024 2048 1024 3072 one memSq (by omega)
      (Or.inl (by omega)) honeRep
  have hframeOne : Exp.Frame memOne n bsize minv :=
    Exp.frame_storeWord (UInt256.ofNat 1) (by omega) hframeProd
  have hmodOne : Model.FastRepresents memOne 0 n mm :=
    Exp.storeWord_frame memProd (3040 + 32 * n) 0 n mm (UInt256.ofNat 1)
      (Or.inr (by omega)) hmodProd
  have haccOne : Model.FastRepresents memOne 1024 n prodVal :=
    Exp.storeWord_frame memProd (3040 + 32 * n) 1024 n prodVal
      (UInt256.ofNat 1) (Or.inr (by omega)) haccProd
  have honeOne : Model.FastRepresents memOne 3072 n 1 := by
    have hw := Exp.write_low_limb (UInt256.ofNat 1) (by omega) honeProd honeLt
    simpa [memOne, show (UInt256.ofNat 1).toNat = 1 from by decide] using hw
  have htraceDecode := FixedExponentChainTrace.gasSteps_decode
    s memProd n bsize esize msize hn32 hactive hcode hfork hrun hnp
  have hprodLt : prodVal < mm := Model.montMul_lt hm R sqVal bM
  have htraceOutMp := sub.monpro 1024 3072 1024 (UInt256.ofNat 3833)
    (Exp.outer n bsize esize msize) memOne prodVal 1
    (by simp [Exp.outer]) (by omega) (by omega) (by omega) (by omega)
    (by omega) jumpD3833 hframeOne hmodOne haccOne honeOne hprodLt
  have htraceOut : Challenge.EvmProof.GasSteps
      (decode s memProd n bsize esize msize)
      (finish s memOut n bsize esize msize) :=
    htraceDecode.trans htraceOutMp
  have htraceFinish := FixedExponentChainTrace.gasSteps_finish
    s memOut n bsize esize msize hcode hfork hrun hnp
  have hframeOut : Exp.Frame memOut n bsize minv :=
    sub.mpFrame 1024 3072 1024 memOne (by omega) hframeOne
  have houtRep : Model.FastRepresents memOut 1024 n
      (Model.montMul mm R prodVal 1) :=
    spec.mpValue 1024 3072 1024 memOne prodVal 1
      (by omega) (by omega) (by omega) hmodOne hframeOne.minvW
      haccOne honeOne hprodLt (lt_of_lt_of_le Limbs.radix_gt_one hradix)
  have htraceReturn := Exp.gasSteps_return s memOut n bsize esize msize
    hn hn32 hmz hm32 hactive hcode hfork hrun hnp
  have htrace : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (Exp.returnedState s memOut n bsize esize msize) :=
    (((htraceSq.trans htraceProd).trans htraceOut).trans
      htraceFinish).trans htraceReturn
  have hsqForm := fixedValue_form hm hcop hbMform count
  have hprodEq := Model.mont_mul_step hm hcop hsqForm hbMform
  have hprodForm : prodVal ≡
      Precompile.bytesToNatPadded input 96 bsize ^ (2 ^ count + 1) * R
        [MOD mm] := by
    dsimp [prodVal]
    rw [hprodEq]
    exact Nat.mod_modEq _ _
  have houtEq := Model.mont_out_modPow hm hcop hprodForm
  refine Exp.handled_of_trace input
    (special s memory n bsize esize msize count) s memOut
    n bsize esize msize (Model.montMul mm R prodVal 1)
    hstack htrace hn hm32 (by omega) hbsize hesize hmsz houtRep ?_
  rw [← hmm]
  simpa [hexp] using houtEq

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentHitCorrect
