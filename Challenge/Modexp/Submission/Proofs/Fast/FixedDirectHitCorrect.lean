import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Correctness of a direct fixed-exponent hit

The retained normal-domain ACC supplies the last factor of the power. Its
mixed-domain product with squared Montgomery BASE needs no separate decode.
Which of the two square chains ran (the in-kernel loop for `n ∈ {4, 8}`, the
caller's loop otherwise) is immaterial here: both deliver a
`FixedDirectChainCorrect.Chain`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Exact correctness for either fixed chain, with arbitrary valid operands. -/
theorem handled_of_fixed (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv bM rawBase count : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
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
    (hm : 0 < mm) (hcop : Nat.Coprime (Limbs.radix ^ n) mm) (_hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize *
      Limbs.radix ^ n [MOD mm])
    (hrawForm : rawBase ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm])
    (hcount : 1 ≤ count) (hcount16 : count ≤ 16)
    (hexp : Precompile.bytesToNatPadded input (96 + bsize) esize =
      2 ^ count + 1)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 512 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    FixedExponentRoute.Handled input
      (special s memory n bsize esize msize count) := by
  let ch := chain_of_fixed s sub memory esize msize count bM rawBase
    hm hn hn32 hcount hcount16 hbMlt hactive
    hframe hmod hbase hrawAcc hone hcode hfork hrun hnp
  let memSq := ch.mem
  let sqVal := fixedDirectValue mm (Limbs.radix ^ n) bM count
  let prodVal := Model.montMul mm (Limbs.radix ^ n) sqVal rawBase
  let memOut := sub.mpMem 512 256 256 memSq
  have hsqInv : Inv memSq n mm rawBase sqVal := ch.inv
  have hframeSq : Exp.Frame memSq n bsize minv := ch.frame
  have hsqLt : sqVal < mm := fixedDirectValue_lt hm hbMlt count
  have htraceProdCall := FixedDirectChainTrace.gasSteps_product
    s memSq n bsize esize msize ch.cnt hcode hfork hrun hnp
  have htraceProdMp := sub.monpro 512 256 256 (UInt256.ofNat 1571)
    (Exp.outer n bsize esize msize) memSq sqVal rawBase
    (by simp [Exp.outer]) (by omega) (by omega) (by omega) (by omega)
    (by omega) jumpD3997 hframeSq hsqInv.modulus hsqInv.squareBase
    hsqInv.rawAcc hsqLt
  have htraceProd : Challenge.EvmProof.GasSteps
      (product s memSq n bsize esize msize ch.cnt)
      (Exp.finHead s memOut n bsize esize msize) :=
    htraceProdCall.trans htraceProdMp
  have houtRep : Model.FastRepresents memOut 256 n prodVal :=
    spec.mpValueRaw 512 256 256 memSq sqVal rawBase
      (by omega) (by omega) (by omega) hsqInv.modulus hframeSq.minvW
      hsqInv.squareBase hsqInv.rawAcc hsqLt
  have htraceReturn := Exp.gasSteps_return s memOut n bsize esize msize
    hn hn32 hmz hm32 hactive hcode hfork hrun hnp
  have htrace : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize count)
      (Exp.returnedState s memOut n bsize esize msize) :=
    (ch.trace.trans htraceProd).trans htraceReturn
  have houtEq : prodVal =
      Precompile.bytesToNatPadded input 96 bsize ^ (2 ^ count + 1) % mm :=
    directProduct_value hm hcop hbMform hrawForm
  refine Exp.handled_of_trace input
    (special s memory n bsize esize msize count) s memOut
    n bsize esize msize prodVal hstack htrace hn hm32 (by omega)
    hbsize hesize hmsz houtRep ?_
  rw [← hmm, Model.modPow_eq_pow_mod hm, hexp]
  exact houtEq

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect

#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect.handled_of_fixed
