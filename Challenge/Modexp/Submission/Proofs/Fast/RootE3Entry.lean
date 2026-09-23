import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectRouteCorrect
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect
import Challenge.Modexp.Submission.Proofs.Fast.Model

set_option warningAsError true
set_option maxHeartbeats 2000000

namespace RootE3Scale
open Challenge.Modexp.Submission.Proofs.Fast.Model

/-- Two existing Montgomery products evaluate a cube with asymmetric input scales. -/
theorem asymmetric_cube {m R a S T X Y : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime R m) (hx : X ≡ a * S [MOD m])
    (hy : Y ≡ a * T [MOD m]) (hscale : S * S * T = R * R) :
    montMul m R (montMul m R X X) Y = a ^ 3 % m := by
  have hfirst := montMul_mul_R_modEq hm hcop X X
  have hsecond := montMul_mul_R_modEq hm hcop (montMul m R X X) Y
  have htotal : montMul m R (montMul m R X X) Y * (R * R) ≡
      a ^ 3 * (R * R) [MOD m] := by
    calc
      montMul m R (montMul m R X X) Y * (R * R)
          ≡ (montMul m R X X * Y) * R [MOD m] := by
            simpa only [Nat.mul_assoc] using hsecond.mul_right R
      _ = (montMul m R X X * R) * Y := by ring
      _ ≡ (X * X) * Y [MOD m] := hfirst.mul_right Y
      _ ≡ (a * S) * (a * S) * (a * T) [MOD m] := (hx.mul hx).mul hy
      _ = a ^ 3 * (R * R) := by rw [← hscale]; ring
  have hresult : montMul m R (montMul m R X X) Y ≡ a ^ 3 [MOD m] :=
    htotal.cancel_right_of_coprime (Nat.Coprime.mul_left hcop hcop).symm
  exact (Nat.mod_eq_of_lt (montMul_lt hm _ _ _)).symm.trans hresult

theorem quarter_scale (B k : Nat) :
    B ^ (3 * k) * B ^ (3 * k) * B ^ (2 * k) = B ^ (4 * k) * B ^ (4 * k) := by
  simp only [← Nat.pow_add]
  congr 1
  omega

theorem asymmetric_cube_quarters {m a B k X Y : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime (B ^ (4 * k)) m)
    (hx : X ≡ a * B ^ (3 * k) [MOD m])
    (hy : Y ≡ a * B ^ (2 * k) [MOD m]) :
    montMul m (B ^ (4 * k)) (montMul m (B ^ (4 * k)) X X) Y = a ^ 3 % m :=
  asymmetric_cube hm hcop hx hy (quarter_scale B k)

#print axioms asymmetric_cube
#print axioms asymmetric_cube_quarters
end RootE3Scale

namespace RootE3Hit
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectChainCorrect
open Challenge.Modexp.Submission.Proofs.Bytecode
theorem handled_of_asymmetric_three (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv bM rawBase S T : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : s.callStack = []) (hactive : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hn48 : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    (hmz : 32 < msize)
    (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hm : 0 < mm) (hcop : Nat.Coprime (Limbs.radix ^ n) mm) (_hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize * S [MOD mm])
    (hrawForm : rawBase ≡ Precompile.bytesToNatPadded input 96 bsize * T [MOD mm])
    (hscale : S * S * T = (Limbs.radix ^ n) * (Limbs.radix ^ n))
    (hexp : Precompile.bytesToNatPadded input (96 + bsize) esize =
      3)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2112 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hrawLt : rawBase < mm)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    FixedExponentRoute.Handled input
      (special s memory n bsize esize msize 1) := by
  let ch := chain_of_fixed s sub spec memory esize msize 1 bM rawBase
    ⟨hn48, hminv1⟩ hm hn hn32 (by omega) (by omega) hbMlt hactive
    hframe hmod hbase hrawAcc hrawLt hone hcode hfork hrun hnp
  let sqVal := fixedDirectValue mm (Limbs.radix ^ n) bM 1
  let prodVal := Model.montMul mm (Limbs.radix ^ n) sqVal rawBase
  let memOut := ch.mem
  have houtRep : Model.FastRepresents memOut 256 n prodVal := ch.value
  have htraceReturn := Exp.gasSteps_return s memOut n bsize esize msize
    hn hn32 hmz hm32 hfull hactive hcode hfork hrun hnp
  have htrace : Challenge.EvmProof.GasSteps
      (special s memory n bsize esize msize 1)
      (Exp.returnedState s memOut n bsize esize msize) :=
    ch.trace.trans htraceReturn
  have houtEq : prodVal =
      Precompile.bytesToNatPadded input 96 bsize ^ 3 % mm :=
    RootE3Scale.asymmetric_cube hm hcop hbMform hrawForm hscale
  refine Exp.handled_of_trace input
    (special s memory n bsize esize msize 1) s memOut
    n bsize esize msize prodVal hstack htrace hn hm32 (by omega)
    hbsize hesize hmsz houtRep ?_
  rw [← hmm, Model.modPow_eq_pow_mod hm, hexp]
  exact houtEq


theorem handled_of_entry_asymmetric_three (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize msize mm minv bM rawBase S T : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hb : bsize ≤ 1024)
    (hstack : s.callStack = []) (hactive : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hn48 : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    (hmz : 32 < msize)
    (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : 1 = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + 1) msize)
    (hm : 0 < mm) (hcop : Nat.Coprime (Limbs.radix ^ n) mm) (_hradix : Limbs.radix ≤ mm)
    (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize * S [MOD mm])
    (hrawForm : rawBase ≡ Precompile.bytesToNatPadded input 96 bsize * T [MOD mm])
    (hscale : S * S * T = (Limbs.radix ^ n) * (Limbs.radix ^ n))
    (hexp : Precompile.bytesToNatPadded input (96 + bsize) 1 =
      3)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2112 n bM)
    (hrawAcc : Model.FastRepresents memory 256 n rawBase)
    (hrawLt : rawBase < mm)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    FixedExponentRoute.Handled input
      (FixedExponentRoute.entryState s memory n bsize 1 msize) := by
  have htoSpecial :=
    ((FixedDirectDispatchTrace.gasSteps_entry_other s memory
      n bsize 1 msize (by decide) (by omega) hcode hfork hrun hnp).trans
    (FixedDirectDispatchTrace.gasSteps_oneWidth_hit s memory
      n bsize msize hcode hfork hrun hnp)).trans
    (FixedDirectValueTrace.gasSteps_checkThree_hit s memory input
      n bsize msize hb hexp hdata hactive hframe.eoff hcode hfork hrun hnp)
  have hfixed := handled_of_asymmetric_three input s memory n bsize 1 msize mm minv
    bM rawBase S T sub spec hcode hfork hrun hnp hstack hactive hn hn32 hn48 hminv1 hmz hm32 hfull
    hbsize hesize hmsz hmm hm hcop _hradix hbMlt hbMform hrawForm hscale hexp
    hframe hmod hbase hrawAcc hrawLt hone
  rcases hfixed with ⟨final, ⟨tail⟩, hdone, hresult⟩
  exact ⟨final, ⟨htoSpecial.trans tail⟩, hdone, hresult⟩

#print axioms handled_of_asymmetric_three
#print axioms handled_of_entry_asymmetric_three
end RootE3Hit
