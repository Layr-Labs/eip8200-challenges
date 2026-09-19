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

theorem handled_of_terminal_trace (input : ByteArray) (entry s : State) (mem : ByteArray)
    (rest : List UInt256) (n bsize esize msize result : Nat)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (htrace : Challenge.EvmProof.GasSteps entry
      (GenericReturnAdapter.terminalOutput s mem rest))
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm32 : msize ≤ 32 * n) (hmpos : 0 < msize)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 256 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    FixedExponentRoute.Handled input entry := by
  have hmodlt : Challenge.Modexp.modulusSize input < 2 ^ 256 := by
    have hmodle : Challenge.Modexp.modulusSize input ≤ 256 := by omega
    have hp : (256 : Nat) < 2 ^ 256 := by norm_num
    omega
  have hcalldata : (MachineState.readWord s.executionEnv.calldata 64).toNat = msize := by
    calc
      (MachineState.readWord s.executionEnv.calldata 64).toNat =
          (UInt256.ofNat (Challenge.Modexp.modulusSize input)).toNat := by
            rw [hdata]
            rfl
      _ = Challenge.Modexp.modulusSize input := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
      _ = msize := hmsz.symm
  have hspec := Exp.returned_eq_spec s mem input n bsize esize msize result hn hm32 hmpos
    hbsize hesize hmsz hrep hres
  have hreturn :
      (GenericReturnAdapter.terminalOutput s mem rest).hReturn =
        Challenge.Modexp.spec input := by
    change MachineState.readPadded mem 256
      (MachineState.readWord s.executionEnv.calldata 64).toNat = _
    rw [hcalldata]
    simpa [Exp.returnedState, hfull] using hspec
  have hdone :
      (GenericReturnAdapter.terminalOutput s mem rest).isDone = true := by
    simp [State.isDone, State.isHalted, State.isRunning,
      GenericReturnAdapter.terminalOutput, GenericReturnAdapter.atState, hstack]
  refine ⟨GenericReturnAdapter.terminalOutput s mem rest, ⟨htrace⟩, hdone, ?_⟩
  rw [State.toResult_returned _ (by rfl)]
  exact hreturn

/-- Exact correctness for either fixed chain, with arbitrary valid operands. -/
theorem handled_of_fixed (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv bM rawBase count : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input)
    (hstack : s.callStack = []) (hactive : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmz : 32 < msize)
    (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
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
    (hrawLt : rawBase < mm)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    FixedExponentRoute.Handled input
      (special s memory n bsize esize msize count) := by
  let ch := chain_of_fixed s sub spec memory esize msize count bM rawBase
    hm hn hn32 hcount hcount16 hbMlt hactive
    hframe hmod hbase hrawAcc hrawLt hone hcode hfork hrun hnp
  let sqVal := fixedDirectValue mm (Limbs.radix ^ n) bM count
  let prodVal := Model.montMul mm (Limbs.radix ^ n) sqVal rawBase
  let memOut := ch.mem
  have houtRep : Model.FastRepresents memOut 256 n prodVal := ch.value
  have houtEq : prodVal =
      Precompile.bytesToNatPadded input 96 bsize ^ (2 ^ count + 1) % mm :=
    directProduct_value hm hcop hbMform hrawForm
  have hres : prodVal = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize) := by
    rw [← hmm, Model.modPow_eq_pow_mod hm, hexp]
    exact houtEq
  by_cases hfast : (n = 4 ∨ n = 8) ∧ minv ≠ 1
  · have htrace : Challenge.EvmProof.GasSteps
        (special s memory n bsize esize msize count)
        (GenericReturnAdapter.terminalOutput s memOut
          (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
      simpa only [chainFinal, if_pos hfast] using ch.trace
    exact handled_of_terminal_trace input
      (special s memory n bsize esize msize count) s memOut
      (UInt256.ofNat count :: Exp.outer n bsize esize msize)
      n bsize esize msize prodVal hdata hstack htrace hn hn32 hm32 (by omega)
      hfull hbsize hesize hmsz houtRep hres
  · have htrace : Challenge.EvmProof.GasSteps
        (special s memory n bsize esize msize count)
        (Exp.finHead s memOut n bsize esize msize) := by
      simpa only [chainFinal, if_neg hfast] using ch.trace
    have htraceReturn := Exp.gasSteps_return s memOut n bsize esize msize
      hn hn32 hmz hm32 hfull hactive hcode hfork hrun hnp
    exact Exp.handled_of_trace input
      (special s memory n bsize esize msize count) s memOut
      n bsize esize msize prodVal hstack (htrace.trans htraceReturn)
      hn hm32 (by omega) hbsize hesize hmsz houtRep hres

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect

#print axioms Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect.handled_of_fixed
