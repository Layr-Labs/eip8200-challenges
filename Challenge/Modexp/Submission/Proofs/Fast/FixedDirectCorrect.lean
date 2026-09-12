import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectRouteCorrect
import Challenge.Modexp.Submission.Proofs.Fast.GenericExponentFromHead

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Composition of fixed and generic exponent routes

The concrete fixed-chain proof supplies `Route.hit`. The unchanged exponent
proof supplies `generic` from the exact `ebHead` state reconstructed on a miss.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Prefix a packaged fixed/generic continuation by a certified trace. -/
theorem prepend {input : ByteArray} {start middle : State}
    (head : Challenge.EvmProof.GasSteps start middle)
    (suffix : FixedExponentRoute.Handled input middle) :
    FixedExponentRoute.Handled input start := by
  rcases suffix with ⟨final, ⟨tail⟩, hdone, hresult⟩
  exact ⟨final, ⟨head.trans tail⟩, hdone, hresult⟩

/-- Route-aware replacement for the outer case split at `Exp.bDone`.

The miss continuation is the body of the old generic branch of
`Exp.handled_of_bDone`, factored to start at `Exp.ebHead`. The two hit cases
are discharged by the ported PR145 fixed-square and final-product proof.
-/
def handled_of_bDone (route : FixedExponentRoute.Route s mem input
      n bsize esize msize)
    (generic : FixedExponentRoute.Handled input
      (FixedExponentRoute.missState s mem n bsize esize msize)) :
    FixedExponentRoute.Handled input
      (Exp.bDone s mem n bsize esize msize) := by
  by_cases hmatch : FixedExponentRoute.Matches input bsize esize
  · exact prepend route.enter (route.hit hmatch)
  · exact prepend (route.enter.trans (route.miss hmatch)) generic

/-- Route-aware replacement for the outer case split at the dispatcher entry.

`run_rrDone_skip` and `run_shiftDone` now jump straight to pc 3215, so their
traces end at `entryState` rather than `bDone`; the `enter` trampoline step is
already consumed and must not be prepended again. -/
def handled_of_entryState (route : FixedExponentRoute.Route s mem input
      n bsize esize msize)
    (generic : FixedExponentRoute.Handled input
      (FixedExponentRoute.missState s mem n bsize esize msize)) :
    FixedExponentRoute.Handled input
      (FixedExponentRoute.entryState s mem n bsize esize msize) := by
  by_cases hmatch : FixedExponentRoute.Matches input bsize esize
  · exact route.hit hmatch
  · exact prepend (route.miss hmatch) generic

/-- Adapter expected by the `bsize = 0` RR-skip and the shift-reduce hit
continuations, whose traces now land on the dispatcher entry directly. -/
abbrev EntryContinuation (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : Prop :=
  FixedExponentRoute.Handled input
    (FixedExponentRoute.entryState s mem n bsize esize msize)

/-- Exact adapter expected by the c64 full-base hit and generic Horner
continuations. It makes the cc628 layer replace only the continuation beginning
at `bDone`; all base-conversion proofs remain independent. -/
abbrev BDoneContinuation (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : Prop :=
  FixedExponentRoute.Handled input (Exp.bDone s mem n bsize esize msize)

/-- Complete generic-miss adapter using the factored inherited exponent proof.

Only the fixed hit remains abstract in `route`. All nonmatching exponents are
closed by `handled_of_ebHead`, which is the old `Exp.handled_of_bDone` body
with its replaced initialization block removed. -/
def handled_of_bDoneWithGeneric
    (route : FixedExponentRoute.Route s mem input n bsize esize msize)
    (mm minv bM : Nat)
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
    BDoneContinuation input s mem n bsize esize msize :=
  handled_of_bDone route
    (handled_of_ebHead input s mem n bsize esize msize mm minv bM sub spec
      hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize
      hesize hmsz hmm hodd hradix hbMlt hbMform hframe hEb)

/-- Fully instantiated replacement for the inherited `handled_of_bDone`.

The pre-copy representations are kept explicit because the fixed hit starts
before the generic miss performs its R1-to-ACC copy. -/
def handled_of_bDoneConcrete (input : ByteArray) (s : State) (mem : ByteArray)
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
    (hmod : Model.FastRepresents mem 0 n mm)
    (hbase : Model.FastRepresents mem 2048 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents mem 3072 n one)
    (hEb : Exp.EbInv (Exp.mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (Exp.expAcc mm (Limbs.radix ^ n) bM (Exp.expBits input bsize) 0))
    (hraw : ∃ rawBase, Model.FastRepresents mem 1024 n rawBase ∧
      rawBase ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm]) :
    BDoneContinuation input s mem n bsize esize msize :=
  handled_of_bDoneWithGeneric
    (FixedDirectRouteCorrect.route input s mem n bsize esize msize mm minv bM
      sub spec hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32
      hbsize hesize hmsz hmm hodd hradix hbMlt hbMform hframe hmod hbase hone hraw)
    mm minv bM sub spec hcode hfork hrun hnp hdata hstack hact hn hn32 hb he
    hmz hm32 hbsize hesize hmsz hmm hodd hradix hbMlt hbMform hframe hEb

/-- Fully instantiated adapter for traces that land on the dispatcher entry
at pc 3215 directly (the `bsize = 0` RR-skip and the shift-reduce hit). -/
def handled_of_entryStateConcrete (input : ByteArray) (s : State) (mem : ByteArray)
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
    (hmod : Model.FastRepresents mem 0 n mm)
    (hbase : Model.FastRepresents mem 2048 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents mem 3072 n one)
    (hEb : Exp.EbInv (Exp.mcopyMem mem 1024 4096 (32 * n)) n mm bM
      (Exp.expAcc mm (Limbs.radix ^ n) bM (Exp.expBits input bsize) 0))
    (hraw : ∃ rawBase, Model.FastRepresents mem 1024 n rawBase ∧
      rawBase ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm]) :
    EntryContinuation input s mem n bsize esize msize :=
  handled_of_entryState
    (FixedDirectRouteCorrect.route input s mem n bsize esize msize mm minv bM
      sub spec hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32
      hbsize hesize hmsz hmm hodd hradix hbMlt hbMform hframe hmod hbase hone hraw)
    (handled_of_ebHead input s mem n bsize esize msize mm minv bM sub spec
      hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize
      hesize hmsz hmm hodd hradix hbMlt hbMform hframe hEb)

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectCorrect
