import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastP6
import Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleSubmission.Global.Fast.Return
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option linter.unusedSimpArgs false in
/-- `CycleSubmission.Global.Fast.blk1333` (pc 774..779): `RETURN(256, msize)`. -/
theorem run_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 32 < msize) (_hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hact : 88 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock CycleSubmission.Global.Fast.blk1333
      (finHead s mem n bsize esize msize) =
      some (returnedState s mem n bsize esize msize) := by
  have hoff : 256 + 32 * n - msize = 256 := by omega
  have hmodSz : msize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = msize :=
    mod_word_self (Nat.lt_of_le_of_lt (show msize ≤ 256 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      256 msize) = s.activeWords :=
    activeWords_fix s 256 msize (by omega) (by omega) hact
  simp (config := { maxSteps := 600000 }) [CycleSubmission.Global.Fast.blk1333, CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt, CycleSubmission.Global.Fast.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    finHead, returnedState, outer, hrun, hoff, hmodSz, hfix,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ### Gas traces for the exponent blocks -/

def gasSteps_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (finHead s mem n bsize esize msize)
      (returnedState s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka CycleSubmission.Global.Fast.blk1333 hcode hfork
      (run_return s mem n bsize esize msize hn hn32 hm hm32 hfull hact hrun) hrun hnp


end CycleSubmission.Global.Fast.Return
