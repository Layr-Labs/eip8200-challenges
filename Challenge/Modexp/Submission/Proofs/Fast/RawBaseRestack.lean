import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.Paths.RawBase
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseStates
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

abbrev rawGuard := FullBase.rawDispatchState
abbrev rawMiss := FullBase.fallbackState

def rawHit (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3704, stack := outer n bsize esize msize, memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_rawGuard_hit (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hraw : bsize = 32 * n) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rawGuardBlock
      (rawGuard s mem n bsize esize msize) =
      some (rawHit s mem n bsize esize msize) := by
  have heq : UInt256.eq (UInt256.ofNat (32 * n)) (UInt256.ofNat bsize) =
      UInt256.ofNat 1 := by simp [UInt256.eq, hraw]
  simp (config := { maxSteps := 400000 }) [rawGuardBlock, opAt, pushAt, wfOp,
    rawGuard, FullBase.rawDispatchState, rawHit, outer, FullBase.outer, hrun, heq, isZero_ofNat_one, not_isTrue_zero,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_rawGuard_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hraw : bsize ≠ 32 * n)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rawGuardBlock
      (rawGuard s mem n bsize esize msize) =
      some (rawMiss s mem n bsize esize msize) := by
  have hnW : 32 * n < 2 ^ 256 := lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num)
  have hbW : bsize < 2 ^ 256 := lt_of_le_of_lt hb (by norm_num)
  have heq : UInt256.eq (UInt256.ofNat (32 * n)) (UInt256.ofNat bsize) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, toNat_ofNat_self hnW, toNat_ofNat_self hbW, if_neg (Ne.symm hraw)]
  simp (config := { maxSteps := 400000 }) [rawGuardBlock, opAt, pushAt, wfOp,
    rawGuard, FullBase.rawDispatchState, rawMiss, FullBase.fallbackState, outer, FullBase.outer, hrun, hcode, heq, isZero_ofNat_zero, isTrue_one,
    jumpDest3661,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_rawHit (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock rawHitBlock
      (rawHit s mem n bsize esize msize) =
      some (mpCall s (rawBaseCopy mem input n) 6144 2048 2048 (UInt256.ofNat 1755)
        (outer n bsize esize msize)) := by
  have hnW : (UInt256.ofNat (32 * n)).toNat = 32 * n :=
    toNat_ofNat_self (lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      2048 (32 * n)) = s.activeWords :=
    activeWords_fix s 2048 (32 * n) (by omega) (by omega) hact
  simp (config := { maxSteps := 800000 }) [rawHitBlock, opAt, pushAt, wfOp,
    rawHit, mpCall, rawBaseCopy, outer, hdata, hrun, hcode, hnW, hfix,
    jumpDest1939, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


def gasSteps_rawBaseChain (s : State) {n bsize mm minv : Nat}
    (sub : Subroutines s n bsize mm minv) (input mem : ByteArray)
    (esize msize rr : Nat) (hraw : bsize = 32 * n)
    (hdata : s.executionEnv.calldata = input) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hact : 298 ≤ s.activeWords.toNat) (hrrlt : rr < mm)
    (hframe : Frame mem n bsize minv) (hmod : Model.FastRepresents mem 0 n mm)
    (hrr : Model.FastRepresents mem 6144 n rr)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rawGuard s mem n bsize esize msize)
      (bDone s (sub.mpMem 6144 2048 2048 (rawBaseCopy mem input n)) n bsize esize msize) := by
  have guard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka rawGuardBlock
      (s := rawGuard s mem n bsize esize msize) hcode hfork
      (run_rawGuard_hit s mem n bsize esize msize hraw hrun) hrun hnp
  have copy := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka rawHitBlock
      (s := rawHit s mem n bsize esize msize) hcode hfork
      (run_rawHit s mem input n bsize esize msize hdata hn hn32 hact hcode hrun) hrun hnp
  have mp := sub.monpro 6144 2048 2048 (UInt256.ofNat 1755) (outer n bsize esize msize)
    (rawBaseCopy mem input n) rr (Precompile.bytesToNatPadded input 96 (32 * n))
    (by simp [outer]) (by omega) (by omega) (by omega) (by omega) (by omega) jumpD1755
    (rawBaseCopy_frame hn32 hframe)
    (rawBaseCopy_preserves mem input n 0 n mm (Or.inr (by omega)) hmod)
    (rawBaseCopy_preserves mem input n 6144 n rr (Or.inl (by omega)) hrr)
    (rawBaseCopy_represents mem input n) hrrlt
  exact ((guard.trans copy).trans mp).trans
    (gasSteps_bRejoin s (sub.mpMem 6144 2048 2048 (rawBaseCopy mem input n))
      n bsize esize msize hcode hfork hrun hnp)


end Challenge.Modexp.Submission.Proofs.Fast.Exp
