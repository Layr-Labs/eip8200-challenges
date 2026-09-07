import Challenge.Modexp.Submission.Proofs.Fast.FullBaseFallbackCore
import Challenge.Modexp.Submission.Proofs.Fast.FullBasePaths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Concrete located trace for the relocated full-base fallback

The semantic calculation is supplied by `FullBaseFallbackCore`; this module
only checks that the same 24 instructions occur at the submitted locations
and lifts the resulting execution to `GasSteps`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseFallbackTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast

open Challenge.Modexp.Submission.Proofs.Fast.FullBase

private def fallbackCountPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2390 .JUMPDEST, opAt 2391 (.Dup ⟨2, by decide⟩),
   pushAt 2392 1 31, opAt 2393 .ADD, pushAt 2394 1 5, opAt 2395 .SHR]
private def fallbackWordPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2396 (.Dup ⟨3, by decide⟩), opAt 2397 (.Dup ⟨1, by decide⟩),
   pushAt 2398 1 5, opAt 2399 .SHL, opAt 2400 .SUB, pushAt 2401 1 3,
   opAt 2402 .SHL, pushAt 2403 1 96, opAt 2404 .CALLDATALOAD,
   opAt 2405 (.Swap ⟨0, by decide⟩), opAt 2406 .SHR]
private def fallbackStorePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2407 (.Dup ⟨2, by decide⟩), pushAt 2408 2 992, opAt 2409 .ADD,
   opAt 2410 .MSTORE, pushAt 2411 1 1, pushAt 2412 2 1668, opAt 2413 .JUMP]

private theorem shr_ofNat (value shift : Nat) (hv : value < 2 ^ 256)
    (hs : shift < 256) :
    UInt256.shiftRight (UInt256.ofNat value) (UInt256.ofNat shift) =
      UInt256.ofNat (value / 2 ^ shift) := by
  simpa only [Nat.shiftRight_eq_div_pow] using
    Challenge.EvmProof.Word.shiftRight_ofNat hv hs

private theorem mod_word_self {a : Nat} (ha : a < 2 ^ 256) :
    a % 2 ^ 256 = a := Nat.mod_eq_of_lt ha

private theorem activeWords_fix (s : State) (offset size : Nat) (hsz : size ≠ 0)
    (hend : offset + size ≤ 9536) (hactive : 298 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat offset size) =
      s.activeWords := by
  have hnat : MachineState.activeWordsAfter s.activeWords.toNat offset size =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, hsz, if_false]
    apply Nat.max_eq_left
    omega
  rw [hnat]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm


set_option linter.unusedSimpArgs false in
theorem run_fallback (s : State) (mem input : ByteArray)
    (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hact : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFullBaseFallback
      (FullBase.fallbackState s mem n bsize esize msize) =
      some (FullBase.legacyLoopState s
        (FullBase.storeWord mem (992 + 32 * n)
          (UInt256.ofNat (FullBase.topLimbOf input bsize)))
        n bsize esize msize (FullBase.pbOf bsize) 1) := by
  have hjump : Decode.isValidJumpDest s.executionEnv.code 1668 = true := by
    simpa [hcode] using jumpDest1668
  have hpb1 : 1 ≤ pbOf bsize := by unfold pbOf; omega
  have hpbLe : pbOf bsize ≤ 32 := by unfold pbOf; omega
  have hpbBig : bsize ≤ 32 * pbOf bsize := by unfold pbOf; omega
  have hpbLow : 32 * (pbOf bsize - 1) < bsize := by unfold pbOf; omega
  have htw1 : 0 < topWidth bsize := by unfold topWidth; omega
  have htw32 : topWidth bsize ≤ 32 := by unfold topWidth; omega
  have hshiftEq : 32 * pbOf bsize - bsize = 32 - topWidth bsize := by
    unfold topWidth; omega
  have hshr : UInt256.shiftRight (UInt256.ofNat (31 + bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat ((31 + bsize) / 2 ^ 5) :=
    shr_ofNat _ 5 (Nat.lt_of_le_of_lt (show 31 + bsize ≤ 1055 by omega) (by norm_num))
      (by omega)
  have hpb : (31 + bsize) / 32 = pbOf bsize := rfl
  have hshl : UInt256.shiftLeft (UInt256.ofNat (pbOf bsize)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * pbOf bsize) := by
    have he : pbOf bsize * 2 ^ 5 = 32 * pbOf bsize := by ring
    have h1 : pbOf bsize < 2 ^ 256 := Nat.lt_of_le_of_lt hpbLe (by norm_num)
    have h2 : (5 : Nat) < 256 := by omega
    have h3 : pbOf bsize * 2 ^ 5 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsub : UInt256.ofNat (32 * pbOf bsize) - UInt256.ofNat bsize =
      UInt256.ofNat (32 * pbOf bsize - bsize) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hpbBig
      (Nat.lt_of_le_of_lt (show 32 * pbOf bsize ≤ 1024 by omega) (by norm_num))
  have hshl2 : UInt256.shiftLeft (UInt256.ofNat (32 * pbOf bsize - bsize))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - topWidth bsize) * 8) := by
    have he : (32 * pbOf bsize - bsize) * 2 ^ 3 = (32 - topWidth bsize) * 8 := by
      rw [← hshiftEq]; ring
    have h1 : 32 * pbOf bsize - bsize < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (show 32 * pbOf bsize - bsize ≤ 1024 by omega) (by norm_num)
    have h2 : (3 : Nat) < 256 := by omega
    have h3 : (32 * pbOf bsize - bsize) * 2 ^ 3 < 2 ^ 256 := by
      rw [he]
      exact Nat.lt_of_le_of_lt (show (32 - topWidth bsize) * 8 ≤ 256 by omega)
        (by norm_num)
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat h1 h2 h3]
    exact congrArg UInt256.ofNat he
  have hsr : UInt256.shiftRight (MachineState.readWord input 96)
      (UInt256.ofNat ((32 - topWidth bsize) * 8)) =
      UInt256.ofNat (topLimbOf input bsize) :=
    Challenge.EvmProof.Bytes.shiftRight_readWord input 96 (topWidth bsize) htw1 htw32
  have hmod : (992 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 992 + 32 * n := mod_word_self (by
        exact Nat.lt_of_le_of_lt (show 992 + 32 * n ≤ 2016 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (992 + 32 * n) 32) = s.activeWords :=
    activeWords_fix s (992 + 32 * n) 32 (by omega) (by omega) hact
  have hcount : Challenge.EvmProof.Stepper.runLocatedBlock fallbackCountPath
      (fallbackState s mem n bsize esize msize) =
      some (fallbackCountState s mem n bsize esize msize) := by
    simp [fallbackCountPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, opAt, pushAt, wfOp,
      hcode, hrun, fullBasePC, jumpDest1668,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Stepper.runInstr,
      fallbackState, fallbackCountState, outer, hshr, hpb,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hword : Challenge.EvmProof.Stepper.runLocatedBlock fallbackWordPath
      (fallbackCountState s mem n bsize esize msize) =
      some (fallbackWordState s mem input n bsize esize msize) := by
    simp [fallbackWordPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, opAt, pushAt, wfOp,
      hcode, hrun, fullBasePC, jumpDest1668,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Stepper.runInstr,
      fallbackCountState, fallbackWordState, outer, hdata, hshl, hsub, hshl2, hsr,
      List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hstore : Challenge.EvmProof.Stepper.runLocatedBlock fallbackStorePath
      (fallbackWordState s mem input n bsize esize msize) =
      some (legacyLoopState s (storeWord mem (992 + 32 * n)
        (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize
        (pbOf bsize) 1) := by
    simp [fallbackStorePath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, opAt, pushAt, wfOp,
      hcode, hrun, fullBasePC, jumpDest1668,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Stepper.runInstr,
      fallbackWordState, legacyLoopState, storeWord, outer, hmod, hfix, hjump,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hrest := Challenge.EvmProof.Stepper.runLocatedBlock_append
    fallbackWordPath fallbackStorePath
    (fallbackCountState s mem n bsize esize msize)
    (fallbackWordState s mem input n bsize esize msize)
    (legacyLoopState s (storeWord mem (992 + 32 * n)
      (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize (pbOf bsize) 1)
    hword hrun hstore
  have hall := Challenge.EvmProof.Stepper.runLocatedBlock_append fallbackCountPath
    (fallbackWordPath ++ fallbackStorePath)
    (fallbackState s mem n bsize esize msize)
    (fallbackCountState s mem n bsize esize msize)
    (legacyLoopState s (storeWord mem (992 + 32 * n)
      (UInt256.ofNat (topLimbOf input bsize))) n bsize esize msize (pbOf bsize) 1)
    hcount hrun hrest
  have hprogram : blkFullBaseFallback =
      fallbackCountPath ++ (fallbackWordPath ++ fallbackStorePath) := rfl
  exact (congrArg
    (fun program => Challenge.EvmProof.Stepper.runLocatedBlock program
      (fallbackState s mem n bsize esize msize)) hprogram).trans hall

def gasSteps_fallback (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FullBase.fallbackState s memory n bsize esize msize)
      (FullBase.legacyLoopState s
        (FullBase.storeWord memory (992 + 32 * n)
          (UInt256.ofNat (FullBase.topLimbOf input bsize)))
        n bsize esize msize (FullBase.pbOf bsize) 1) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFullBaseFallback hcode hfork
      (run_fallback s memory input n bsize esize msize hdata hn32 hb hb0
        hactive hcode hrun)
      hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseFallbackTrace
