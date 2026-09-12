import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedFour
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedEight

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult

/-- Every other width: `mul entry` → `common` fallback → the generic `MONPRO` (pc 1667). -/
opaque gasSteps_fallback (E : EntryLemmas) (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 5376)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 5248 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 5344 = UInt256.ofNat (4128 + 32 * n))
    (hml : MachineState.readWord mem 5312 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) (hn4 : n ≠ 4) (hn8 : n ≠ 8) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  have h32n : 32 * n < 2 ^ 256 := by omega
  have h128 : MachineState.readWord mem 5248 ≠ UInt256.ofNat 128 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 128 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn4 (by omega)
  have h256 : MachineState.readWord mem 5248 ≠ UInt256.ofNat 256 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 256 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn8 (by omega)
  have hf := ((E.gasSteps_mulEntry s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp).trans
    (E.gasSteps_commonFallback s mem (UInt256.ofNat 4029) pa pb pdst ret rest (by omega) hrun
      hcode hfork hnp hact h128 h256)).trans
    (gasSteps_monpro s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact
      hn hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml)
  simpa only [selectedRows, if_neg (show ¬(n=4 ∨ n=8) by simp [hn4, hn8])] using hf

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
