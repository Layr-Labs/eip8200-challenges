import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheKernel
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlocks
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

/-- Universal execution bridge.  It is observationally identical to the
existing MONPRO trace at the CSUB entry for every admitted limb count. -/
opaque gasSteps_toCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : ((MachineState.readWord mem (32*n-32)).toNat *
      (MachineState.readWord mem 9376).toNat+1)%2^256 = 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  by_cases hn4 : n = 4
  · subst n
    exact (gasSteps_dispatch4 s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
      (by simpa using hs32)).trans
      (CiosStackCache.Gas.kernel s (CiosStackCacheBlocks.environment s hcode hfork hrun hnp)
        CiosStackCacheBlocks.kernelBlocks mem pa pb 4 pdst ret rest hcap hact (Or.inl rfl)
        hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv)
  by_cases hn8 : n = 8
  · subst n
    exact (gasSteps_dispatch8 s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
      (by simpa using hs32)).trans
      (CiosStackCache.Gas.kernel s (CiosStackCacheBlocks.environment s hcode hfork hrun hnp)
        CiosStackCacheBlocks.kernelBlocks mem pa pb 8 pdst ret rest hcap hact (Or.inr rfl)
        hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv)
  have h32n : 32 * n < 2 ^ 256 := by omega
  have h128 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 128 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 128 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn4 (by omega)
  have h256 : MachineState.readWord mem 9344 ≠ UInt256.ofNat 256 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 256 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn8 (by omega)
  exact (gasSteps_dispatchFallback s mem pa pb pdst ret rest (by omega) hrun hcode
    hfork hnp hact h128 h256).trans
    (gasSteps_monpro s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact
      hn hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml)

/-- The universal dispatcher followed by the unchanged CSUB tail. -/
opaque gasSteps_monproCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : ((MachineState.readWord mem (32*n-32)).toNat *
      (MachineState.readWord mem 9376).toNat+1)%2^256 = 0)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (rowsMem (mpZeroed s mem n) pa pb n n) 8224).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (rowsMem (mpZeroed s mem n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_toCsub s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv).trans
    (Csub.gasSteps_csub s (rowsMem (mpZeroed s mem n) pa pb n n) n pdst ret rest
      (by omega) hcode hfork hrun hnp hact hn hn32 hjump
      ((readWord_monpro_preserved s mem pa pb n n 9408 hn32 (by omega)).trans hml)
      ((readWord_monpro_preserved s mem pa pb n n 9440 hn32 (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint (rowsMem (mpZeroed s mem n) pa pb n n) n 9344
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_monpro_preserved s mem pa pb n n 9344 hn32 (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint (rowsMem (mpZeroed s mem n) pa pb n n) n
          8224 (by omega) (Or.inr (by omega)) n (Nat.le_refl n)]
        exact htn))

/-- The full cached CIOS-dispatched MONPRO call with the existing arithmetic theorem
discharging the accumulator bound. -/
opaque gasSteps_monproFull (s : State) (mem : ByteArray) (pa pb p : Nat)
    (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 9472)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) (p + 2)
        pdst ret rest) :=
  gasSteps_monproCsub s mem pa pb (p + 2) pdst ret rest (by omega) hrun hcode hfork hnp
    hact (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hminv hjump
    hdstFit
    (Monpro.monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham
      hmpos hminv)

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheFull
