import Challenge.Modexp.Submission.Proofs.Fast.Cios2Rows

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Universal CIOS2-to-MONPRO bridge

Widths four and eight execute the specialized CIOS2 schedules.  Every other
width takes the dispatcher's unchanged jump to the original MONPRO entry.
Both arms end in the same existing `rowsMem` model at the common CSUB entry.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Full

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Entry
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Rows

def gasSteps_rowsFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 4) pa pb 4 0 pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) := by
  have hs32z : MachineState.readWord (mpZeroed s mem 4) 9344 =
      UInt256.ofNat (32 * 4) :=
    (readWord_mpZeroed s mem 4 9344 (by decide) (by omega)).trans hs32
  have htlz : MachineState.readWord (mpZeroed s mem 4) 9440 =
      UInt256.ofNat (8224 + 32 * 4) :=
    (readWord_mpZeroed s mem 4 9440 (by decide) (by omega)).trans htl
  have hmlz : MachineState.readWord (mpZeroed s mem 4) 9408 =
      UInt256.ofNat (32 * 4 - 32) :=
    (readWord_mpZeroed s mem 4 9408 (by decide) (by omega)).trans hml
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsMem (mpZeroed s mem 4) pa pb 4 i)
      pa pb 4 i pdst ret rest) 3 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowFourNext s (rowsMem (mpZeroed s mem 4) pa pb 4 i) pa pb i
      pdst ret rest hcap hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9344 (by decide) (by omega)
        i).trans hs32z)
      ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9440 (by decide) (by omega)
        i).trans htlz)
      ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9408 (by decide) (by omega)
        i).trans hmlz)
  · simpa only [rowsMem] using
      gasSteps_rowFourLast s (rowsMem (mpZeroed s mem 4) pa pb 4 3) pa pb 3
        pdst ret rest hcap hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb
        hpbFit
        ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9344 (by decide) (by omega)
          3).trans hs32z)
        ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9440 (by decide) (by omega)
          3).trans htlz)
        ((readWord_rowsMem (mpZeroed s mem 4) pa pb 4 9408 (by decide) (by omega)
          3).trans hmlz)

def gasSteps_rowsEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 8) pa pb 8 0 pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  have hs32z : MachineState.readWord (mpZeroed s mem 8) 9344 =
      UInt256.ofNat (32 * 8) :=
    (readWord_mpZeroed s mem 8 9344 (by decide) (by omega)).trans hs32
  have htlz : MachineState.readWord (mpZeroed s mem 8) 9440 =
      UInt256.ofNat (8224 + 32 * 8) :=
    (readWord_mpZeroed s mem 8 9440 (by decide) (by omega)).trans htl
  have hmlz : MachineState.readWord (mpZeroed s mem 8) 9408 =
      UInt256.ofNat (32 * 8 - 32) :=
    (readWord_mpZeroed s mem 8 9408 (by decide) (by omega)).trans hml
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsMem (mpZeroed s mem 8) pa pb 8 i)
      pa pb 8 i pdst ret rest) 7 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowEightNext s (rowsMem (mpZeroed s mem 8) pa pb 8 i) pa pb i
      pdst ret rest hcap hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9344 (by decide) (by omega)
        i).trans hs32z)
      ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9440 (by decide) (by omega)
        i).trans htlz)
      ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9408 (by decide) (by omega)
        i).trans hmlz)
  · simpa only [rowsMem] using
      gasSteps_rowEightLast s (rowsMem (mpZeroed s mem 8) pa pb 8 7) pa pb 7
        pdst ret rest hcap hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb
        hpbFit
        ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9344 (by decide) (by omega)
          7).trans hs32z)
        ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9440 (by decide) (by omega)
          7).trans htlz)
        ((readWord_rowsMem (mpZeroed s mem 8) pa pb 8 9408 (by decide) (by omega)
          7).trans hmlz)

def gasSteps_specializedFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) :=
  (gasSteps_dispatch4 s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
    (by simpa using hs32)).trans <|
  (gasSteps_entry s mem pa pb 4 pdst ret rest hcap hrun hcode hfork hnp hact
    (by decide) (by decide) hpa hpaFit hpb hpbFit hcds hs32).trans <|
  gasSteps_rowsFour s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
    hpa hpaFit hpb hpbFit hs32 htl hml

def gasSteps_specializedEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) :=
  (gasSteps_dispatch8 s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
    (by simpa using hs32)).trans <|
  (gasSteps_entry s mem pa pb 8 pdst ret rest hcap hrun hcode hfork hnp hact
    (by decide) (by decide) hpa hpaFit hpb hpbFit hcds hs32).trans <|
  gasSteps_rowsEight s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact
    hpa hpaFit hpb hpbFit hs32 htl hml

/-- Universal execution bridge.  It is observationally identical to the
existing MONPRO trace at the CSUB entry for every admitted limb count. -/
def gasSteps_toCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  by_cases hn4 : n = 4
  · subst n
    exact gasSteps_specializedFour s mem pa pb pdst ret rest hcap hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml
  by_cases hn8 : n = 8
  · subst n
    exact gasSteps_specializedEight s mem pa pb pdst ret rest hcap hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml
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
  exact (gasSteps_dispatchFallback s mem pa pb pdst ret rest hcap hrun hcode
    hfork hnp hact h128 h256).trans
    (gasSteps_monpro s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact
      hn hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml)

/-- The universal dispatcher followed by the unchanged CSUB tail. -/
def gasSteps_monproCsub (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (rowsMem (mpZeroed s mem n) pa pb n n) 8224).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (rowsMem (mpZeroed s mem n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_toCsub s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml).trans
    (Csub.gasSteps_csub s (rowsMem (mpZeroed s mem n) pa pb n n) n pdst ret rest
      hcap hcode hfork hrun hnp hact hn hn32 hjump
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

/-- The full CIOS2-dispatched MONPRO call with the existing arithmetic theorem
discharging the accumulator bound. -/
def gasSteps_monproFull (s : State) (mem : ByteArray) (pa pb p : Nat)
    (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
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
  gasSteps_monproCsub s mem pa pb (p + 2) pdst ret rest hcap hrun hcode hfork hnp
    hact (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hjump
    hdstFit
    (Monpro.monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham
      hmpos hminv)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Full
