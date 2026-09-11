import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRows
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Universal cached CIOS-to-MONPRO bridge

Widths four and eight execute the specialized cached CIOS schedules.  Every other
width takes the dispatcher's unchanged jump to the original MONPRO entry.
The specialized arms retain carry on the stack. Their memory agrees with the
original model outside the unused scratch word; the fallback keeps `rowsMem`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedGas CiosCachedMidMemory CarryCached CarryRowModel CarryResult
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRows

opaque gasSteps_rowsFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosOperandCache.OperandCache mem pa 4 m96 m64 m32 aEnd) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 4) pa pb 4 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) := by
  have hs32z : MachineState.readWord (mpZeroed s mem 4) 9344 =
      UInt256.ofNat (32 * 4) :=
    (readWord_mpZeroed s mem 4 9344 (by decide) (by omega)).trans hs32
  have htlz : MachineState.readWord (mpZeroed s mem 4) 9440 =
      UInt256.ofNat (8224 + 32 * 4) :=
    (readWord_mpZeroed s mem 4 9440 (by decide) (by omega)).trans htl
  have hmlz : MachineState.readWord (mpZeroed s mem 4) 9408 =
      UInt256.ofNat (32 * 4 - 32) :=
    (readWord_mpZeroed s mem 4 9408 (by decide) (by omega)).trans hml
  have hminvz := inverse_mpZeroed s mem 4 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s (by decide) (by decide) hpaFit
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsCarry (mpZeroed s mem 4) pa pb 4 i)
      pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) 3 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowFourNext s (rowsCarry (mpZeroed s mem 4) pa pb 4 i) pa pb i
      tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9344 (by decide) (by omega)
        i).trans hs32z)
      ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9440 (by decide) (by omega)
        i).trans htlz)
      ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9408 (by decide) (by omega)
        i).trans hmlz)
      (inverse_rowsCarry (mpZeroed s mem 4) pa pb 4 i (by decide) hminvz)
      (readonly_rows hcz (by decide) pa pb i)
      (operand_rows hez pb i (by decide) (by decide) hpaFit)
  · simpa only [rowsCarry] using
      gasSteps_rowFourLast s (rowsCarry (mpZeroed s mem 4) pa pb 4 3) pa pb 3
        tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb
        hpbFit
        ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9344 (by decide) (by omega)
          3).trans hs32z)
        ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9440 (by decide) (by omega)
          3).trans htlz)
        ((readWord_rowsCarry (mpZeroed s mem 4) pa pb 4 9408 (by decide) (by omega)
          3).trans hmlz)
        (inverse_rowsCarry (mpZeroed s mem 4) pa pb 4 3 (by decide) hminvz)
        (readonly_rows hcz (by decide) pa pb 3)
        (operand_rows hez pb 3 (by decide) (by decide) hpaFit)

opaque gasSteps_rowsEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosOperandCache.OperandCache mem pa 8 m96 m64 m32 aEnd) :
    Challenge.EvmProof.GasSteps
      (outState s (mpZeroed s mem 8) pa pb 8 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  have hs32z : MachineState.readWord (mpZeroed s mem 8) 9344 =
      UInt256.ofNat (32 * 8) :=
    (readWord_mpZeroed s mem 8 9344 (by decide) (by omega)).trans hs32
  have htlz : MachineState.readWord (mpZeroed s mem 8) 9440 =
      UInt256.ofNat (8224 + 32 * 8) :=
    (readWord_mpZeroed s mem 8 9440 (by decide) (by omega)).trans htl
  have hmlz : MachineState.readWord (mpZeroed s mem 8) 9408 =
      UInt256.ofNat (32 * 8 - 32) :=
    (readWord_mpZeroed s mem 8 9408 (by decide) (by omega)).trans hml
  have hminvz := inverse_mpZeroed s mem 8 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s (by decide) (by decide) hpaFit
  refine (Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => outState s (rowsCarry (mpZeroed s mem 8) pa pb 8 i)
      pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) 7 ?_).trans ?_
  · intro i hi
    exact gasSteps_rowEightNext s (rowsCarry (mpZeroed s mem 8) pa pb 8 i) pa pb i
      tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by omega) hpa hpaFit hpb
      hpbFit
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9344 (by decide) (by omega)
        i).trans hs32z)
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9440 (by decide) (by omega)
        i).trans htlz)
      ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9408 (by decide) (by omega)
        i).trans hmlz)
      (inverse_rowsCarry (mpZeroed s mem 8) pa pb 8 i (by decide) hminvz)
      (readonly_rows hcz (by decide) pa pb i)
      (operand_rows hez pb i (by decide) (by decide) hpaFit)
  · simpa only [rowsCarry] using
      gasSteps_rowEightLast s (rowsCarry (mpZeroed s mem 8) pa pb 8 7) pa pb 7
        tl inv m0 aEnd m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb
        hpbFit
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9344 (by decide) (by omega)
          7).trans hs32z)
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9440 (by decide) (by omega)
          7).trans htlz)
        ((readWord_rowsCarry (mpZeroed s mem 8) pa pb 8 9408 (by decide) (by omega)
          7).trans hmlz)
        (inverse_rowsCarry (mpZeroed s mem 8) pa pb 8 7 (by decide) hminvz)
        (readonly_rows hcz (by decide) pa pb 7)
        (operand_rows hez pb 7 (by decide) (by decide) hpaFit)

opaque gasSteps_specializedFour (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) :=
  (gasSteps_dispatch4 s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by simpa using hs32)).trans <|
  (gasSteps_entry s mem pa pb 4 pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by decide) (by decide) hpa (by omega) hpb hpbFit hcds hs32 hml).trans <|
  gasSteps_rowsFour s mem pa pb
    (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
    (MachineState.readWord mem (32*4-32)) (MachineState.readWord mem (pa+32*(4-1))) (MachineState.readWord mem (pa+96)) (MachineState.readWord mem (pa+64))
    (MachineState.readWord mem (pa+32)) pdst ret rest (by omega) hrun hcode hfork hnp hact
    hpa hpaFit hpb hpbFit hs32 htl hml hminv ⟨htl, rfl, rfl⟩ ⟨rfl,rfl,rfl,rfl⟩

opaque gasSteps_specializedEight (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) :=
  (gasSteps_dispatch8 s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by simpa using hs32)).trans <|
  (gasSteps_entry s mem pa pb 8 pdst ret rest (by omega) hrun hcode hfork hnp hact
    (by decide) (by decide) hpa (by omega) hpb hpbFit hcds hs32 hml).trans <|
  gasSteps_rowsEight s mem pa pb
    (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
    (MachineState.readWord mem (32*8-32)) (MachineState.readWord mem (pa+32*(8-1))) (MachineState.readWord mem (pa+96)) (MachineState.readWord mem (pa+64))
    (MachineState.readWord mem (pa+32)) pdst ret rest (by omega) hrun hcode hfork hnp hact
    hpa hpaFit hpb hpbFit hs32 htl hml hminv ⟨htl, rfl, rfl⟩ ⟨rfl,rfl,rfl,rfl⟩

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
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s mem n) pa pb n n) pdst ret rest) := by
  by_cases hn4 : n = 4
  · subst n
    rw [selectedRows, if_pos (Or.inl rfl)]
    exact gasSteps_specializedFour s mem pa pb pdst ret rest (by omega) hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv
  by_cases hn8 : n = 8
  · subst n
    rw [selectedRows, if_pos (Or.inr rfl)]
    exact gasSteps_specializedEight s mem pa pb pdst ret rest (by omega) hrun hcode
      hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv
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
  rw [selectedRows, if_neg (not_or.mpr ⟨hn4, hn8⟩)]
  exact (gasSteps_dispatchFallback s mem pa pb pdst ret rest (by omega) hrun hcode
    hfork hnp hact h128 h256).trans
    (gasSteps_monpro s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact
      hn hn32 hpa (by omega) hpb hpbFit hcds hs32 htl hml)

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
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (selectedRows (mpZeroed s mem n) pa pb n n) 8224).toNat
      ≤ 1) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (selectedRows (mpZeroed s mem n) pa pb n n) n n pdst ret
        rest) :=
  (gasSteps_toCsub s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp hact hn
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv).trans
    (Csub.gasSteps_csub s (selectedRows (mpZeroed s mem n) pa pb n n) n pdst ret rest
      (by omega) hcode hfork hrun hnp hact hn hn32 hjump
      ((readWord_selected_preserved s mem pa pb n n 9408 hn32 (by omega)).trans hml)
      ((readWord_selected_preserved s mem pa pb n n 9440 hn32 (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint (selectedRows (mpZeroed s mem n) pa pb n n) n 9344
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_selected_preserved s mem pa pb n n 9344 hn32 (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint (selectedRows (mpZeroed s mem n) pa pb n n) n
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
        (selectedRows (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) (p + 2)
        pdst ret rest) :=
  gasSteps_monproCsub s mem pa pb (p + 2) pdst ret rest (by omega) hrun hcode hfork hnp
    hact (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hminv hjump
    hdstFit
    (by
      have hr := selectedRows_agree (mpZeroed s mem (p+2)) pa pb (p+2) (p+2)
        hpaFit hpbFit (by omega) hn32 (by omega)
      rw [CarryScratchAgreement.readWord_eq hr 8224 (Or.inr (by decide))]
      exact Monpro.monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham
        hmpos hminv)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFull
