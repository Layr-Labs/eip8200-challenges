import Challenge.Modexp.Submission.Proofs.Fast.LazyMixedProduct
import Challenge.Modexp.Submission.Proofs.Fast.FusedEntry
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsFour
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsEight
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopRuns
import Challenge.Modexp.Submission.Proofs.Fast.FusedFinish
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
noncomputable section

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMidMemory CarryRowModel FusedEntry SquareLoopBlocks

def retainedFrame (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : List UInt256 :=
  TnM128InitialMultiply.retainedFrame s mem 2368 256 n tl inv m0
    (UInt256.ofNat (2368 + 32*n - 32)) m96 m64 m32 (UInt256.ofNat 256)
    (UInt256.ofNat GenericReturnAdapter.terminalReturnPC) rest

def gasSteps_rows (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hn : n = 4 ∨ n = 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps (rowReady s (mpZeroed s mem n) n tl inv m0 m96 m64 m32 rest)
      (mpCsubState s (rowsCarry (mpZeroed s mem n) 2368 256 n n)
        (UInt256.ofNat 256) (UInt256.ofNat GenericReturnAdapter.terminalReturnPC)
        (retainedFrame s mem n tl inv m0 m96 m64 m32 rest)) := by
  by_cases h4 : n = 4
  · subst n
    unfold rowReady
    unfold TnM128FusedEntry.rowReady
    simpa only [retainedFrame, outState, TnM128Setup.outState, l1Target, TnM128Setup.l1Target,
      TnM128Setup.zeroTn, GenericReturnAdapter.terminalReturnPC] using
      (CarryFull.gasSteps_rowsFour s mem 2368 256 tl inv m0
      (UInt256.ofNat (2368+32*4-32)) m96 m64 m32 (UInt256.ofNat 256)
      (UInt256.ofNat GenericReturnAdapter.terminalReturnPC)
      rest hcap hrun hcode hfork hnp hact (Or.inr rfl) (by decide) (by decide)
      hminv hc he rfl (by intro _ _; rfl))
  · have h8 : n = 8 := hn.resolve_left h4
    subst n
    unfold rowReady
    unfold TnM128FusedEntry.rowReady
    simpa only [retainedFrame, outState, TnM128Setup.outState, l1Target, TnM128Setup.l1Target,
      TnM128Setup.zeroTn, GenericReturnAdapter.terminalReturnPC] using
      (CarryFull.gasSteps_rowsEight s mem 2368 256 tl inv m0
      (UInt256.ofNat (2368+32*8-32)) m96 m64 m32 (UInt256.ofNat 256)
      (UInt256.ofNat GenericReturnAdapter.terminalReturnPC)
      rest hcap hrun hcode hfork hnp hact (Or.inr rfl) (by decide) (by decide)
      hminv hc he rfl (by intro _ _; rfl))

def gasSteps_product (tn : UInt256) (s : State) (mem : ByteArray) (p a mm : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 992) (hn : p+2 = 4 ∨ p+2 = 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hminv : inverseInvariant mem (p+2))
    (hc : CiosReadonly.ReadonlyCache mem (p+2) tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (ham : a < Limbs.radix^(p+2)) (hmpos : 0 < mm)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*(p+2)-32))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080+32*(p+2)))
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*(p+2))) :
    GenericReturnAdapter.TerminalTrace
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3481 s mem (p+2) pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      s (StagedProduct.memory s mem (p+2)) := by
  have hn8 : p+2 ≤ 8 := by omega
  have g1 := TnM128FusedEntry.gasSteps_entry tn s mem (p+2) pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
    (by omega) hn hrun (hcode.trans TnM128GlobalBinding.bytecode_eq) hfork hnp hact hcds hc.lowAddress
  have g2 := gasSteps_rows s mem (p+2) tl inv m0 m96 m64 m32 rest (by omega) hn hrun hcode hfork hnp
    hact hminv hc he
  have hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat GenericReturnAdapter.terminalReturnPC).toNat = true := by
    change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      GenericReturnAdapter.terminalReturnPC = true
    exact TnM128CandidateArtifact.isValidJumpDest_index 3315 (by rfl)
  have hread (addr : Nat) (hd : addr+32 ≤ 2048 ∨ 2624 ≤ addr) :
      MachineState.readWord (rowsCarry (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) addr =
        MachineState.readWord mem addr := by
    rw [readWord_rowsCarry _ 2368 256 (p+2) addr hn8 hd,
      readWord_mpZeroed s mem (p+2) addr hn8 hd]
  let finalRest := retainedFrame s mem (p+2) tl inv m0 m96 m64 m32 rest
  have hfinalRest : finalRest.length ≤ 1008 := by
    have hlen : finalRest.length = 16 + rest.length := by
      simp [finalRest, retainedFrame, TnM128InitialMultiply.retainedFrame,
        TnCacheFrameOps.frame]
      omega
    omega
  have g3 := gasSteps_csubAt s (rowsCarry (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2))
    (p+2) 256 (UInt256.ofNat GenericReturnAdapter.terminalReturnPC) finalRest hfinalRest
    hrun hcode hfork hnp hact (by omega) hn8
    (by omega) hj
    ((hread 2752 (Or.inr (by decide))).trans hml)
    ((hread 2784 (Or.inr (by decide))).trans htl)
    (by rw [Csub.csStep_readWord_disjoint _ (p+2) 2688 (by omega) (Or.inr (by omega)) (p+2) le_rfl,
      hread 2688 (Or.inr (by decide))]; exact hs32)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p+2) 2080 (by omega) (Or.inr (by omega)) (p+2) le_rfl]
      exact LazyMixedProduct.rows_tn_le_one s mem p a (Csub.lowValue mem 256 (p+2) (p+2)) mm hn8
        ha (Csub.fastRepresents_lowValue mem 256 (p+2)) hm ham hmpos hminv)
  have g4 := FusedFinish.gasSteps s (StagedProduct.memory s mem (p+2)) finalRest
    (by omega) hcode hfork hrun hnp
  refine ⟨finalRest, ?_⟩
  exact (g1.trans g2).trans ((g3 hn).trans g4)

#print axioms gasSteps_product
end Challenge.Modexp.Submission.Proofs.Fast.FusedProductTrace
