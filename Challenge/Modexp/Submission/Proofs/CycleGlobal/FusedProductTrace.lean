import Challenge.Modexp.Submission.Proofs.Fast.LazyMixedProduct
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnM128FusedEntry
import Challenge.Modexp.Submission.Proofs.CycleGlobal.CarryFullRowsFour
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareLoopRuns
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleSubmission.Global.Fast.FusedProductTrace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMidMemory CarryRowModel

def gasSteps_rows (s : State) (mem : ByteArray) (n : Nat)
    (w3 ent tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hn : n = 4)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hw3 : n = 8 → w3 = MachineState.readWord mem 192) :
    Challenge.EvmProof.GasSteps (TnM128FusedEntry.rowReady s (mpZeroed s mem n) n w3 ent tl inv m0 m96 m64 m32 rest)
      (CycleSubmission.Global.Fast.EarlyCsub.atState s (rowsCarry (mpZeroed s mem n) 2368 256 n n) 3442
        (UInt256.ofNat 256) (UInt256.ofNat 690) rest) := by
  subst n
  exact CarryFull.gasSteps_rowsFour s mem 2368 w3 ent tl inv m0
    (UInt256.ofNat (2368+32*4-32)) m96 m64 m32 (UInt256.ofNat 256) (UInt256.ofNat 690)
    rest hcap hrun hcode hfork hnp hact (Or.inr rfl)
    hminv hc he rfl (by intro _ _; rfl)

def gasSteps_product (tn : UInt256) (s : State) (mem : ByteArray) (p a mm : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hn : p+2 = 4) (htn : tn = UInt256.ofNat 0)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
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
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*(p+2)))
    (hw3 : p+2 = 8 → w3 = MachineState.readWord mem 192) :
    Challenge.EvmProof.GasSteps
      (TnM128SquareExit.frameAt tn (MachineState.readWord mem 128) 3256 s mem (p+2) pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      {s with pc := UInt256.ofNat 690, stack := rest, memory := StagedProduct.memory s mem (p+2)} := by
  have hn8 : p+2 ≤ 8 := by omega
  have g1 := TnM128FusedEntry.gasSteps_entry tn s mem (p+2) pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest
    (by omega) hn htn hrun hcode hfork hnp hact hcds htl
  have g2 := gasSteps_rows s mem (p+2) w3 ent tl inv m0 m96 m64 m32 rest hcap hn hrun hcode hfork hnp
    hact hminv hc he hw3
  have hj : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode
      (UInt256.ofNat 690).toNat = true := by
    change Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 690 = true
    exact CycleSubmission.Global.Binding.jumpDest 486 (by rfl)
  have hread (addr : Nat) (hd : addr+32 ≤ 2048 ∨ 2624 ≤ addr) :
      MachineState.readWord (rowsCarry (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) addr =
        MachineState.readWord mem addr := by
    rw [readWord_rowsCarry _ 2368 256 (p+2) addr hn8 hd,
      readWord_mpZeroed s mem (p+2) addr hn8 hd]
  have g3 := CycleSubmission.Global.Fast.SquareLoopBlocks.gasSteps_csubAt s (rowsCarry (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2))
    (p+2) 256 (UInt256.ofNat 690) rest (by omega) hrun hcode hfork hnp hact (by omega) hn8
    (by omega) hj
    ((hread 2752 (Or.inr (by decide))).trans hml)
    ((hread 2784 (Or.inr (by decide))).trans htl)
    (by rw [Csub.csStep_readWord_disjoint _ (p+2) 2688 (by omega) (Or.inr (by omega)) (p+2) le_rfl,
      hread 2688 (Or.inr (by decide))]; exact hs32)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p+2) 2080 (by omega) (Or.inr (by omega)) (p+2) le_rfl]
      exact LazyMixedProduct.rows_tn_le_one s mem p a (Csub.lowValue mem 256 (p+2) (p+2)) mm hn8
        ha (Csub.fastRepresents_lowValue mem 256 (p+2)) hm ham hmpos hminv)
  exact (g1.trans g2).trans (g3 (Or.inl hn))

end CycleSubmission.Global.Fast.FusedProductTrace
