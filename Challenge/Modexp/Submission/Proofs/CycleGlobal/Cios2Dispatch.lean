import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleCaller.Blocks
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
import Challenge.Modexp.Submission.Proofs.Fast.SquarePreclearMemory

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
Kernel dispatch and setup, bound to the submitted cached-carry/modulus artifact.
The multiply entry at 3209 pushes row head 3358, then enters common3213 and
setup3214. The square caller selects staged-square entry4394 instead.
`TnM128Setup.run_entry` proves the 62 setup instructions, including operand
staging, zero carry initialization, and the cached modulus word at offset128.
-/

namespace CycleSubmission.Global.Fast.Cios2Dispatch
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel WindowTwentyOneBinding

abbrev commonGuardProgram := CycleSubmission.CallerBlocks.commonProgram
abbrev commonGuard := CycleSubmission.CallerBlocks.commonBlock

def relocatedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
 {CiosCached.setupState s mem hd pa pb pdst ret rest with pc := UInt256.ofNat 3156}
def commonState (s : State) (mem : ByteArray) (_hd : UInt256) (_pa _pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 3146, memory := mem, stack := [pdst, ret] ++ rest}
opaque gasSteps_commonSetupSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0)
    (hhd : hd = UInt256.ofNat 3710) (hpaEq : pa = 2112) (hpbEq : pb = 512)
    (hret : ret = UInt256.ofNat (32*n)) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (SquarePartialClear.memory (StagedOperand.stageW mem pa n)) pb n 0 hd
        (UInt256.ofNat 3347)
        (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0)
        (UInt256.ofNat 0 :: UInt256.ofNat 0 ::
          MachineState.readWord mem 2720 :: UInt256.ofNat 0 ::
          UInt256.ofNat 0 :: pdst :: ret :: rest)) := by
  subst hd
  subst pa
  subst pb
  let env : Environment CycleSubmission.Artifact.artifact .Osaka s :=
    ⟨(by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide),hcode,hfork,hrun,hnp⟩
  have hc := CycleSubmission.CallerBlocks.commonBlock.steps
    (s := commonState s mem (UInt256.ofNat 3710) 2112 512 pdst ret rest)
    (env.transfer rfl rfl) rfl (CycleSubmission.CallerBlocks.common_run s mem pdst ret rest (by omega))
  have hs := CycleSubmission.CallerBlocks.setupBlock.steps
    (s := relocatedSetupState s mem (UInt256.ofNat 3710) 2112 512 pdst ret rest)
    (env.transfer rfl rfl) rfl
    (CycleSubmission.DeadSetup.run_entry_sq s mem (UInt256.ofNat 3710) 2112 512 n pdst ret rest hcap hact
      (by rcases hn with rfl | rfl <;> omega) (by rcases hn with rfl | rfl <;> omega)
      hpaFit hpb hpbFit hcds hs32 hret (by rw [hcode]; exact hjump))
  exact hc.trans hs
end CycleSubmission.Global.Fast.Cios2Dispatch
