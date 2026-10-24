import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubInstructions
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubTrace
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareLoopBlocks
import Challenge.Modexp.Submission.Proofs.CycleGlobal.LazyCsubTrace

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Run lemmas of the squaring loop: the four-limb exit `m4j` and the lazy gate

The four-limb exit `m4j` (4248) as a `runInstructions` lemma and gas step, and the final
conditional subtraction on an abstract memory.
-/

namespace CycleSubmission.Global.Fast.SquareLoopBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## Run lemmas -/

/-- The `last` entry: the retained frame under the unused CSUB call pair `[pdst, again]`. -/
def lazyCsubState (s : State) (mem : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  LazyGate.atState s mem 3697 dst ret rest

/-- The four-limb exit `m4j` (4248): the retained frame, no call pair on top. -/
def m4jAt (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pcM4j
           stack := frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `m4j`: call the lazy gate as a subroutine with `[2368, after_sq]` on the retained frame. -/
theorem run_m4j (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) :
    runInstructions m4jProgram
      (m4jAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
    some (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3256)
      (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) := by
  have hc16' : rest.length + 16 < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 3697 = true := by
    rw [hcode]; exact jumpDestLazy
  simp [m4jProgram, TnM128SquareExit.m4jProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, frameStack, m4jAt, pcM4j, lazyCsubState, LazyGate.atState,
    hjd, hc16', capacity, Nat.add_assoc, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The loop's blocks as gas steps -/

/-- `m4j`: into the lazy gate with `[2368, after_sq]`. -/
def gasSteps_m4j (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (m4jAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (lazyCsubState s mem (UInt256.ofNat 2368) (UInt256.ofNat 3256)
        (frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)) :=
  m4jBlock.steps
    (CycleSubmission.Global.Fast.EarlyCsub.environment (m4jAt s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_m4j s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hcode)

/-- The final conditional subtraction on an abstract memory: `[2048, ret]` above `tail`. -/
def gasSteps_lazyCsubAt (s : State) (X : ByteArray) (n dst : Nat) (ret : UInt256)
    (tail : List UInt256) (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8) (hdst : dst + 32 * n ≤ 2816)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hml : MachineState.readWord X 2752 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord X 2784 = UInt256.ofNat (2080 + 32 * n))
    (hs32 : MachineState.readWord (Csub.csStep X n n).memory 2688 = UInt256.ofNat (32 * n))
    (htn : (MachineState.readWord (Csub.csStep X n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps
      (lazyCsubState s X (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail, memory := LazyCsub.resultMemory X n dst } := by
  have hdstNat : (UInt256.ofNat dst).toNat = dst := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have g := LazyCsub.gasSteps_csub_lazy s X n (UInt256.ofNat dst) ret tail
    hcap hcode hfork hrun hnp hact hn hn32 hjump hml htl hs32
    (by simpa only [hdstNat] using hdst) htn hfast
  simpa only [lazyCsubState, LazyGate.returnedState, hdstNat] using g

def gasSteps_csubAt (s : State) (X : ByteArray) (n dst : Nat) (ret : UInt256)
    (tail : List UInt256) (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8) (hdst : dst + 32 * n ≤ 2816)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hml : MachineState.readWord X 2752 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord X 2784 = UInt256.ofNat (2080 + 32 * n))
    (hs32 : MachineState.readWord (Csub.csStep X n n).memory 2688 = UInt256.ofNat (32 * n))
    (htn : (MachineState.readWord (Csub.csStep X n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps
      (CycleSubmission.Global.Fast.EarlyCsub.atState s X 3442 (UInt256.ofNat dst) ret tail)
      { s with pc := ret, stack := tail, memory := Csub.csResultMemory X n dst } := by
  have g := Csub.gasSteps_csub s X n (UInt256.ofNat dst) ret tail hcap hcode hfork hrun hnp
    hact hn hn32 hjump hml htl hs32
    (by rw [show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]; omega) htn hfast
  refine g.cast rfl ?_
  rw [show Csub.csReturnedState s X n n (UInt256.ofNat dst) ret tail =
      { s with pc := ret, stack := tail,
               memory := Csub.csResultMemory X n (UInt256.ofNat dst).toNat } from rfl,
    show (UInt256.ofNat dst).toNat = dst from by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]

end CycleSubmission.Global.Fast.SquareLoopBlocks
