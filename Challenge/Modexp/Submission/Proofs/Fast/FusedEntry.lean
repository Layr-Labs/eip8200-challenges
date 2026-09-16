import Challenge.Modexp.Submission.Proofs.Fast.FusionFrame
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusedEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareLoopBlocks

def prefixProgram : List Instr := FusionFrame.frameProgram 3351 1047
def clearProgram : List Instr :=
  [.push 2 2016, .op (.Dup ⟨10, by decide⟩), .op .SUB,
   .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY]

def prefixBlock : Block Artifact.submissionArtifact .Osaka 3300 prefixProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2442 25 3300 prefixProgram
    (by decide) (by rfl) (by rfl) (by decide)
def clearBlock : Block Artifact.submissionArtifact .Osaka 3341 clearProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2467 6 3341 clearProgram
    (by decide) (by rfl) (by rfl) (by decide)

def rowReady (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  outState s mem 256 n 0 (UInt256.ofNat 3351) (l1Target n) inv m0
    (tl :: m96 :: m64 :: m32 :: UInt256.ofNat (2368+32*n-32) ::
      UInt256.ofNat 256 :: UInt256.ofNat 1047 :: rest)

def prefixState (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  { rowReady s mem n tl inv m0 m96 m64 m32 rest with pc := UInt256.ofNat 3341 }

theorem run_prefix (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (htl : tl = UInt256.ofNat (2080+32*n)) :
    runInstructions prefixProgram
      (frameAt 3300 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (prefixState s mem n tl inv m0 m96 m64 m32 rest) := by
  rcases hn with rfl | rfl <;> subst tl <;>
    exact FusionFrame.run_prefix (s := {s with memory := mem}) (p := pbi)
      (oldHead := UInt256.ofNat 4065) (oldEnd := UInt256.ofNat (2368-32))
      (ent := ent) (neg := negative32) (mask := allOnes) (ent2 := l2Target _)
      (inv := inv) (m0 := m0) (tl := _) (m96 := m96) (m64 := m64) (m32 := m32)
      (aprev := aprev) (dst := pdst) (ret := ret) (head := UInt256.ofNat 3351)
      (finish := UInt256.ofNat 1047) (rest := rest) (by omega)

theorem run_clear (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htl : tl = UInt256.ofNat (2080+32*n)) :
    runInstructions clearProgram (prefixState s mem n tl inv m0 m96 m64 m32 rest) =
      some (rowReady s (mpZeroed s mem n) n tl inv m0 m96 m64 m32 rest) := by
  have hn8 : n ≤ 8 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hsub : tl - UInt256.ofNat 2016 = UInt256.ofNat (64+32*n) := by
    rw [htl, Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have hactC := activeWords_fix s 2048 (64+32*n) (by omega) (by omega) hact
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt hcds
  have hsizeN : (64+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64+32*n := Nat.mod_eq_of_lt (by omega)
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  simp [clearProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    prefixState, rowReady, outState, mpZeroed, hsub, hactC, hcdsN, hsizeN, h2048,
    State.activeWordsAfterUInt256, hc16, hc17, hc18, hc19,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htl : tl = UInt256.ofNat (2080+32*n)) :
    Challenge.EvmProof.GasSteps
      (frameAt 3300 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (rowReady s (mpZeroed s mem n) n tl inv m0 m96 m64 m32 rest) :=
  (prefixBlock.steps (CarryRowBlocks.environment
    (frameAt 3300 s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_prefix s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hn htl)).trans
  (clearBlock.steps (CarryRowBlocks.environment
    (prefixState s mem n tl inv m0 m96 m64 m32 rest) hcode hfork hrun hnp) rfl
    (run_clear s mem n tl inv m0 m96 m64 m32 rest hcap hn hact hcds htl))

#print axioms gasSteps_entry
end Challenge.Modexp.Submission.Proofs.Fast.FusedEntry
