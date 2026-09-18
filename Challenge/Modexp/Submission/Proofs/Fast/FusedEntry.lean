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

def prefixProgram : List Instr := FusionFrame.frameProgram 3481 782
def clearProgram : List Instr :=
  [.push 2 2016, .op (.Dup ⟨10, by decide⟩), .op .SUB,
   .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY]
/-- The boundary reload (E15, pc 3475..3480): after the `CALLDATACOPY` zero-fill the cell
takes the scratch word `mem[2080]`, the value the row heads read there before the
reassembly. -/
def reloadProgram : List Instr :=
  [.push 2 2080, .op .MLOAD, .op (.Swap ⟨6, by decide⟩), .op .POP]

def prefixBlock : Block Artifact.submissionArtifact .Osaka 3414 prefixProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2733 34 3414 prefixProgram
    (by decide) (by rfl) (by rfl) (by decide)
def clearBlock : Block Artifact.submissionArtifact .Osaka 3465 clearProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2767 6 3465 clearProgram
    (by decide) (by rfl) (by rfl) (by decide)
def reloadBlock : Block Artifact.submissionArtifact .Osaka 3475 reloadProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2773 4 3475 reloadProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first-loop register at the fused frame: `sqEnt 8 8 = 3806` after the eight-limb
square rows, the prologue's `l1Target 4 = 5302` on the four-limb path.  E8 turns it into
`l1Base n`. -/
def stagedEnt (n : Nat) : UInt256 :=
  if n = 4 then UInt256.ofNat 5302 else UInt256.ofNat 3806

@[simp] theorem stagedEnt_four : stagedEnt 4 = UInt256.ofNat 5302 := rfl
@[simp] theorem stagedEnt_eight : stagedEnt 8 = UInt256.ofNat 3806 := rfl

theorem stagedBase_stagedEnt (n : Nat) (hn : n = 4 ∨ n = 8) :
    FusionFrame.stagedBase (stagedEnt n) = l1Base n := by
  rcases hn with rfl | rfl
  · exact FusionFrame.stagedBase_four
  · exact FusionFrame.stagedBase_eight

/-- The multiply's row-0 frame: the cell holds the scratch word of the (zero-filled)
memory, installed by the reload E15. -/
def rowReady (s : State) (mem : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  outState s mem 256 n 0 (UInt256.ofNat 3481) (l1Base n) (MachineState.readWord mem 2080) inv m0
    (tl :: m96 :: m64 :: m32 :: UInt256.ofNat (2368+32*n-32) ::
      UInt256.ofNat 256 :: UInt256.ofNat 782 :: rest)

/-- After the fused frame program (E8 done): the row-0 frame with the cell still holding
whatever entered the staging (`cy`), at the clear block. -/
def prefixState (s : State) (mem : ByteArray) (n : Nat)
    (cy tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  { outState s mem 256 n 0 (UInt256.ofNat 3481) (l1Base n) cy inv m0
      (tl :: m96 :: m64 :: m32 :: UInt256.ofNat (2368+32*n-32) ::
        UInt256.ofNat 256 :: UInt256.ofNat 782 :: rest) with pc := UInt256.ofNat 3465 }

/-- After the zero-fill, at the reload block. -/
def clearedState (s : State) (mem : ByteArray) (n : Nat)
    (cy tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) : State :=
  { outState s mem 256 n 0 (UInt256.ofNat 3481) (l1Base n) cy inv m0
      (tl :: m96 :: m64 :: m32 :: UInt256.ofNat (2368+32*n-32) ::
        UInt256.ofNat 256 :: UInt256.ofNat 782 :: rest) with pc := UInt256.ofNat 3475 }

theorem run_prefix (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (htl : tl = UInt256.ofNat (2080+32*n)) (hent : ent = stagedEnt n) :
    runInstructions prefixProgram
      (frameAt 3414 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) =
      some (prefixState s mem n cy tl inv m0 m96 m64 m32 rest) := by
  subst hent
  have h := FusionFrame.run_prefix (s := {s with memory := mem}) (p := pbi)
      (oldHead := UInt256.ofNat 4190) (oldEnd := UInt256.ofNat (2368-32))
      (ent := stagedEnt n) (neg := negative32) (mask := allOnes) (ent2 := cy)
      (inv := inv) (m0 := m0) (tl := tl) (m96 := m96) (m64 := m64) (m32 := m32)
      (aprev := aprev) (dst := pdst) (ret := ret) (head := UInt256.ofNat 3481)
      (finish := UInt256.ofNat 782) (rest := rest) (by omega)
  rw [stagedBase_stagedEnt n hn] at h
  rcases hn with rfl | rfl <;> subst tl <;> exact h

theorem run_clear (s : State) (mem : ByteArray) (n : Nat)
    (cy tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htl : tl = UInt256.ofNat (2080+32*n)) :
    runInstructions clearProgram (prefixState s mem n cy tl inv m0 m96 m64 m32 rest) =
      some (clearedState s (mpZeroed s mem n) n cy tl inv m0 m96 m64 m32 rest) := by
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
    prefixState, clearedState, outState, mpZeroed, hsub, hactC, hcdsN, hsizeN, h2048,
    State.activeWordsAfterUInt256, hc16, hc17, hc18, hc19,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_reload (s : State) (mem : ByteArray) (n : Nat)
    (cy tl inv m0 m96 m64 m32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions reloadProgram (clearedState s mem n cy tl inv m0 m96 m64 m32 rest) =
      some (rowReady s mem n tl inv m0 m96 m64 m32 rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h2080 : (2080 : UInt256).toNat = 2080 := by decide
  simp [reloadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    clearedState, rowReady, outState, hactN, h2080, State.activeWordsAfterUInt256,
    List.exchange, hc16, hc17, hc18,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hn : n = 4 ∨ n = 8)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (htl : tl = UInt256.ofNat (2080+32*n)) (hent : ent = stagedEnt n) :
    Challenge.EvmProof.GasSteps
      (frameAt 3414 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest)
      (rowReady s (mpZeroed s mem n) n tl inv m0 m96 m64 m32 rest) :=
  ((prefixBlock.steps (CarryRowBlocks.environment
    (frameAt 3414 s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest) hcode hfork hrun hnp) rfl
    (run_prefix s mem n pbi ent cy tl inv m0 m96 m64 m32 aprev pdst ret rest hcap hn htl hent)).trans
  (clearBlock.steps (CarryRowBlocks.environment
    (prefixState s mem n cy tl inv m0 m96 m64 m32 rest) hcode hfork hrun hnp) rfl
    (run_clear s mem n cy tl inv m0 m96 m64 m32 rest hcap hn hact hcds htl))).trans
  (reloadBlock.steps (CarryRowBlocks.environment
    (clearedState s (mpZeroed s mem n) n cy tl inv m0 m96 m64 m32 rest) hcode hfork hrun hnp) rfl
    (run_reload s (mpZeroed s mem n) n cy tl inv m0 m96 m64 m32 rest hcap hact))

#print axioms gasSteps_entry
end Challenge.Modexp.Submission.Proofs.Fast.FusedEntry
