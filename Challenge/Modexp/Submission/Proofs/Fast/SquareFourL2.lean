import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourReduce
import Challenge.Modexp.Submission.Proofs.Fast.SquareTop

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourL2
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit

/-- Includes the jump onto the four-word reduction chain and its JUMPDEST. -/
def dispatchProgram : List Instr := [.op (.Dup ⟨9, by decide⟩), .op .JUMP]
def dispatchBlock : Block Artifact.submissionArtifact .Osaka 4516 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3445 2 4516 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)
theorem jump_entry : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4661 = true :=
  Artifact.isValidJumpDest_index 3571 (by rfl)

def state (s : State) (mem : ByteArray) (f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (pc k : Nat) : State :=
  CiosCachedL2.state s (UInt256.ofNat pc) mem f mu c0 4 k pbi pa pb tag (UInt256.ofNat 4661) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)

theorem run_dispatch (s : State) (mem : ByteArray) (f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4661 = true) :
    runInstructions dispatchProgram (state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest 4516 0) =
      some (state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest 4661 0) := by
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  simp [dispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, state,
    CiosCachedL2.state, hc19, hc20, hjump, Nat.add_assoc,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod]

def gasSteps_loops (s : State) (mem : ByteArray) (f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps
      (state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest 4516 0)
      (state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest 4765 3) := by
  let S := state s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hrest : (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have fixed (pc k : Nat) (w : Fin 33) (x loadAddr storeAddr : UInt256)
      (block : Block Artifact.submissionArtifact .Osaka pc (l2Program w x loadAddr storeAddr))
      (hx : x.toNat = 32*(4-2-k))
      (hl : loadAddr.toNat = 8256+32*(4-2-k))
      (hs : storeAddr.toNat = 8256+32*(4-1-k))
      (hk : k+1 < 4) (hp : w.val = 0 → x = UInt256.ofNat 0) :
      Challenge.EvmProof.GasSteps (S pc k) (S (pc+(w.val+35)) (k+1)) := by
    apply block.steps (s := S pc k) (env.transfer rfl rfl) rfl
    have h := CiosCachedL2.run_step w s (UInt256.ofNat pc) mem f mu c0 4 k x loadAddr storeAddr
      hx hl hs pbi pa pb tag (UInt256.ofNat 4661) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest) hrest hact (by decide) hk hp
    simpa only [S, state, Challenge.EvmProof.Word.ofNat_add_mod] using h
  have extra (pc k : Nat) (slot : Fin 3) (x loadAddr storeAddr : UInt256)
      (block : Block Artifact.submissionArtifact .Osaka pc (CiosReadonlyExtra.extraProgram slot loadAddr storeAddr))
      (hx : x.toNat = 32*(4-2-k)) (hx' : x.toNat = CiosReadonlyExtra.cacheAddress slot)
      (hl : loadAddr.toNat = 8256+32*(4-2-k))
      (hs : storeAddr.toNat = 8256+32*(4-1-k)) (hk : k+1 < 4) :
      Challenge.EvmProof.GasSteps (S pc k) (S (pc+34) (k+1)) := by
    apply block.steps (s := S pc k) (env.transfer rfl rfl) rfl
    have h := CiosReadonlyExtra.run_extraStep slot s (UInt256.ofNat pc) mem f mu c0 4 k x loadAddr storeAddr
      hx hx' hl hs pbi pa pb tag (UInt256.ofNat 4661) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact
      (by decide) hk hc
    simpa only [S, state, Challenge.EvmProof.Word.ofNat_add_mod] using h
  have hd : Challenge.EvmProof.GasSteps (S 4516 0) (S 4661 0) :=
    dispatchBlock.steps (env.transfer rfl rfl) rfl
      (run_dispatch s mem f mu c0 pbi pa pb tag tl inv m0 aEnd m96 m64 m32 dst ret rest hcap
        (by rw [env.code]; exact jump_entry))
  have hj : Challenge.EvmProof.GasSteps (S 4661 0) (S 4662 0) := by
    apply CarryRowBlocks.l2Join.steps (s := S 4661 0) (env.transfer rfl rfl) rfl
    have hlen : rest.length+19 < 1024 := by omega
    simp [S, state, CiosCachedL2.state, joinProgram, runInstructions,
      Challenge.EvmProof.Stepper.runInstr, Nat.add_assoc, hlen,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  exact hd.trans <| hj.trans <|
    (extra 4662 0 1 64 8320 8352 CarryRowBlocks.l2Mac4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
    (extra 4696 1 2 32 8288 8320 CarryRowBlocks.l2Mac5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
    fixed 4730 2 0 0 8256 8288 CarryRowBlocks.l2Mac6 (by decide) (by decide) (by decide) (by decide) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourL2
