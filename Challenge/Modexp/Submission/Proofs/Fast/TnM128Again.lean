import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128Again
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

/-- The eight-limb CSUB return: carry reset, pointer reset, and the literal jump to the
overwrite-first square row.  The four-limb path returns straight to R4 (4579), so no width
dispatch runs here. -/
def bodyProgram : List Instr :=
  TnCacheFrameOps.reset ++
  [.push 2 256, .op .ADD, .push 2 5062, .op .JUMP]

def program : List Instr :=
  [.op .JUMPDEST] ++ bodyProgram

def againBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4233 program :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3358 8 4233 program
    (by decide) (by rfl) (by rfl) (by decide)

def input (s : State) (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4233)
    (TnCacheFrameOps.frame (UInt256.ofNat 2336) (UInt256.ofNat 4258) (UInt256.ofNat 2336)
      (UInt256.ofNat 3858) tn (MachineState.readWord mem 128) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

theorem run_again (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 5062 = true) :
    runInstructions program (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest) =
      some (TnM128SquareFirstSteps.input s mem aprev tl inv m0 m96 m64 m32 dst ret rest
        (UInt256.ofNat 3858)) := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  simp [program, bodyProgram, TnCacheFrameOps.reset, input, TnM128SquareFirstSteps.input,
    TnM128SquareSteps.outState, TnCacheFrameOps.frame, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hjump,
    hc16, hc17, hc18, ptrAt_zero, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

noncomputable def steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (_htl : tl = UInt256.ofNat 2336) :
    GasSteps (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
      (TnM128SquareFirstSteps.input s mem aprev tl inv m0 m96 m64 m32 dst ret rest
        (UInt256.ofNat 3858)) := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 5062 = true := by
    rw [env.code]
    exact TnM128CandidateArtifact.isValidJumpDest_index 4042 (by rfl)
  exact againBlock.steps (s := input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
    (env.transfer rfl rfl) rfl (run_again s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest hcap hj)

#print axioms steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128Again
