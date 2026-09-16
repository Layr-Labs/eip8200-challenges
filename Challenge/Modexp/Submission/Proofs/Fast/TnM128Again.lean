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

/-- The eight-limb repeat path: width dispatch, carry reset, pointer reset,
entry reset, and the literal jump to the overwrite-first square row. -/
def program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨9, by decide⟩), .push 2 2208, .op .EQ,
   .push 2 4422, .op .JUMPI] ++ TnCacheFrameOps.reset ++
  [.push 2 256, .op .ADD, .push 2 3387, .op (.Swap ⟨3, by decide⟩), .op .POP,
   .push 2 4917, .op .JUMP]

def guardProgram : List Instr := program.take 6
def bodyProgram : List Instr := program.drop 6

def guardBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4067 guardProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3037 6 4067 guardProgram
    (by decide) (by rfl) (by rfl) (by decide)
def bodyBlock : Block TnM128CandidateArtifact.submissionArtifact .Osaka 4077 bodyProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3043 10 4077 bodyProgram
    (by decide) (by rfl) (by rfl) (by decide)

def input (s : State) (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4067)
    (TnCacheFrameOps.frame (UInt256.ofNat 2336) (UInt256.ofNat 4093) (UInt256.ofNat 2336)
      (UInt256.ofNat 3683) tn (MachineState.readWord mem 128) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

theorem run_again (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (htl : tl = UInt256.ofNat 2336)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4917 = true) :
    runInstructions program (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest) =
      some (TnM128SquareFirstSteps.input s mem aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hcond : ¬UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2336)) := by decide
  simp [program, TnCacheFrameOps.reset, input, TnM128SquareFirstSteps.input,
    TnM128SquareSteps.outState, TnCacheFrameOps.frame, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, htl, hcond, hjump,
    hc16, hc17, hc18, ptrAt_zero, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_body (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (htl : tl = UInt256.ofNat 2336)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4917 = true) :
    runInstructions bodyProgram {input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4077} =
      some (TnM128SquareFirstSteps.input s mem aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hcond : ¬UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2336)) := by decide
  simp [bodyProgram, program, TnCacheFrameOps.reset, input, TnM128SquareFirstSteps.input,
    TnM128SquareSteps.outState, TnCacheFrameOps.frame, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, htl, hcond, hjump,
    hc16, hc17, hc18, ptrAt_zero, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_guard (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (htl : tl = UInt256.ofNat 2336) :
    runInstructions guardProgram (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest) =
      some {input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4077} := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hcond : ¬UInt256.isTrue ((UInt256.ofNat 2208).eq (UInt256.ofNat 2336)) := by decide
  simp [guardProgram, program, input, TnCacheFrameOps.frame, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, htl, hcond, hc16, hc17, hc18,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable def steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (htl : tl = UInt256.ofNat 2336) :
    GasSteps (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
      (TnM128SquareFirstSteps.input s mem aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 4917 = true := by
    rw [env.code]
    exact TnM128CandidateArtifact.isValidJumpDest_index 3724 (by rfl)
  have g0 := guardBlock.steps (s := input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
    (env.transfer rfl rfl) rfl (run_guard s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest hcap htl)
  have g1 := bodyBlock.steps
    (s := {input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4077})
    (env.transfer rfl rfl) rfl (run_body s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest hcap htl hj)
  exact g0.trans g1

#print axioms steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128Again
