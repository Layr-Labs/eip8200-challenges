import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateR8FullSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateAgain
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open TnCandidateSquareRowSteps TnCandidateReductionSteps

def program : List Instr := TnCacheFrameOps.reset ++
  [.push 2 256, .push 2 320, .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY,
   .op .ADD, .push 2 283, .op (.Dup ⟨7, by decide⟩), .op .SUB,
   .op (.Swap ⟨3, by decide⟩), .op .POP]

def block : Block TnCandidateArtifact.submissionArtifact .Osaka 4419 program :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3346 14 4419 program
    (by decide) (by rfl) (by rfl) (by decide)

def input (s : State) (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat 4419)
    (TnCacheFrameOps.frame (UInt256.ofNat 2336) (UInt256.ofNat 4471) (UInt256.ofNat 2336)
      (UInt256.ofNat 4036) tn (UInt256.ofNat 4023) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest))

def output (s : State) (mem : ByteArray) (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : State :=
  { rowState s ⟨mpZeroed s mem 8, UInt256.ofNat 0⟩ 8 0 aprev tl inv m0 m96 m64 m32 dst ret rest
      with pc := UInt256.ofNat 4441 }

theorem run_again (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256) :
    runInstructions program (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest) =
      some (output s mem aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  have hactC := activeWords_fix s 2048 320 (by decide) (by decide) hact
  have hcdsN : s.executionEnv.calldata.size % 2^256 = s.executionEnv.calldata.size :=
    Nat.mod_eq_of_lt hcds
  norm_num only at hcdsN
  have haddr : (2048 : UInt256).toNat = 2048 := by decide
  have hlen : (320 : UInt256).toNat = 320 := by decide
  have hptr : UInt256.ofNat 256 + UInt256.ofNat 2336 = UInt256.ofNat 2592 := by decide
  have hent : UInt256.ofNat 4023 - UInt256.ofNat 283 = UInt256.ofNat 3740 := by decide
  simp (config := { maxSteps := 200000 }) [program, TnCacheFrameOps.reset, input, output,
    rowState, sqEnt, TnCacheRowPointers.pointer, ptrAt_zero, l2PC, mpZeroed,
    TnCacheFrameOps.frame, framed, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc16, hc17, hc18, hc19, hc20, hactC, hcdsN, haddr, hlen, hptr, hent,
    State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

noncomputable def again_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256) :
    GasSteps (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
      (output s mem aprev tl inv m0 m96 m64 m32 dst ret rest) :=
  block.steps (s := input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest)
    (env.transfer rfl rfl) rfl (run_again s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest
      hcap hact hcds)

#print axioms again_steps

def hookProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .push 2 4171, .op .EQ,
   .push 2 4809, .op .JUMPI]

def hookBlock : Block TnCandidateArtifact.submissionArtifact .Osaka 4409 hookProgram :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3340 6 4409 hookProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem run_hook (s : State) (mem : ByteArray)
    (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    runInstructions hookProgram
      { input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4409 } =
      some (input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hcond : ¬ UInt256.isTrue ((UInt256.ofNat 4171).eq (UInt256.ofNat 4023)) := by decide
  simp [hookProgram, input, TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc16, hc17, hc18, hcond,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The eight-limb dispatch preserves the carry until the immediately following
reset, then enters the next square with zero carry and zero scratch memory. -/
noncomputable def hook_again_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (tn aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256) :
    GasSteps
      { input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4409 }
      (output s mem aprev tl inv m0 m96 m64 m32 dst ret rest) := by
  have hg := hookBlock.steps
    (s := { input s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest with pc := UInt256.ofNat 4409 })
    (env.transfer rfl rfl) rfl (run_hook s mem tn aprev tl inv m0 m96 m64 m32 dst ret rest hcap)
  exact hg.trans (again_steps s env mem tn aprev tl inv m0 m96 m64 m32 dst ret rest hcap hact hcds)

#print axioms hook_again_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateAgain
