import Challenge.Modexp.Submission.Proofs.Fast.SquareInitBinding

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareSelect
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast SquareInit
open Challenge.EvmProof.Word

def guard (_mem : ByteArray) (pa pb : UInt256) : UInt256 :=
  UInt256.eq pb pa

theorem guard_def (mem : ByteArray) (pa pb : UInt256) :
    guard mem pa pb =
      UInt256.eq pb pa := rfl

def checkProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .EQ,
   .push 2 5027, .op .JUMPI]
def normalProgram : List Instr :=
  [.push 0 0, .push 2 2368, .op .MSTORE, .push 2 4173, .push 2 5031, .op .JUMP]
def squareProgram : List Instr := [.op .JUMPDEST, .push 2 5040]
def storeProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2720, .op .MSTORE, .push 2 4076, .op .JUMP]

theorem destSquare : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5027 = true :=
  Artifact.isValidJumpDest_index 3829 (by rfl)
theorem destStore : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5031 = true :=
  Artifact.isValidJumpDest_index 3831 (by rfl)
theorem destHeader : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4076 = true :=
  Artifact.isValidJumpDest_index 3085 (by rfl)

def checkBlock : Block Artifact.submissionArtifact .Osaka 5007 checkProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3817 6 5007 checkProgram
    (by decide) (by rfl) (by rfl) (by decide)
def normalBlock : Block Artifact.submissionArtifact .Osaka 5015 normalProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3823 6 5015 normalProgram
    (by decide) (by rfl) (by rfl) (by decide)
def squareBlock : Block Artifact.submissionArtifact .Osaka 5027 squareProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3829 2 5027 squareProgram
    (by decide) (by rfl) (by rfl) (by decide)
def storeBlock : Block Artifact.submissionArtifact .Osaka 5031 storeProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3831 5 5031 storeProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem run_check (s : State) (mem : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 91 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions checkProgram (stateAt s mem 5007 ([pa,pb,dst,ret] ++ rest)) =
      some (stateAt s mem (if UInt256.isTrue (guard mem pa pb) then 5027 else 5015)
        ([pa,pb,dst,ret] ++ rest)) := by
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 2784 32 (by decide) (by decide) hact
  have h9344 : (2784 : UInt256).toNat = 2784 := by decide
  have h5036 : (5027 : UInt256).toNat = 5027 := by decide
  have he5036 : (5027 : UInt256) = UInt256.ofNat 5027 := by decide
  by_cases hc : UInt256.isTrue (UInt256.eq pb pa) <;>
    simp [checkProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
      hc4, hc5, hc6, hc7, ha, h9344, h5036, he5036, hcode, destSquare, guard, hc,
      State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

theorem run_normal (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 91 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions normalProgram (stateAt s mem 5015 rest) =
      some (stateAt s (storeWord mem 2368 (UInt256.ofNat 0)) 5031
        (UInt256.ofNat 4173 :: rest)) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 2368 32 (by decide) (by decide) hact
  have hd : (2368 : UInt256).toNat = 2368 := by decide
  have hp : (5031 : UInt256).toNat = 5031 := by decide
  have hep : (5031 : UInt256) = UInt256.ofNat 5031 := by decide
  have hv : (4173 : UInt256) = UInt256.ofNat 4173 := by decide
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := by decide
  simp [normalProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    storeWord, hc0, hc1, hc2, ha, hd, hp, hep, hv, hz, hcode, destStore,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

theorem run_square (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions squareProgram (stateAt s mem 5027 rest) =
      some (stateAt s mem 5031 (UInt256.ofNat 5040 :: rest)) := by
  have hv : (5040 : UInt256) = UInt256.ofNat 5040 := by decide
  simp [squareProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    show rest.length < 1024 by omega, hv, succ_ofNat_mod, ofNat_add_mod]

theorem run_store (s : State) (mem : ByteArray) (route : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 91 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions storeProgram (stateAt s mem 5031 (route :: rest)) =
      some (stateAt s (storeWord mem 2720 route) 4076 rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 2720 32 (by decide) (by decide) hact
  have hd : (2720 : UInt256).toNat = 2720 := by decide
  have hp : (4076 : UInt256).toNat = 4076 := by decide
  have hep : (4076 : UInt256) = UInt256.ofNat 4076 := by decide
  simp [storeProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    storeWord, hc0, hc1, hc2, ha, hd, hp, hep, hcode, destHeader,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

def selectedMemory (mem : ByteArray) (pa pb : UInt256) : ByteArray :=
  if UInt256.isTrue (guard mem pa pb) then storeWord mem 2720 (UInt256.ofNat 5040)
  else storeWord (storeWord mem 2368 (UInt256.ofNat 0)) 2720 (UInt256.ofNat 4173)

def gasSteps_select (s : State) (mem : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 91 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5007 ([pa,pb,dst,ret] ++ rest))
      (stateAt s (selectedMemory mem pa pb) 4076 ([pa,pb,dst,ret] ++ rest)) := by
  let args := [pa,pb,dst,ret] ++ rest
  have hargs : args.length ≤ 1018 := by simp only [args, List.length_append, List.length_cons, List.length_nil]; omega
  have check := checkBlock.steps (EarlyCsub.environment (stateAt s mem 5007 args) hcode hfork hrun hnp) rfl
    (run_check s mem pa pb dst ret rest hcap hact hcode)
  by_cases hs : UInt256.isTrue (guard mem pa pb)
  · rw [if_pos hs] at check
    have sq := squareBlock.steps (EarlyCsub.environment (stateAt s mem 5027 args) hcode hfork hrun hnp) rfl
      (run_square s mem args hargs)
    have put := storeBlock.steps (EarlyCsub.environment (stateAt s mem 5031 (UInt256.ofNat 5040 :: args)) hcode hfork hrun hnp) rfl
      (run_store s mem (UInt256.ofNat 5040) args hargs hact hcode)
    simpa only [selectedMemory, if_pos hs] using check.trans (sq.trans put)
  · rw [if_neg hs] at check
    have normal := normalBlock.steps (EarlyCsub.environment (stateAt s mem 5015 args) hcode hfork hrun hnp) rfl
      (run_normal s mem args hargs hact hcode)
    have put := storeBlock.steps (EarlyCsub.environment (stateAt s (storeWord mem 2368 (UInt256.ofNat 0)) 5031 (UInt256.ofNat 4173 :: args)) hcode hfork hrun hnp) rfl
      (run_store s (storeWord mem 2368 (UInt256.ofNat 0)) (UInt256.ofNat 4173)
        args hargs hact hcode)
    simpa only [selectedMemory, if_neg hs] using check.trans (normal.trans put)

#print axioms gasSteps_select

end Challenge.Modexp.Submission.Proofs.Fast.SquareSelect
