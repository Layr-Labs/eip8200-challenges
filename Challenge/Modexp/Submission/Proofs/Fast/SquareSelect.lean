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

def guard (mem : ByteArray) (pa pb : UInt256) : UInt256 :=
  UInt256.land (UInt256.eq 256 (MachineState.readWord mem 9344)) (UInt256.eq pb pa)

theorem guard_def (mem : ByteArray) (pa pb : UInt256) :
    guard mem pa pb =
      UInt256.land (UInt256.eq 256 (MachineState.readWord mem 9344)) (UInt256.eq pb pa) := rfl

def checkProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .EQ,
   .push 2 9344, .op .MLOAD, .push 2 256, .op .EQ, .op .AND,
   .push 2 5036, .op .JUMPI]
def normalProgram : List Instr :=
  [.push 0 0, .push 2 8928, .op .MSTORE, .push 2 4173, .push 2 5040, .op .JUMP]
def squareProgram : List Instr := [.op .JUMPDEST, .push 2 5049]
def storeProgram : List Instr :=
  [.op .JUMPDEST, .push 2 9280, .op .MSTORE, .push 2 4076, .op .JUMP]

theorem destSquare : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5036 = true :=
  Artifact.isValidJumpDest_index 3831 (by rfl)
theorem destStore : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5040 = true :=
  Artifact.isValidJumpDest_index 3833 (by rfl)
theorem destHeader : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4076 = true :=
  Artifact.isValidJumpDest_index 3082 (by rfl)

def checkBlock : Block Artifact.submissionArtifact .Osaka 5007 checkProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3814 11 5007 checkProgram
    (by decide) (by rfl) (by rfl) (by decide)
def normalBlock : Block Artifact.submissionArtifact .Osaka 5024 normalProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3825 6 5024 normalProgram
    (by decide) (by rfl) (by rfl) (by decide)
def squareBlock : Block Artifact.submissionArtifact .Osaka 5036 squareProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3831 2 5036 squareProgram
    (by decide) (by rfl) (by rfl) (by decide)
def storeBlock : Block Artifact.submissionArtifact .Osaka 5040 storeProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3833 5 5040 storeProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem run_check (s : State) (mem : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions checkProgram (stateAt s mem 5007 ([pa,pb,dst,ret] ++ rest)) =
      some (stateAt s mem (if UInt256.isTrue (guard mem pa pb) then 5036 else 5024)
        ([pa,pb,dst,ret] ++ rest)) := by
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 9344 32 (by decide) (by decide) hact
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h5036 : (5036 : UInt256).toNat = 5036 := by decide
  have he5036 : (5036 : UInt256) = UInt256.ofNat 5036 := by decide
  by_cases hc : UInt256.isTrue (guard mem pa pb) <;>
    simp [checkProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
      hc4, hc5, hc6, hc7, ha, h9344, h5036, he5036, hcode, destSquare, ← guard_def, hc,
      State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

theorem run_normal (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions normalProgram (stateAt s mem 5024 rest) =
      some (stateAt s (storeWord mem 8928 (UInt256.ofNat 0)) 5040
        (UInt256.ofNat 4173 :: rest)) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 8928 32 (by decide) (by decide) hact
  have hd : (8928 : UInt256).toNat = 8928 := by decide
  have hp : (5040 : UInt256).toNat = 5040 := by decide
  have hep : (5040 : UInt256) = UInt256.ofNat 5040 := by decide
  have hv : (4173 : UInt256) = UInt256.ofNat 4173 := by decide
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := by decide
  simp [normalProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    storeWord, hc0, hc1, hc2, ha, hd, hp, hep, hv, hz, hcode, destStore,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

theorem run_square (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions squareProgram (stateAt s mem 5036 rest) =
      some (stateAt s mem 5040 (UInt256.ofNat 5049 :: rest)) := by
  have hv : (5049 : UInt256) = UInt256.ofNat 5049 := by decide
  simp [squareProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    show rest.length < 1024 by omega, hv, succ_ofNat_mod, ofNat_add_mod]

theorem run_store (s : State) (mem : ByteArray) (route : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions storeProgram (stateAt s mem 5040 (route :: rest)) =
      some (stateAt s (storeWord mem 9280 route) 4076 rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 9280 32 (by decide) (by decide) hact
  have hd : (9280 : UInt256).toNat = 9280 := by decide
  have hp : (4076 : UInt256).toNat = 4076 := by decide
  have hep : (4076 : UInt256) = UInt256.ofNat 4076 := by decide
  simp [storeProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    storeWord, hc0, hc1, hc2, ha, hd, hp, hep, hcode, destHeader,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

def selectedMemory (mem : ByteArray) (pa pb : UInt256) : ByteArray :=
  if UInt256.isTrue (guard mem pa pb) then storeWord mem 9280 (UInt256.ofNat 5049)
  else storeWord (storeWord mem 8928 (UInt256.ofNat 0)) 9280 (UInt256.ofNat 4173)

def gasSteps_select (s : State) (mem : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 296 ≤ s.activeWords.toNat)
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
    have sq := squareBlock.steps (EarlyCsub.environment (stateAt s mem 5036 args) hcode hfork hrun hnp) rfl
      (run_square s mem args hargs)
    have put := storeBlock.steps (EarlyCsub.environment (stateAt s mem 5040 (UInt256.ofNat 5049 :: args)) hcode hfork hrun hnp) rfl
      (run_store s mem (UInt256.ofNat 5049) args hargs hact hcode)
    simpa only [selectedMemory, if_pos hs] using check.trans (sq.trans put)
  · rw [if_neg hs] at check
    have normal := normalBlock.steps (EarlyCsub.environment (stateAt s mem 5024 args) hcode hfork hrun hnp) rfl
      (run_normal s mem args hargs hact hcode)
    have put := storeBlock.steps (EarlyCsub.environment (stateAt s (storeWord mem 8928 (UInt256.ofNat 0)) 5040 (UInt256.ofNat 4173 :: args)) hcode hfork hrun hnp) rfl
      (run_store s (storeWord mem 8928 (UInt256.ofNat 0)) (UInt256.ofNat 4173)
        args hargs hact hcode)
    simpa only [selectedMemory, if_neg hs] using check.trans (normal.trans put)

#print axioms gasSteps_select

end Challenge.Modexp.Submission.Proofs.Fast.SquareSelect
