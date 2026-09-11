import Challenge.Modexp.Submission.Proofs.Fast.SquareTop

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareControls
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore SquareInit

def target (delta : UInt256) : UInt256 :=
  UInt256.ofNat 4499 - UInt256.ofNat 38 * UInt256.shiftRight delta (UInt256.ofNat 5)

def guardProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .ISZERO,
   .push 2 5294,
   .op .JUMPI]

def dispatchProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .push 1 5,
   .op .SHR,
   .push 1 38,
   .op .MUL,
   .push 2 4499,
   .op .SUB,
   .op .JUMP]

def lastProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MSTORE,
   .op .LT,
   .push 2 4488,
   .op .JUMP]

def muProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Swap ⟨0, by decide⟩),
   .op .POP]

theorem run_guard (s : State) (c ai pbi pa pb delta : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 5294 = true) :
    runInstructions guardProgram
      (framed s (UInt256.ofNat 5229) ([c,ai,pbi,pa,pb,delta] ++ rest)) =
    some (framed s (if UInt256.isTrue (UInt256.isZero delta) then UInt256.ofNat 5294 else UInt256.ofNat 5235)
      ([c,ai,pbi,pa,pb,delta] ++ rest)) := by
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  by_cases hcond : UInt256.isTrue (UInt256.isZero delta)
  all_goals simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc6, hc7, hc8, hcond, hjump, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch (s : State) (c ai pbi pa pb delta : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code (target delta).toNat = true) :
    runInstructions dispatchProgram
      (framed s (UInt256.ofNat 5282) ([c,ai,pbi,pa,pb,delta] ++ rest)) =
    some (framed s (target delta) ([c,ai,pbi,pa,pb,delta] ++ rest)) := by
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  simp only [target, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd] at hjump
  have h5 : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h38 : (38 : UInt256) = UInt256.ofNat 38 := by decide
  have h4499 : (4499 : UInt256) = UInt256.ofNat 4499 := by decide
  simp [dispatchProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, target, hc6, hc7, hc8, h5, h38, h4499, hjump,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_last (s : State) (mem : ByteArray) (c ai : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) (hact : 296 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4488 = true) :
    runInstructions lastProgram (stateAt s mem 5294 (c :: ai :: rest)) =
      some (stateAt s (storeWord mem 8224 (MachineState.readWord mem 8224+c)) 4488
        (UInt256.lt (MachineState.readWord mem 8224+c) c :: ai :: rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have ha := EarlyCsub.activeWords_fix s 8224 32 (by decide) (by decide) hact
  have haddr : (8224 : UInt256).toNat = 8224 := by decide
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, storeWord, hc2, hc3, hc4, hc5, ha, haddr, hjump, Nat.add_assoc,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_mu (s : State) (mem : ByteArray) (f ai : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1021) :
    runInstructions muProgram (stateAt s mem 4488 (f :: ai :: rest)) =
      some (stateAt s mem 4491 (f :: rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  simp [muProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, hc2, List.exchange, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod]

def guardBlock : Block Artifact.submissionArtifact .Osaka 5229 guardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3962 4 5229 guardProgram
    (by decide) (by rfl) (by rfl) (by decide)
def dispatchBlock : Block Artifact.submissionArtifact .Osaka 5282 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4006 8 5282 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)
def lastBlock : Block Artifact.submissionArtifact .Osaka 5294 lastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4014 11 5294 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)
def muBlock : Block Artifact.submissionArtifact .Osaka 4488 muProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3419 3 4488 muProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem target_index (i : Nat) (hi : i < 7) :
    target (UInt256.ofNat (32*(7-i))) = UInt256.ofNat (4157+38*(i+2)) := by
  interval_cases i <;> decide

theorem guard_index (i : Nat) (hi : i < 8) :
    UInt256.isTrue (UInt256.isZero (UInt256.ofNat (32*(7-i)))) ↔ i = 7 := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.SquareControls
