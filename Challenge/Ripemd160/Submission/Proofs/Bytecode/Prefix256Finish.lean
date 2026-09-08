import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar
open YulEvmCompiler

open private
  submissionInstructionsChunk0
  submissionInstructionsChunk1
  submissionInstructionsChunk2
  submissionInstructionsChunk3
  submissionInstructionsChunk4
  submissionInstructionsChunk5
  submissionInstructionsChunk6
  submissionInstructionsChunk7
  submissionInstructionsChunk8
  submissionInstructionsChunk9
  submissionInstructionsChunk10
  submissionInstructionsChunk11
  submissionInstructionsChunk12
  submissionInstructionsChunk13
  submissionInstructionsChunk14
  submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk17
  submissionInstructionsChunk18
  submissionInstructionsChunk19
  submissionInstructionsChunk20
  submissionInstructionsChunk0_length
  submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length
  submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length
  submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length
  submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length
  submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length
  submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length
  submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length
  submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  submissionInstructionsChunk17_length
  submissionInstructionsChunk18_length
  submissionInstructionsChunk19_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

def paddedDigestWord : UInt256 := 0xc6c53c46cf08de1c5375b15af8676a2d32ef528a

def paddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0xc6, 0xc5, 0x3c, 0x46, 0xcf, 0x08, 0xde, 0x1c, 0x53, 0x75,
  0xb1, 0x5a, 0xf8, 0x67, 0x6a, 0x2d, 0x32, 0xef, 0x52, 0x8a]

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def storedState (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { stS input pc stk with memory := answerMemory, activeWords := UInt256.ofNat 1 }

def returnedState (input : ByteArray) : State :=
  { storedState input 5235 [] with
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) :
    (returnedState input).hReturn = paddedDigest := answerMemory_read

@[simp] theorem returnedState_hReturn_size (input : ByteArray) :
    (returnedState input).hReturn.size = 32 := by
  rw [returnedState_hReturn, paddedDigest_size]

private def artifactPrefix : List Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++
    submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++
    submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++
    submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++
    submissionInstructionsChunk18 ++ submissionInstructionsChunk19

private def finishBefore : List Instr :=
  artifactPrefix ++ submissionInstructionsChunk20.take 61

private def finishSegment : List Instr :=
  (submissionInstructionsChunk20.drop 61).take 41

private def finishAfter : List Instr :=
  submissionInstructionsChunk20.drop 102

private theorem finishBefore_length : finishBefore.length = 4061 := by
  simp [finishBefore, artifactPrefix]

private theorem finishSegment_length : finishSegment.length = 41 := by decide

private theorem artifactChunk20_finish :
    submissionInstructionsChunk20 =
      submissionInstructionsChunk20.take 61 ++ finishSegment ++ finishAfter := by
  rfl

private theorem artifact_finish_split :
    Artifact.submissionArtifact.instructions =
      finishBefore ++ finishSegment ++ finishAfter := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      artifactPrefix ++ submissionInstructionsChunk20 := by
    simp only [Artifact.submissionInstructions, artifactPrefix, List.append_assoc]
  rw [hprefix]
  conv_lhs => rw [artifactChunk20_finish]
  simp only [finishBefore, List.append_assoc]

/-- The sole whole-artifact reduction; subsequent finish PCs use the certified
local segment and its instruction widths. -/
private theorem pc3750 : Artifact.submissionArtifact.instructionPC 4061 = 5180 := rfl

private theorem finish_instruction_pc (i : Nat) (hi : i ≤ finishSegment.length) :
    Artifact.submissionArtifact.instructionPC (4061 + i) =
      5180 + ArtifactByteLength.byteLength (finishSegment.take i) := by
  have hzero := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    finishBefore finishSegment finishAfter artifact_finish_split 0 (by omega)
  have hzero' : Artifact.submissionArtifact.instructionPC 4061 =
      (assembleBytes finishBefore).length := by
    simpa [finishBefore_length] using hzero
  have hbefore : (assembleBytes finishBefore).length = 5180 :=
    hzero'.symm.trans pc3750
  have h := ArtifactSegment.instructionPC_segment_of_bounds
    Artifact.submissionArtifact finishBefore finishSegment finishAfter 4061 5180
    artifact_finish_split finishBefore_length hbefore i hi
  simpa only [ArtifactByteLength.byteLength_eq_assemble] using h

/-- Shared PC certificate for the complete 64/128/256 finish region.  The only
whole-artifact PC reduction is `pc3750`; callers reduce this small local table. -/
theorem finish_instruction_pc_table (i : Nat) (hi : i ≤ 41) :
    Artifact.submissionArtifact.instructionPC (4061 + i) =
      [5180, 5181, 5182, 5183, 5184, 5185, 5186, 5187, 5188, 5189,
       5192, 5193, 5194, 5196, 5197, 5200, 5201, 5202, 5204, 5205,
       5208, 5209, 5230, 5231, 5232, 5234, 5235, 5236, 5237, 5258,
       5259, 5260, 5262, 5263, 5264, 5265, 5286, 5287, 5288, 5290,
       5291, 5292][i]! := by
  have hsegment : i ≤ finishSegment.length := by
    rw [finishSegment_length]
    exact hi
  rw [finish_instruction_pc i hsegment]
  interval_cases i <;> decide

private theorem pc3751 : Artifact.submissionArtifact.instructionPC 4062 = 5181 := by
  simpa using finish_instruction_pc_table 1 (by decide)
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 4063 = 5182 := by
  simpa using finish_instruction_pc_table 2 (by decide)
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 4064 = 5183 := by
  simpa using finish_instruction_pc_table 3 (by decide)
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 4065 = 5184 := by
  simpa using finish_instruction_pc_table 4 (by decide)
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 4066 = 5185 := by
  simpa using finish_instruction_pc_table 5 (by decide)
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 4067 = 5186 := by
  simpa using finish_instruction_pc_table 6 (by decide)
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 4068 = 5187 := by
  simpa using finish_instruction_pc_table 7 (by decide)
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 4069 = 5188 := by
  simpa using finish_instruction_pc_table 8 (by decide)
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 4070 = 5189 := by
  simpa using finish_instruction_pc_table 9 (by decide)
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 4071 = 5192 := by
  simpa using finish_instruction_pc_table 10 (by decide)
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 4077 = 5201 := by
  simpa using finish_instruction_pc_table 16 (by decide)
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 4078 = 5202 := by
  simpa using finish_instruction_pc_table 17 (by decide)
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 4079 = 5204 := by
  simpa using finish_instruction_pc_table 18 (by decide)
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 4080 = 5205 := by
  simpa using finish_instruction_pc_table 19 (by decide)
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 4081 = 5208 := by
  simpa using finish_instruction_pc_table 20 (by decide)
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 4082 = 5209 := by
  simpa using finish_instruction_pc_table 21 (by decide)
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 4083 = 5230 := by
  simpa using finish_instruction_pc_table 22 (by decide)
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 4084 = 5231 := by
  simpa using finish_instruction_pc_table 23 (by decide)
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 4085 = 5232 := by
  simpa using finish_instruction_pc_table 24 (by decide)
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 4086 = 5234 := by
  simpa using finish_instruction_pc_table 25 (by decide)
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 4087 = 5235 := by
  simpa using finish_instruction_pc_table 26 (by decide)

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 352 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 193 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4061 .JUMPDEST, opAt 4062 .POP, opAt 4063 .POP,
   opAt 4064 (.Swap ⟨4, by decide⟩), opAt 4065 .POP, opAt 4066 .POP,
   opAt 4067 .POP, opAt 4068 .POP, opAt 4069 .POP,
   pushAt 4070 2 352, opAt 4071 .JUMPI]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5180 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5192 [352, acc]) := by
  have a := soundS (opAt 4061 .JUMPDEST)
    (blockOfS _ (pcFactS input 4061 5180 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5180 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4062 .POP)
    (blockOfS _ (pcFactS input 4062 5181 _ (by norm_num) pc3751)
      (stepS_pop input 5181 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4063 .POP)
    (blockOfS _ (pcFactS input 4063 5182 _ (by norm_num) pc3752)
      (stepS_pop input 5182 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4064 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4064 5183 _ (by norm_num) pc3753)
      (stepS_swap input 5183 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4065 .POP)
    (blockOfS _ (pcFactS input 4065 5184 _ (by norm_num) pc3754)
      (stepS_pop input 5184 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4066 .POP)
    (blockOfS _ (pcFactS input 4066 5185 _ (by norm_num) pc3755)
      (stepS_pop input 5185 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4067 .POP)
    (blockOfS _ (pcFactS input 4067 5186 _ (by norm_num) pc3756)
      (stepS_pop input 5186 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4068 .POP)
    (blockOfS _ (pcFactS input 4068 5187 _ (by norm_num) pc3757)
      (stepS_pop input 5187 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4069 .POP)
    (blockOfS _ (pcFactS input 4069 5188 _ (by norm_num) pc3758)
      (stepS_pop input 5188 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4070 2 352)
    (blockOfS _ (pcFactS input 4070 5189 _ (by norm_num) pc3759)
      (stepS_push input 5189 2 352 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5180 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4071 .JUMPI)
      (blockOfS _ (pcFactS input 4071 5192 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5192 352 352 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5180 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5193 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4071 .JUMPI)
      (blockOfS _ (pcFactS input 4071 5192 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5192 352 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_size64_test (input : ByteArray) :
    GasSteps (stS input 5193 [])
      (stS input 5200 [5264,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4072 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4072 5193 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 5193 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4073 1 64)
    (blockOfS _ (pcFactS input 4073 5194 _ (by norm_num) (by rfl))
      (stepS_push input 5194 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4074 .EQ)
    (blockOfS _ (pcFactS input 4074 5196 _ (by norm_num) (by rfl))
      (stepS_eq input 5196 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4075 2 5264)
    (blockOfS _ (pcFactS input 4075 5197 _ (by norm_num) (by rfl))
      (stepS_push input 5197 2 5264
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_skip64 (input : ByteArray)
    (hsize : input.size = 128 ∨ input.size = 256) :
    GasSteps (stS input 5193 []) (stS input 5201 []) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rcases hsize with h | h <;> rw [h] <;> decide
  exact (gasSteps_size64_test input).trans
    (soundS (opAt 4076 .JUMPI)
      (blockOfS _ (pcFactS input 4076 5200 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 5200 5264
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5201 [])
      (stS input 5208 [5236,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4077 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4077 5201 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5201 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4078 1 128)
    (blockOfS _ (pcFactS input 4078 5202 _ (by norm_num) pc3762)
      (stepS_push input 5202 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4079 .EQ)
    (blockOfS _ (pcFactS input 4079 5204 _ (by norm_num) pc3763)
      (stepS_eq input 5204 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4080 2 5236)
    (blockOfS _ (pcFactS input 4080 5205 _ (by norm_num) pc3764)
      (stepS_push input 5205 2 5236
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5201 []) (stS input 5209 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4081 .JUMPI)
      (blockOfS _ (pcFactS input 4081 5208 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5208 5236
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5209 []) (returnedState input) := by
  have a := soundS (pushAt 4082 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4082 5209 _ (by norm_num) pc3766)
      (stepS_push input 5209 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4083 0 0)
    (blockOfS _ (pcFactS input 4083 5230 _ (by norm_num) pc3767)
      (stepS_push0 input 5230 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5231 [0, paddedDigestWord]) = some (storedState input 5232 []) := by
    rfl
  have c := soundS (opAt 4084 .MSTORE)
    (blockOfS _ (pcFactS input 4084 5231 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5232 []) =
      some (storedState input 5234 [32]) := by rfl
  have d := soundS (pushAt 4085 1 32)
    (blockOfS _
      (show (storedState input 5232 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4085 from
          pcFactS input 4085 5232 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5234 [32]) =
      some (storedState input 5235 [0, 32]) := by rfl
  have e := soundS (pushAt 4086 0 0)
    (blockOfS _
      (show (storedState input 5234 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4086 from
          pcFactS input 4086 5234 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5235 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4087 .RETURN)
    (blockOfS _
      (show (storedState input 5235 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4087 from
          pcFactS input 4087 5235 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5180 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_skip64 input (Or.inr hsize)).trans
      ((gasSteps_select256 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
