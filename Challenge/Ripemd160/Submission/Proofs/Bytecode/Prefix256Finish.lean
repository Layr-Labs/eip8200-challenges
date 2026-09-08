import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

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
  { storedState input 5242 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 4064 = 5187 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 4065 = 5188 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 4066 = 5189 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 4067 = 5190 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 4068 = 5191 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 4069 = 5192 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 4070 = 5193 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 4071 = 5194 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 4072 = 5195 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 4073 = 5196 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 4074 = 5199 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 4080 = 5208 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 4081 = 5209 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 4082 = 5211 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 4083 = 5212 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 4084 = 5215 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 4085 = 5216 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 4086 = 5237 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 4087 = 5238 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 4088 = 5239 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 4089 = 5241 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 4090 = 5242 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 364 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4064 .JUMPDEST, opAt 4065 .POP, opAt 4066 .POP,
   opAt 4067 (.Swap ⟨4, by decide⟩), opAt 4068 .POP, opAt 4069 .POP,
   opAt 4070 .POP, opAt 4071 .POP, opAt 4072 .POP,
   pushAt 4073 2 364, opAt 4074 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5200 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (fallbackState input) ↔ acc ≠ 0 := by
  rw [run_exit]
  by_cases hc : UInt256.isTrue acc
  · simp only [if_pos hc, true_iff]
    intro hz
    subst acc
    exact hc rfl
  · have hz : acc = 0 := by
      apply Word.word_ext
      change acc.toNat = 0
      exact not_not.mp hc
    have hstates : stS input 5200 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5205 = 364 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5199 [364, acc]) := by
  have a := soundS (opAt 4064 .JUMPDEST)
    (blockOfS _ (pcFactS input 4064 5187 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5187 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4065 .POP)
    (blockOfS _ (pcFactS input 4065 5188 _ (by norm_num) pc3751)
      (stepS_pop input 5188 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4066 .POP)
    (blockOfS _ (pcFactS input 4066 5189 _ (by norm_num) pc3752)
      (stepS_pop input 5189 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4067 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4067 5190 _ (by norm_num) pc3753)
      (stepS_swap input 5190 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4068 .POP)
    (blockOfS _ (pcFactS input 4068 5191 _ (by norm_num) pc3754)
      (stepS_pop input 5191 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4069 .POP)
    (blockOfS _ (pcFactS input 4069 5192 _ (by norm_num) pc3755)
      (stepS_pop input 5192 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4070 .POP)
    (blockOfS _ (pcFactS input 4070 5193 _ (by norm_num) pc3756)
      (stepS_pop input 5193 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4071 .POP)
    (blockOfS _ (pcFactS input 4071 5194 _ (by norm_num) pc3757)
      (stepS_pop input 5194 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4072 .POP)
    (blockOfS _ (pcFactS input 4072 5195 _ (by norm_num) pc3758)
      (stepS_pop input 5195 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4073 2 364)
    (blockOfS _ (pcFactS input 4073 5196 _ (by norm_num) pc3759)
      (stepS_push input 5196 2 364 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4074 .JUMPI)
      (blockOfS _ (pcFactS input 4074 5199 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5199 364 364 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5200 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4074 .JUMPI)
      (blockOfS _ (pcFactS input 4074 5199 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5199 364 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_size64_test (input : ByteArray) :
    GasSteps (stS input 5200 [])
      (stS input 5207 [5275,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4075 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4075 5200 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 5200 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4076 1 64)
    (blockOfS _ (pcFactS input 4076 5201 _ (by norm_num) (by rfl))
      (stepS_push input 5201 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4077 .EQ)
    (blockOfS _ (pcFactS input 4077 5203 _ (by norm_num) (by rfl))
      (stepS_eq input 5203 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4078 2 5270)
    (blockOfS _ (pcFactS input 4078 5204 _ (by norm_num) (by rfl))
      (stepS_push input 5204 2 5270
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_skip64 (input : ByteArray)
    (hsize : input.size = 128 ∨ input.size = 256) :
    GasSteps (stS input 5200 []) (stS input 5208 []) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rcases hsize with h | h <;> rw [h] <;> decide
  exact (gasSteps_size64_test input).trans
    (soundS (opAt 4079 .JUMPI)
      (blockOfS _ (pcFactS input 4079 5207 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 5207 5270
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5208 [])
      (stS input 5215 [5248,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4080 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4080 5208 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5208 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4081 1 128)
    (blockOfS _ (pcFactS input 4081 5209 _ (by norm_num) pc3762)
      (stepS_push input 5209 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4082 .EQ)
    (blockOfS _ (pcFactS input 4082 5211 _ (by norm_num) pc3763)
      (stepS_eq input 5211 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4083 2 5243)
    (blockOfS _ (pcFactS input 4083 5212 _ (by norm_num) pc3764)
      (stepS_push input 5212 2 5243
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5208 []) (stS input 5216 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4084 .JUMPI)
      (blockOfS _ (pcFactS input 4084 5215 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5215 5243
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5216 []) (returnedState input) := by
  have a := soundS (pushAt 4090 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4085 5216 _ (by norm_num) pc3766)
      (stepS_push input 5216 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4086 0 0)
    (blockOfS _ (pcFactS input 4086 5237 _ (by norm_num) pc3767)
      (stepS_push0 input 5237 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5238 [0, paddedDigestWord]) = some (storedState input 5239 []) := by
    rfl
  have c := soundS (opAt 4087 .MSTORE)
    (blockOfS _ (pcFactS input 4087 5238 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5239 []) =
      some (storedState input 5241 [32]) := by rfl
  have d := soundS (pushAt 4088 1 32)
    (blockOfS _
      (show (storedState input 5239 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4093 from
          pcFactS input 4088 5239 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5241 [32]) =
      some (storedState input 5242 [0, 32]) := by rfl
  have e := soundS (pushAt 4089 0 0)
    (blockOfS _
      (show (storedState input 5241 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4094 from
          pcFactS input 4089 5241 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5242 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4090 .RETURN)
    (blockOfS _
      (show (storedState input 5242 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4095 from
          pcFactS input 4090 5242 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_skip64 input (Or.inr hsize)).trans
      ((gasSteps_select256 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
