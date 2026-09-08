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
  { storedState input 5247 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 4069 = 5192 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 4070 = 5193 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 4071 = 5194 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 4072 = 5195 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 4073 = 5196 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 4074 = 5197 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 4075 = 5198 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 4076 = 5199 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 4077 = 5200 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 4078 = 5201 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 4079 = 5204 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 4085 = 5213 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 4086 = 5214 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 4087 = 5216 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 4088 = 5217 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 4089 = 5220 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 4090 = 5221 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 4091 = 5242 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 4092 = 5243 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 4093 = 5244 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 4094 = 5246 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 4095 = 5247 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 364 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4069 .JUMPDEST, opAt 4070 .POP, opAt 4071 .POP,
   opAt 4072 (.Swap ⟨4, by decide⟩), opAt 4073 .POP, opAt 4074 .POP,
   opAt 4075 .POP, opAt 4076 .POP, opAt 4077 .POP,
   pushAt 4078 2 364, opAt 4079 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5205 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5205 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5205 = 364 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5204 [364, acc]) := by
  have a := soundS (opAt 4069 .JUMPDEST)
    (blockOfS _ (pcFactS input 4069 5192 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5192 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4070 .POP)
    (blockOfS _ (pcFactS input 4070 5193 _ (by norm_num) pc3751)
      (stepS_pop input 5193 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4071 .POP)
    (blockOfS _ (pcFactS input 4071 5194 _ (by norm_num) pc3752)
      (stepS_pop input 5194 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4072 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4072 5195 _ (by norm_num) pc3753)
      (stepS_swap input 5195 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4073 .POP)
    (blockOfS _ (pcFactS input 4073 5196 _ (by norm_num) pc3754)
      (stepS_pop input 5196 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4074 .POP)
    (blockOfS _ (pcFactS input 4074 5197 _ (by norm_num) pc3755)
      (stepS_pop input 5197 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4075 .POP)
    (blockOfS _ (pcFactS input 4075 5198 _ (by norm_num) pc3756)
      (stepS_pop input 5198 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4076 .POP)
    (blockOfS _ (pcFactS input 4076 5199 _ (by norm_num) pc3757)
      (stepS_pop input 5199 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4077 .POP)
    (blockOfS _ (pcFactS input 4077 5200 _ (by norm_num) pc3758)
      (stepS_pop input 5200 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4078 2 364)
    (blockOfS _ (pcFactS input 4078 5201 _ (by norm_num) pc3759)
      (stepS_push input 5201 2 364 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4079 .JUMPI)
      (blockOfS _ (pcFactS input 4079 5204 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5204 364 364 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5205 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4079 .JUMPI)
      (blockOfS _ (pcFactS input 4079 5204 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5204 364 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_size64_test (input : ByteArray) :
    GasSteps (stS input 5205 [])
      (stS input 5212 [5275,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4080 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4080 5205 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 5205 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4081 1 64)
    (blockOfS _ (pcFactS input 4081 5206 _ (by norm_num) (by rfl))
      (stepS_push input 5206 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4082 .EQ)
    (blockOfS _ (pcFactS input 4082 5208 _ (by norm_num) (by rfl))
      (stepS_eq input 5208 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4083 2 5275)
    (blockOfS _ (pcFactS input 4083 5209 _ (by norm_num) (by rfl))
      (stepS_push input 5209 2 5275
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_skip64 (input : ByteArray)
    (hsize : input.size = 128 ∨ input.size = 256) :
    GasSteps (stS input 5205 []) (stS input 5213 []) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rcases hsize with h | h <;> rw [h] <;> decide
  exact (gasSteps_size64_test input).trans
    (soundS (opAt 4084 .JUMPI)
      (blockOfS _ (pcFactS input 4084 5212 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 5212 5275
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5213 [])
      (stS input 5220 [5248,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4085 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4085 5213 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5213 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4086 1 128)
    (blockOfS _ (pcFactS input 4086 5214 _ (by norm_num) pc3762)
      (stepS_push input 5214 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4087 .EQ)
    (blockOfS _ (pcFactS input 4087 5216 _ (by norm_num) pc3763)
      (stepS_eq input 5216 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4088 2 5248)
    (blockOfS _ (pcFactS input 4088 5217 _ (by norm_num) pc3764)
      (stepS_push input 5217 2 5248
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5213 []) (stS input 5221 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4089 .JUMPI)
      (blockOfS _ (pcFactS input 4089 5220 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5220 5248
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5221 []) (returnedState input) := by
  have a := soundS (pushAt 4090 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4090 5221 _ (by norm_num) pc3766)
      (stepS_push input 5221 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4091 0 0)
    (blockOfS _ (pcFactS input 4091 5242 _ (by norm_num) pc3767)
      (stepS_push0 input 5242 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5243 [0, paddedDigestWord]) = some (storedState input 5244 []) := by
    rfl
  have c := soundS (opAt 4092 .MSTORE)
    (blockOfS _ (pcFactS input 4092 5243 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5244 []) =
      some (storedState input 5246 [32]) := by rfl
  have d := soundS (pushAt 4093 1 32)
    (blockOfS _
      (show (storedState input 5244 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4093 from
          pcFactS input 4093 5244 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5246 [32]) =
      some (storedState input 5247 [0, 32]) := by rfl
  have e := soundS (pushAt 4094 0 0)
    (blockOfS _
      (show (storedState input 5246 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4094 from
          pcFactS input 4094 5246 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5247 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4095 .RETURN)
    (blockOfS _
      (show (storedState input 5247 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4095 from
          pcFactS input 4095 5247 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_skip64 input (Or.inr hsize)).trans
      ((gasSteps_select256 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
