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
  { storedState input 5321 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 4044 = 5274 := rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 4045 = 5275 := rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 4046 = 5276 := rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 4047 = 5277 := rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 4048 = 5278 := rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 4049 = 5279 := rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 4050 = 5280 := rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 4051 = 5281 := rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 4052 = 5282 := rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 4053 = 5283 := rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 4054 = 5286 := rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 4055 = 5287 := rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 4056 = 5288 := rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 4057 = 5290 := rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 4058 = 5291 := rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 4059 = 5294 := rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 4060 = 5295 := rfl
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 4061 = 5316 := rfl
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 4062 = 5317 := rfl
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 4063 = 5318 := rfl
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 4064 = 5320 := rfl
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 4065 = 5321 := rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 346 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 188 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4044 .JUMPDEST, opAt 4045 .POP, opAt 4046 .POP,
   opAt 4047 (.Swap ⟨4, by decide⟩), opAt 4048 .POP, opAt 4049 .POP,
   opAt 4050 .POP, opAt 4051 .POP, opAt 4052 .POP,
   pushAt 4053 2 346, opAt 4054 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5287 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5287 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5287 = 346 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5286 [346, acc]) := by
  have a := soundS (opAt 4044 .JUMPDEST)
    (blockOfS _ (pcFactS input 4044 5274 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5274 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4045 .POP)
    (blockOfS _ (pcFactS input 4045 5275 _ (by norm_num) pc3751)
      (stepS_pop input 5275 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4046 .POP)
    (blockOfS _ (pcFactS input 4046 5276 _ (by norm_num) pc3752)
      (stepS_pop input 5276 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4047 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4047 5277 _ (by norm_num) pc3753)
      (stepS_swap input 5277 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4048 .POP)
    (blockOfS _ (pcFactS input 4048 5278 _ (by norm_num) pc3754)
      (stepS_pop input 5278 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4049 .POP)
    (blockOfS _ (pcFactS input 4049 5279 _ (by norm_num) pc3755)
      (stepS_pop input 5279 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4050 .POP)
    (blockOfS _ (pcFactS input 4050 5280 _ (by norm_num) pc3756)
      (stepS_pop input 5280 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4051 .POP)
    (blockOfS _ (pcFactS input 4051 5281 _ (by norm_num) pc3757)
      (stepS_pop input 5281 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4052 .POP)
    (blockOfS _ (pcFactS input 4052 5282 _ (by norm_num) pc3758)
      (stepS_pop input 5282 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4053 2 346)
    (blockOfS _ (pcFactS input 4053 5283 _ (by norm_num) pc3759)
      (stepS_push input 5283 2 346 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4054 .JUMPI)
      (blockOfS _ (pcFactS input 4054 5286 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5286 346 346 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5287 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4054 .JUMPI)
      (blockOfS _ (pcFactS input 4054 5286 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5286 346 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5287 [])
      (stS input 5294 [5322,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4055 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4055 5287 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5287 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4056 1 128)
    (blockOfS _ (pcFactS input 4056 5288 _ (by norm_num) pc3762)
      (stepS_push input 5288 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4057 .EQ)
    (blockOfS _ (pcFactS input 4057 5290 _ (by norm_num) pc3763)
      (stepS_eq input 5290 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4058 2 5322)
    (blockOfS _ (pcFactS input 4058 5291 _ (by norm_num) pc3764)
      (stepS_push input 5291 2 5322
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5287 []) (stS input 5295 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4059 .JUMPI)
      (blockOfS _ (pcFactS input 4059 5294 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5294 5322
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5295 []) (returnedState input) := by
  have a := soundS (pushAt 4060 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4060 5295 _ (by norm_num) pc3766)
      (stepS_push input 5295 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4061 0 0)
    (blockOfS _ (pcFactS input 4061 5316 _ (by norm_num) pc3767)
      (stepS_push0 input 5316 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5317 [0, paddedDigestWord]) = some (storedState input 5318 []) := by
    rfl
  have c := soundS (opAt 4062 .MSTORE)
    (blockOfS _ (pcFactS input 4062 5317 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5318 []) =
      some (storedState input 5320 [32]) := by rfl
  have d := soundS (pushAt 4063 1 32)
    (blockOfS _
      (show (storedState input 5318 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4063 from
          pcFactS input 4063 5318 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5320 [32]) =
      some (storedState input 5321 [0, 32]) := by rfl
  have e := soundS (pushAt 4064 0 0)
    (blockOfS _
      (show (storedState input 5320 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4064 from
          pcFactS input 4064 5320 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5321 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4065 .RETURN)
    (blockOfS _
      (show (storedState input 5321 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4065 from
          pcFactS input 4065 5321 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5274 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select256 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
