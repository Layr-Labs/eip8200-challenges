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
  { storedState input 5330 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 3761 = 5283 := rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 3762 = 5284 := rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 3763 = 5285 := rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 3764 = 5286 := rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 3765 = 5287 := rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 3766 = 5288 := rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 3767 = 5289 := rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 3768 = 5290 := rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 3769 = 5291 := rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 3770 = 5292 := rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 3771 = 5295 := rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 3772 = 5296 := rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 3773 = 5297 := rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 3774 = 5299 := rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 3775 = 5300 := rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 3776 = 5303 := rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 3777 = 5304 := rfl
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 3778 = 5325 := rfl
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 3779 = 5326 := rfl
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 3780 = 5327 := rfl
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 3781 = 5329 := rfl
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 3782 = 5330 := rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 346 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 188 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 3761 .JUMPDEST, opAt 3762 .POP, opAt 3763 .POP,
   opAt 3764 (.Swap ⟨4, by decide⟩), opAt 3765 .POP, opAt 3766 .POP,
   opAt 3767 .POP, opAt 3768 .POP, opAt 3769 .POP,
   pushAt 3770 2 346, opAt 3771 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5296 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5296 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5296 = 346 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5295 [346, acc]) := by
  have a := soundS (opAt 3761 .JUMPDEST)
    (blockOfS _ (pcFactS input 3761 5283 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5283 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 3762 .POP)
    (blockOfS _ (pcFactS input 3762 5284 _ (by norm_num) pc3751)
      (stepS_pop input 5284 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 3763 .POP)
    (blockOfS _ (pcFactS input 3763 5285 _ (by norm_num) pc3752)
      (stepS_pop input 5285 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 3764 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 3764 5286 _ (by norm_num) pc3753)
      (stepS_swap input 5286 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 3765 .POP)
    (blockOfS _ (pcFactS input 3765 5287 _ (by norm_num) pc3754)
      (stepS_pop input 5287 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 3766 .POP)
    (blockOfS _ (pcFactS input 3766 5288 _ (by norm_num) pc3755)
      (stepS_pop input 5288 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 3767 .POP)
    (blockOfS _ (pcFactS input 3767 5289 _ (by norm_num) pc3756)
      (stepS_pop input 5289 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 3768 .POP)
    (blockOfS _ (pcFactS input 3768 5290 _ (by norm_num) pc3757)
      (stepS_pop input 5290 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 3769 .POP)
    (blockOfS _ (pcFactS input 3769 5291 _ (by norm_num) pc3758)
      (stepS_pop input 5291 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 3770 2 346)
    (blockOfS _ (pcFactS input 3770 5292 _ (by norm_num) pc3759)
      (stepS_push input 5292 2 346 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 3771 .JUMPI)
      (blockOfS _ (pcFactS input 3771 5295 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5295 346 346 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5296 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 3771 .JUMPI)
      (blockOfS _ (pcFactS input 3771 5295 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5295 346 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5296 [])
      (stS input 5303 [5331,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 3772 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 3772 5296 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5296 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 3773 1 128)
    (blockOfS _ (pcFactS input 3773 5297 _ (by norm_num) pc3762)
      (stepS_push input 5297 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 3774 .EQ)
    (blockOfS _ (pcFactS input 3774 5299 _ (by norm_num) pc3763)
      (stepS_eq input 5299 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 3775 2 5331)
    (blockOfS _ (pcFactS input 3775 5300 _ (by norm_num) pc3764)
      (stepS_push input 5300 2 5331
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5296 []) (stS input 5304 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 3776 .JUMPI)
      (blockOfS _ (pcFactS input 3776 5303 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5303 5331
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5304 []) (returnedState input) := by
  have a := soundS (pushAt 3777 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 3777 5304 _ (by norm_num) pc3766)
      (stepS_push input 5304 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 3778 0 0)
    (blockOfS _ (pcFactS input 3778 5325 _ (by norm_num) pc3767)
      (stepS_push0 input 5325 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5326 [0, paddedDigestWord]) = some (storedState input 5327 []) := by
    rfl
  have c := soundS (opAt 3779 .MSTORE)
    (blockOfS _ (pcFactS input 3779 5326 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5327 []) =
      some (storedState input 5329 [32]) := by rfl
  have d := soundS (pushAt 3780 1 32)
    (blockOfS _
      (show (storedState input 5327 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3780 from
          pcFactS input 3780 5327 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5329 [32]) =
      some (storedState input 5330 [0, 32]) := by rfl
  have e := soundS (pushAt 3781 0 0)
    (blockOfS _
      (show (storedState input 5329 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3781 from
          pcFactS input 3781 5329 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5330 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 3782 .RETURN)
    (blockOfS _
      (show (storedState input 5330 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3782 from
          pcFactS input 3782 5330 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select256 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
