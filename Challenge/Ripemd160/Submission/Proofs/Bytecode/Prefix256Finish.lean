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
  { storedState input 5306 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 4534 = 5251 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 4535 = 5252 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 4536 = 5253 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 4537 = 5254 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 4538 = 5255 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 4539 = 5256 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 4540 = 5257 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 4541 = 5258 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 4542 = 5259 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 4543 = 5260 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 4544 = 5263 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 4550 = 5272 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 4551 = 5273 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 4552 = 5275 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 4553 = 5276 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 4554 = 5279 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 4555 = 5280 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3767 : Artifact.submissionArtifact.instructionPC 4556 = 5301 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3768 : Artifact.submissionArtifact.instructionPC 4557 = 5302 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3769 : Artifact.submissionArtifact.instructionPC 4558 = 5303 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3770 : Artifact.submissionArtifact.instructionPC 4559 = 5305 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3771 : Artifact.submissionArtifact.instructionPC 4560 = 5306 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 364 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4534 .JUMPDEST, opAt 4535 .POP, opAt 4536 .POP,
   opAt 4537 (.Swap ⟨4, by decide⟩), opAt 4538 .POP, opAt 4539 .POP,
   opAt 4540 .POP, opAt 4541 .POP, opAt 4542 .POP,
   pushAt 4543 2 364, opAt 4544 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5264 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5264 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5264 = 364 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5263 [364, acc]) := by
  have a := soundS (opAt 4534 .JUMPDEST)
    (blockOfS _ (pcFactS input 4534 5251 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5251 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4535 .POP)
    (blockOfS _ (pcFactS input 4535 5252 _ (by norm_num) pc3751)
      (stepS_pop input 5252 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4536 .POP)
    (blockOfS _ (pcFactS input 4536 5253 _ (by norm_num) pc3752)
      (stepS_pop input 5253 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4537 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4537 5254 _ (by norm_num) pc3753)
      (stepS_swap input 5254 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4538 .POP)
    (blockOfS _ (pcFactS input 4538 5255 _ (by norm_num) pc3754)
      (stepS_pop input 5255 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4539 .POP)
    (blockOfS _ (pcFactS input 4539 5256 _ (by norm_num) pc3755)
      (stepS_pop input 5256 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4540 .POP)
    (blockOfS _ (pcFactS input 4540 5257 _ (by norm_num) pc3756)
      (stepS_pop input 5257 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4541 .POP)
    (blockOfS _ (pcFactS input 4541 5258 _ (by norm_num) pc3757)
      (stepS_pop input 5258 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4542 .POP)
    (blockOfS _ (pcFactS input 4542 5259 _ (by norm_num) pc3758)
      (stepS_pop input 5259 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4543 2 364)
    (blockOfS _ (pcFactS input 4543 5260 _ (by norm_num) pc3759)
      (stepS_push input 5260 2 364 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4544 .JUMPI)
      (blockOfS _ (pcFactS input 4544 5263 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5263 364 364 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5264 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4544 .JUMPI)
      (blockOfS _ (pcFactS input 4544 5263 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5263 364 acc []
          (by simp) (by norm_num) hc)))

private def gasSteps_size64_test (input : ByteArray) :
    GasSteps (stS input 5264 [])
      (stS input 5271 [5335,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4545 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4545 5264 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 5264 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4546 1 64)
    (blockOfS _ (pcFactS input 4546 5265 _ (by norm_num) (by rfl))
      (stepS_push input 5265 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4547 .EQ)
    (blockOfS _ (pcFactS input 4547 5267 _ (by norm_num) (by rfl))
      (stepS_eq input 5267 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4548 2 5335)
    (blockOfS _ (pcFactS input 4548 5268 _ (by norm_num) (by rfl))
      (stepS_push input 5268 2 5335
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_skip64 (input : ByteArray)
    (hsize : input.size = 128 ∨ input.size = 256) :
    GasSteps (stS input 5264 []) (stS input 5272 []) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rcases hsize with h | h <;> rw [h] <;> decide
  exact (gasSteps_size64_test input).trans
    (soundS (opAt 4549 .JUMPI)
      (blockOfS _ (pcFactS input 4549 5271 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 5271 5335
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5272 [])
      (stS input 5279 [5307,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4550 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4550 5272 _ (by norm_num) pc3761)
      (stepS_calldatasize input 5272 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4551 1 128)
    (blockOfS _ (pcFactS input 4551 5273 _ (by norm_num) pc3762)
      (stepS_push input 5273 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4552 .EQ)
    (blockOfS _ (pcFactS input 4552 5275 _ (by norm_num) pc3763)
      (stepS_eq input 5275 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4553 2 5307)
    (blockOfS _ (pcFactS input 4553 5276 _ (by norm_num) pc3764)
      (stepS_push input 5276 2 5307
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select256 (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (stS input 5272 []) (stS input 5280 []) := by
  have hc : ¬ UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4554 .JUMPI)
      (blockOfS _ (pcFactS input 4554 5279 _ (by norm_num) pc3765)
        (stepS_jumpi_fall input 5279 5307
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5280 []) (returnedState input) := by
  have a := soundS (pushAt 4555 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4555 5280 _ (by norm_num) pc3766)
      (stepS_push input 5280 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4556 0 0)
    (blockOfS _ (pcFactS input 4556 5301 _ (by norm_num) pc3767)
      (stepS_push0 input 5301 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5302 [0, paddedDigestWord]) = some (storedState input 5303 []) := by
    rfl
  have c := soundS (opAt 4557 .MSTORE)
    (blockOfS _ (pcFactS input 4557 5302 _ (by norm_num) pc3768) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5303 []) =
      some (storedState input 5305 [32]) := by rfl
  have d := soundS (pushAt 4558 1 32)
    (blockOfS _
      (show (storedState input 5303 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4558 from
          pcFactS input 4558 5303 [] (by norm_num) pc3769) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5305 [32]) =
      some (storedState input 5306 [0, 32]) := by rfl
  have e := soundS (pushAt 4559 0 0)
    (blockOfS _
      (show (storedState input 5305 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4559 from
          pcFactS input 4559 5305 [32] (by norm_num) pc3770) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5306 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4560 .RETURN)
    (blockOfS _
      (show (storedState input 5306 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4560 from
          pcFactS input 4560 5306 [0, 32] (by norm_num) pc3771) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 256) (heq : acc = 0) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_skip64 input (Or.inr hsize)).trans
      ((gasSteps_select256 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
