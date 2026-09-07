import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

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
  { storedState input 5365 [] with
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

private theorem pc3750 : Artifact.submissionArtifact.instructionPC 3750 = 5327 := rfl
private theorem pc3751 : Artifact.submissionArtifact.instructionPC 3751 = 5328 := rfl
private theorem pc3752 : Artifact.submissionArtifact.instructionPC 3752 = 5329 := rfl
private theorem pc3753 : Artifact.submissionArtifact.instructionPC 3753 = 5330 := rfl
private theorem pc3754 : Artifact.submissionArtifact.instructionPC 3754 = 5331 := rfl
private theorem pc3755 : Artifact.submissionArtifact.instructionPC 3755 = 5332 := rfl
private theorem pc3756 : Artifact.submissionArtifact.instructionPC 3756 = 5333 := rfl
private theorem pc3757 : Artifact.submissionArtifact.instructionPC 3757 = 5334 := rfl
private theorem pc3758 : Artifact.submissionArtifact.instructionPC 3758 = 5335 := rfl
private theorem pc3759 : Artifact.submissionArtifact.instructionPC 3759 = 5336 := rfl
private theorem pc3760 : Artifact.submissionArtifact.instructionPC 3760 = 5339 := rfl
private theorem pc3761 : Artifact.submissionArtifact.instructionPC 3761 = 5340 := rfl
private theorem pc3762 : Artifact.submissionArtifact.instructionPC 3762 = 5361 := rfl
private theorem pc3763 : Artifact.submissionArtifact.instructionPC 3763 = 5362 := rfl
private theorem pc3764 : Artifact.submissionArtifact.instructionPC 3764 = 5363 := rfl
private theorem pc3765 : Artifact.submissionArtifact.instructionPC 3765 = 5364 := rfl
private theorem pc3766 : Artifact.submissionArtifact.instructionPC 3766 = 5365 := rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 340 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 183 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 3750 .JUMPDEST, opAt 3751 .POP, opAt 3752 .POP,
   opAt 3753 (.Swap ⟨4, by decide⟩), opAt 3754 .POP, opAt 3755 .POP,
   opAt 3756 .POP, opAt 3757 .POP, opAt 3758 .POP,
   pushAt 3759 2 340, opAt 3760 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5340 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc3750, pc3751, pc3752, pc3753, pc3754,
       pc3755, pc3756, pc3757, pc3758, pc3759, pc3760]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5340 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5340 = 340 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5339 [340, acc]) := by
  have a := soundS (opAt 3750 .JUMPDEST)
    (blockOfS _ (pcFactS input 3750 5327 _ (by norm_num) pc3750)
      (stepS_jumpdest input 5327 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 3751 .POP)
    (blockOfS _ (pcFactS input 3751 5328 _ (by norm_num) pc3751)
      (stepS_pop input 5328 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 3752 .POP)
    (blockOfS _ (pcFactS input 3752 5329 _ (by norm_num) pc3752)
      (stepS_pop input 5329 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 3753 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 3753 5330 _ (by norm_num) pc3753)
      (stepS_swap input 5330 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 3754 .POP)
    (blockOfS _ (pcFactS input 3754 5331 _ (by norm_num) pc3754)
      (stepS_pop input 5331 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 3755 .POP)
    (blockOfS _ (pcFactS input 3755 5332 _ (by norm_num) pc3755)
      (stepS_pop input 5332 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 3756 .POP)
    (blockOfS _ (pcFactS input 3756 5333 _ (by norm_num) pc3756)
      (stepS_pop input 5333 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 3757 .POP)
    (blockOfS _ (pcFactS input 3757 5334 _ (by norm_num) pc3757)
      (stepS_pop input 5334 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 3758 .POP)
    (blockOfS _ (pcFactS input 3758 5335 _ (by norm_num) pc3758)
      (stepS_pop input 5335 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 3759 2 340)
    (blockOfS _ (pcFactS input 3759 5336 _ (by norm_num) pc3759)
      (stepS_push input 5336 2 340 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 3760 .JUMPI)
      (blockOfS _ (pcFactS input 3760 5339 _ (by norm_num) pc3760)
        (stepS_jumpi_taken input 5339 340 340 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5340 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 3760 .JUMPI)
      (blockOfS _ (pcFactS input 3760 5339 _ (by norm_num) pc3760)
        (stepS_jumpi_fall input 5339 340 acc []
          (by simp) (by norm_num) hc)))

private theorem msizeDecoded (s : State)
    (hpc : s.pc =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3764))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) : s.decodedOp = some .MSIZE := by
  have hget : Artifact.submissionInstructions[3764]? = some (.op .MSIZE) := by
    rfl
  have hdecode := Artifact.submissionArtifact.decodeAt_op_index
    3764 .MSIZE hget (by decide) trivial
  have hpcNat : s.pc.toNat =
      Artifact.submissionArtifact.instructionPC 3764 := by
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Artifact.submissionArtifact.instructionPC_le_code_size 3764)
      (by change submissionBytecode.size < 2 ^ 256
          rw [referenceBytecode_size]
          decide))
  exact Artifact.submissionArtifact.state_decodedOp_of s 3764
    hcode hpcNat .MSIZE none hdecode (by rw [hfork]; decide)

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5340 []) (returnedState input) := by
  have a := soundS (pushAt 3761 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 3761 5340 _ (by norm_num) pc3761)
      (stepS_push input 5340 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 3762 0 0)
    (blockOfS _ (pcFactS input 3762 5361 _ (by norm_num) pc3762)
      (stepS_push0 input 5361 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5362 [0, paddedDigestWord]) = some (storedState input 5363 []) := by
    rfl
  have c := soundS (opAt 3763 .MSTORE)
    (blockOfS _ (pcFactS input 3763 5362 _ (by norm_num) pc3763) hc)
  have hop : (storedState input 5363 []).decodedOp = some .MSIZE :=
    msizeDecoded (storedState input 5363 []) (by rfl) (by rfl) (by rfl)
  have hd : GasSteps (storedState input 5363 [])
      (storedState input 5364 [32]) := by
    have hraw := Msize.step hop (by simp) (by rfl)
      (by exact deployAddress_not_precompile)
    exact GasSteps.cast hraw rfl (by
      simp [storedState, stS, initialState,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.word_toNat_ofNat])
  have he : Stepper.runInstr (.push 0 0) (storedState input 5364 [32]) =
      some (storedState input 5365 [0, 32]) := by rfl
  have e := soundS (pushAt 3765 0 0)
    (blockOfS _
      (show (storedState input 5364 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3765 from
          pcFactS input 3765 5364 [32] (by norm_num) pc3765) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5365 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 3766 .RETURN)
    (blockOfS _
      (show (storedState input 5365 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3766 from
          pcFactS input 3766 5365 [0, 32] (by norm_num) pc3766) hf)
  exact a.trans (b.trans (c.trans (hd.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5327 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans (gasSteps_return input)

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
