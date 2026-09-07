import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

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
  { storedState input 5307 [] with
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

private theorem pc4039 : Artifact.submissionArtifact.instructionPC 4039 = 5268 := rfl
private theorem pc4040 : Artifact.submissionArtifact.instructionPC 4040 = 5269 := rfl
private theorem pc4041 : Artifact.submissionArtifact.instructionPC 4041 = 5270 := rfl
private theorem pc4042 : Artifact.submissionArtifact.instructionPC 4042 = 5271 := rfl
private theorem pc4043 : Artifact.submissionArtifact.instructionPC 4043 = 5272 := rfl
private theorem pc4044 : Artifact.submissionArtifact.instructionPC 4044 = 5273 := rfl
private theorem pc4045 : Artifact.submissionArtifact.instructionPC 4045 = 5274 := rfl
private theorem pc4046 : Artifact.submissionArtifact.instructionPC 4046 = 5275 := rfl
private theorem pc4047 : Artifact.submissionArtifact.instructionPC 4047 = 5276 := rfl
private theorem pc4048 : Artifact.submissionArtifact.instructionPC 4048 = 5277 := rfl
private theorem pc4049 : Artifact.submissionArtifact.instructionPC 4049 = 5280 := rfl
private theorem pc4050 : Artifact.submissionArtifact.instructionPC 4050 = 5281 := rfl
private theorem pc4051 : Artifact.submissionArtifact.instructionPC 4051 = 5302 := rfl
private theorem pc4052 : Artifact.submissionArtifact.instructionPC 4052 = 5303 := rfl
private theorem pc4053 : Artifact.submissionArtifact.instructionPC 4053 = 5304 := rfl
private theorem pc4054 : Artifact.submissionArtifact.instructionPC 4054 = 5306 := rfl
private theorem pc4055 : Artifact.submissionArtifact.instructionPC 4055 = 5307 := rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 340 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 183 (by rfl)

attribute [local simp] fallbackDest Challenge.Ripemd160.initialState_stack

/-- The cleanup and branch, ending before the digest store. -/
def exitPath : List Located :=
  [opAt 4039 .JUMPDEST, opAt 4040 .POP, opAt 4041 .POP,
   opAt 4042 (.Swap ⟨4, by decide⟩), opAt 4043 .POP, opAt 4044 .POP,
   opAt 4045 .POP, opAt 4046 .POP, opAt 4047 .POP,
   pushAt 4048 2 340, opAt 4049 .JUMPI]

theorem run_exit (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8]) =
      some (if UInt256.isTrue acc then fallbackState input else stS input 5281 []) := by
  by_cases hc : UInt256.isTrue acc <;>
    simp (config := { maxSteps := 400000 })
      [exitPath, opAt, pushAt, stS, fallbackState, atPC, List.exchange, hc,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
       Word.word_toNat_ofNat, pc4039, pc4040, pc4041, pc4042, pc4043,
       pc4044, pc4045, pc4046, pc4047, pc4048, pc4049]

theorem run_exit_fallback_iff (input : ByteArray) (sv ov acc : UInt256) :
    run exitPath (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8]) =
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
    have hstates : stS input 5281 [] ≠ fallbackState input := by
      intro h
      have hp := congrArg (fun s : State => s.pc.toNat) h
      change 5281 = 340 at hp
      omega
    rw [if_neg hc]
    simp [hz, hstates]

/-- Remove the counters and constants; keep only the branch condition. -/
def gasSteps_cleanup (input : ByteArray) (sv ov acc : UInt256) :
    GasSteps (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5280 [340, acc]) := by
  have a := soundS (opAt 4039 .JUMPDEST)
    (blockOfS _ (pcFactS input 4039 5268 _ (by norm_num) pc4039)
      (stepS_jumpdest input 5268 [sv, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have b := soundS (opAt 4040 .POP)
    (blockOfS _ (pcFactS input 4040 5269 _ (by norm_num) pc4040)
      (stepS_pop input 5269 sv [ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have c := soundS (opAt 4041 .POP)
    (blockOfS _ (pcFactS input 4041 5270 _ (by norm_num) pc4041)
      (stepS_pop input 5270 ov [acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 4042 (.Swap ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 4042 5271 _ (by norm_num) pc4042)
      (stepS_swap input 5271 4 (by decide) [acc, P7, M, m7, P, m8]
        [m8, P7, M, m7, P, acc] (by rfl) (by simp) (by norm_num)))
  have e := soundS (opAt 4043 .POP)
    (blockOfS _ (pcFactS input 4043 5272 _ (by norm_num) pc4043)
      (stepS_pop input 5272 m8 [P7, M, m7, P, acc] (by simp) (by norm_num)))
  have f := soundS (opAt 4044 .POP)
    (blockOfS _ (pcFactS input 4044 5273 _ (by norm_num) pc4044)
      (stepS_pop input 5273 P7 [M, m7, P, acc] (by simp) (by norm_num)))
  have g := soundS (opAt 4045 .POP)
    (blockOfS _ (pcFactS input 4045 5274 _ (by norm_num) pc4045)
      (stepS_pop input 5274 M [m7, P, acc] (by simp) (by norm_num)))
  have h := soundS (opAt 4046 .POP)
    (blockOfS _ (pcFactS input 4046 5275 _ (by norm_num) pc4046)
      (stepS_pop input 5275 m7 [P, acc] (by simp) (by norm_num)))
  have i := soundS (opAt 4047 .POP)
    (blockOfS _ (pcFactS input 4047 5276 _ (by norm_num) pc4047)
      (stepS_pop input 5276 P [acc] (by simp) (by norm_num)))
  have j := soundS (pushAt 4048 2 340)
    (blockOfS _ (pcFactS input 4048 5277 _ (by norm_num) pc4048)
      (stepS_push input 5277 2 340 [acc]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans
    (f.trans (g.trans (h.trans (i.trans j))))))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) := by
  have hc : UInt256.isTrue acc := by
    intro hz
    apply hne
    apply Word.word_ext
    change acc.toNat = 0
    exact hz
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4049 .JUMPI)
      (blockOfS _ (pcFactS input 4049 5280 _ (by norm_num) pc4049)
        (stepS_jumpi_taken input 5280 340 340 acc []
          (by simp) (by norm_num) rfl hc fallbackDest)))

def gasSteps_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5281 []) := by
  have hc : ¬ UInt256.isTrue acc := by
    subst acc
    exact fun h => h rfl
  exact (gasSteps_cleanup input sv ov acc).trans
    (soundS (opAt 4049 .JUMPI)
      (blockOfS _ (pcFactS input 4049 5280 _ (by norm_num) pc4049)
        (stepS_jumpi_fall input 5280 340 acc []
          (by simp) (by norm_num) hc)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5281 []) (returnedState input) := by
  have a := soundS (pushAt 4050 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4050 5281 _ (by norm_num) pc4050)
      (stepS_push input 5281 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have b := soundS (pushAt 4051 0 0)
    (blockOfS _ (pcFactS input 4051 5302 _ (by norm_num) pc4051)
      (stepS_push0 input 5302 [paddedDigestWord] (by simp) (by norm_num)))
  have hc : Stepper.runInstr (.op .MSTORE)
      (stS input 5303 [0, paddedDigestWord]) = some (storedState input 5304 []) := by
    rfl
  have c := soundS (opAt 4052 .MSTORE)
    (blockOfS _ (pcFactS input 4052 5303 _ (by norm_num) pc4052) hc)
  have hd : Stepper.runInstr (.push 1 32) (storedState input 5304 []) =
      some (storedState input 5306 [32]) := by rfl
  have d := soundS (pushAt 4053 1 32)
    (blockOfS _
      (show (storedState input 5304 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4053 from
          pcFactS input 4053 5304 [] (by norm_num) pc4053) hd)
  have he : Stepper.runInstr (.push 0 0) (storedState input 5306 [32]) =
      some (storedState input 5307 [0, 32]) := by rfl
  have e := soundS (pushAt 4054 0 0)
    (blockOfS _
      (show (storedState input 5306 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4054 from
          pcFactS input 4054 5306 [32] (by norm_num) pc4054) he)
  have hf : Stepper.runInstr (.op .RETURN) (storedState input 5307 [0, 32]) =
      some (returnedState input) := by rfl
  have f := soundS (opAt 4055 .RETURN)
    (blockOfS _
      (show (storedState input 5307 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4055 from
          pcFactS input 4055 5307 [0, 32] (by norm_num) pc4055) hf)
  exact a.trans (b.trans (c.trans (d.trans (e.trans f))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256) (heq : acc = 0) :
    GasSteps (stS input 5268 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (gasSteps_hit input sv ov acc heq).trans (gasSteps_return input)

#print axioms gasSteps_miss
#print axioms gasSteps_finish_hit
#print axioms run_exit_fallback_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
