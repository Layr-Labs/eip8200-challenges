import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar
theorem stepS_calldatasize (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Stepper.runInstr (.op .CALLDATASIZE) (stS input pc stk) =
      some (stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_lt (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Stepper.runInstr (.op .LT) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.lt a b :: rest)) := by
  unfold Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Word.succ_ofNat hpc]

def gasSteps_size_test (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) :
    GasSteps (stS input 411 (sv :: ov :: rest))
      (stS input 417 ((316 : UInt256) ::
        UInt256.lt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)) := by
  have a := soundS (opAt 251 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 251 411 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 411 (sv :: ov :: rest) (by simp; omega) (by norm_num)))
  have b := soundS (opAt 252 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 252 412 _ (by norm_num) (by rfl))
      (stepS_dup input 412 2 (by decide)
        (UInt256.ofNat input.size :: sv :: ov :: rest) ov
        (by rfl) (by simp; omega) (by norm_num)))
  have c := soundS (opAt 253 .LT)
    (blockOfS _ (pcFactS input 253 413 _ (by norm_num) (by rfl))
      (stepS_lt input 413 ov (UInt256.ofNat input.size) (sv :: ov :: rest)
        (by simp; omega) (by norm_num)))
  have d := soundS (pushAt 254 2 316)
    (blockOfS _ (pcFactS input 254 414 _ (by norm_num) (by rfl))
      (stepS_push input 414 2 316
        (UInt256.lt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)
        (by simp; omega) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_size_more (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : UInt256.isTrue (UInt256.lt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 411 (sv :: ov :: rest))
      (stS input 316 (sv :: ov :: rest)) := by
  have hd : Decode.isValidJumpDest submissionBytecode 316 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 174 (by rfl)
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 255 .JUMPI)
      (blockOfS _ (pcFactS input 255 417 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 417 316 316 (UInt256.lt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) rfl hc hd)))

def gasSteps_size_end (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : ¬ UInt256.isTrue (UInt256.lt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 411 (sv :: ov :: rest))
      (stS input 418 (sv :: ov :: rest)) := by
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 255 .JUMPI)
      (blockOfS _ (pcFactS input 255 417 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 417 316 (UInt256.lt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) hc)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
