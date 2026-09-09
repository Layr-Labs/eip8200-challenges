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
    GasSteps (stS input 384 (sv :: ov :: rest))
      (stS input 389 ((168 : UInt256) ::
        UInt256.gt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)) := by
  have a := soundS (opAt 230 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 230 384 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 384 (sv :: ov :: rest) (by simp; omega) (by norm_num)))
  have b := soundS (opAt 231 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 231 385 _ (by norm_num) (by rfl))
      (stepS_dup input 385 2 (by decide)
        (UInt256.ofNat input.size :: sv :: ov :: rest) ov
        (by rfl) (by simp; omega) (by norm_num)))
  have c := soundS (opAt 232 .GT)
    (blockOfS _ (pcFactS input 232 386 _ (by norm_num) (by rfl))
      (stepS_gt input 386 ov (UInt256.ofNat input.size) (sv :: ov :: rest)
        (by simp; omega) (by norm_num)))
  have d := soundS (pushAt 233 1 168)
    (blockOfS _ (pcFactS input 233 387 _ (by norm_num) (by rfl))
      (stepS_push input 387 1 168
        (UInt256.gt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)
        (by simp; omega) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_size_skip (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : ¬ UInt256.isTrue (UInt256.gt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 384 (sv :: ov :: rest))
      (stS input 390 (sv :: ov :: rest)) := by
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 234 .JUMPI)
      (blockOfS _ (pcFactS input 234 389 _ (by norm_num) pc_ins221)
        (stepS_jumpi_fall input 389 168 (UInt256.gt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) hc)))

def gasSteps_size_done (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : UInt256.isTrue (UInt256.gt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 384 (sv :: ov :: rest))
      (stS input 168 (sv :: ov :: rest)) := by
  have hd : Decode.isValidJumpDest submissionBytecode 168 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 97 (by rfl)
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 234 .JUMPI)
      (blockOfS _ (pcFactS input 234 389 _ (by norm_num) pc_ins221)
        (stepS_jumpi_taken input 389 168 168 (UInt256.gt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) rfl hc hd)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
