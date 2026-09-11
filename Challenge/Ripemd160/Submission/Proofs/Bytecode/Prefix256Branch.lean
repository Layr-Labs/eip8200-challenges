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
    GasSteps (stS input 241 (sv :: ov :: rest))
      (stS input 246 ((152 : UInt256) ::
        UInt256.lt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)) := by
  have a := soundS (opAt 152 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 152 241 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 241 (sv :: ov :: rest) (by simp; omega) (by norm_num)))
  have b := soundS (opAt 153 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 153 242 _ (by norm_num) (by rfl))
      (stepS_dup input 242 2 (by decide)
        (UInt256.ofNat input.size :: sv :: ov :: rest) ov
        (by rfl) (by simp; omega) (by norm_num)))
  have c := soundS (opAt 154 .LT)
    (blockOfS _ (pcFactS input 154 243 _ (by norm_num) (by rfl))
      (stepS_lt input 243 ov (UInt256.ofNat input.size) (sv :: ov :: rest)
        (by simp; omega) (by norm_num)))
  have d := soundS (pushAt 155 1 152)
    (blockOfS _ (pcFactS input 155 244 _ (by norm_num) (by rfl))
      (stepS_push input 244 1 152
        (UInt256.lt ov (UInt256.ofNat input.size) :: sv :: ov :: rest)
        (by simp; omega) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_size_more (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : UInt256.isTrue (UInt256.lt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 241 (sv :: ov :: rest))
      (stS input 152 (sv :: ov :: rest)) := by
  have hd : Decode.isValidJumpDest submissionBytecode 152 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 79 (by rfl)
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 156 .JUMPI)
      (blockOfS _ (pcFactS input 156 246 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 246 152 152 (UInt256.lt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) rfl hc hd)))

def gasSteps_size_end (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hc : ¬ UInt256.isTrue (UInt256.lt ov (UInt256.ofNat input.size))) :
    GasSteps (stS input 241 (sv :: ov :: rest))
      (stS input 247 (sv :: ov :: rest)) := by
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 156 .JUMPI)
      (blockOfS _ (pcFactS input 156 246 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 246 152 (UInt256.lt ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) hc)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
