import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem stepS_calldatasize (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Stepper.runInstr (.op .CALLDATASIZE) (stS input pc stk) =
      some (stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

def gasSteps_size_test (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) :
    GasSteps (stS input 248 (sv :: ov :: rest))
      (stS input 254 ((5192 : UInt256) ::
        UInt256.eq ov (UInt256.ofNat input.size) :: sv :: ov :: rest)) := by
  have a := soundS (opAt 131 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 131 248 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 248 (sv :: ov :: rest) (by simp; omega) (by norm_num)))
  have b := soundS (opAt 132 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 132 249 _ (by norm_num) (by rfl))
      (stepS_dup input 249 2 (by decide)
        (UInt256.ofNat input.size :: sv :: ov :: rest) ov
        (by rfl) (by simp; omega) (by norm_num)))
  have c := soundS (opAt 133 .EQ)
    (blockOfS _ (pcFactS input 133 250 _ (by norm_num) (by rfl))
      (stepS_eq input 250 ov (UInt256.ofNat input.size) (sv :: ov :: rest)
        (by simp; omega) (by norm_num)))
  have d := soundS (pushAt 134 2 5187)
    (blockOfS _ (pcFactS input 134 251 _ (by norm_num) (by rfl))
      (stepS_push input 251 2 5187
        (UInt256.eq ov (UInt256.ofNat input.size) :: sv :: ov :: rest)
        (by simp; omega) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_size_skip (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hne : ov ≠ UInt256.ofNat input.size) :
    GasSteps (stS input 248 (sv :: ov :: rest))
      (stS input 255 (sv :: ov :: rest)) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq ov (UInt256.ofNat input.size)) := by
    have hn : ov.toNat ≠ (UInt256.ofNat input.size).toNat :=
      fun h => hne (Challenge.EvmProof.Word.word_ext h)
    simp only [UInt256.eq, if_neg hn, UInt256.isTrue]
    decide
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 135 .JUMPI)
      (blockOfS _ (pcFactS input 135 254 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 254 5187 (UInt256.eq ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) hc)))

def gasSteps_size_done (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (heq : ov = UInt256.ofNat input.size) :
    GasSteps (stS input 248 (sv :: ov :: rest))
      (stS input 5187 (sv :: ov :: rest)) := by
  have hc : UInt256.isTrue (UInt256.eq ov (UInt256.ofNat input.size)) := by
    simp [UInt256.eq, UInt256.isTrue, heq]
  have hd : Decode.isValidJumpDest submissionBytecode 5187 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4064 (by rfl)
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 135 .JUMPI)
      (blockOfS _ (pcFactS input 135 254 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 254 5187 5187 (UInt256.eq ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) rfl hc hd)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
