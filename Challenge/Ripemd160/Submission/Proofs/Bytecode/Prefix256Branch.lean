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
    GasSteps (stS input 223 (sv :: ov :: rest))
      (stS input 229 ((5266 : UInt256) ::
        UInt256.eq ov (UInt256.ofNat input.size) :: sv :: ov :: rest)) := by
  have a := soundS (opAt 112 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 112 223 _ (by norm_num) (by rfl))
      (stepS_calldatasize input 223 (sv :: ov :: rest) (by simp; omega) (by norm_num)))
  have b := soundS (opAt 113 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 113 224 _ (by norm_num) (by rfl))
      (stepS_dup input 224 2 (by decide)
        (UInt256.ofNat input.size :: sv :: ov :: rest) ov
        (by rfl) (by simp; omega) (by norm_num)))
  have c := soundS (opAt 114 .EQ)
    (blockOfS _ (pcFactS input 114 225 _ (by norm_num) (by rfl))
      (stepS_eq input 225 ov (UInt256.ofNat input.size) (sv :: ov :: rest)
        (by simp; omega) (by norm_num)))
  have d := soundS (pushAt 115 2 5266)
    (blockOfS _ (pcFactS input 115 226 _ (by norm_num) (by rfl))
      (stepS_push input 226 2 5266
        (UInt256.eq ov (UInt256.ofNat input.size) :: sv :: ov :: rest)
        (by simp; omega) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_size_skip (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (hne : ov ≠ UInt256.ofNat input.size) :
    GasSteps (stS input 223 (sv :: ov :: rest))
      (stS input 230 (sv :: ov :: rest)) := by
  have hc : ¬ UInt256.isTrue (UInt256.eq ov (UInt256.ofNat input.size)) := by
    have hn : ov.toNat ≠ (UInt256.ofNat input.size).toNat :=
      fun h => hne (Challenge.EvmProof.Word.word_ext h)
    simp only [UInt256.eq, if_neg hn, UInt256.isTrue]
    decide
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 116 .JUMPI)
      (blockOfS _ (pcFactS input 116 229 _ (by norm_num) (by rfl))
        (stepS_jumpi_fall input 229 5266 (UInt256.eq ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) hc)))

def gasSteps_size_done (input : ByteArray) (sv ov : UInt256) (rest : List UInt256)
    (hlen : rest.length < 1020) (heq : ov = UInt256.ofNat input.size) :
    GasSteps (stS input 223 (sv :: ov :: rest))
      (stS input 5266 (sv :: ov :: rest)) := by
  have hc : UInt256.isTrue (UInt256.eq ov (UInt256.ofNat input.size)) := by
    simp [UInt256.eq, UInt256.isTrue, heq]
  have hd : Decode.isValidJumpDest submissionBytecode 5266 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4037 (by rfl)
  exact (gasSteps_size_test input sv ov rest hlen).trans
    (soundS (opAt 116 .JUMPI)
      (blockOfS _ (pcFactS input 116 229 _ (by norm_num) (by rfl))
        (stepS_jumpi_taken input 229 5266 5266 (UInt256.eq ov (UInt256.ofNat input.size))
          (sv :: ov :: rest) (by simp; omega) (by norm_num) rfl hc hd)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
