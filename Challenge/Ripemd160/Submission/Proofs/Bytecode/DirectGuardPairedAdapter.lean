import Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSplitCertificate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedSequence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedAdapter

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open DirectGuardPairedRaw DirectGuardPairedSequence

abbrev artifact := Artifact.submissionArtifact

theorem pair_data : artifact.data.drop 280 = pairBytes := by
  rfl

theorem pair_prefix_length :
    (assembleBytes artifact.instructions ++ artifact.data.take 280).length = 5231 := by
  rw [List.length_append, JumpDestSplitCertificate.prefix_length,
    JumpDestSplitCertificate.data_take_length]

theorem pair_assembly :
    mkCode ((assembleBytes artifact.instructions ++ artifact.data.take 280) ++ pairBytes) =
      submissionBytecode := by
  calc
    mkCode ((assembleBytes artifact.instructions ++ artifact.data.take 280) ++ pairBytes) =
        mkCode (assembleBytes artifact.instructions ++
          (artifact.data.take 280 ++ artifact.data.drop 280)) := by
            rw [pair_data]
            simp [List.append_assoc]
    _ = mkCode (assembleBytes artifact.instructions ++ artifact.data) := by
          rw [List.take_append_drop]
    _ = submissionBytecode := artifact.assembly_eq

theorem pair_acc_eq (input : ByteArray) (n : Nat) :
    pairLoopAcc input n = KnownInputCompactState.loopAcc input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pairLoopAcc, KnownInputCompactState.loopAcc]
      rw [ih]
      simp [pairReferenceWord, KnownInputCompactState.referenceWord]

theorem pair_loop_state_eq (input : ByteArray) (n : Nat) :
    pairLoopState submissionBytecode input n =
      { DirectGuard.loopState input n with pc := UInt256.ofNat 5231 } := by
  simp [pairLoopState, DirectGuard.loopState, pairLoopAcc, pairReferenceWord,
    KnownInputCompactState.loopAcc, KnownInputCompactState.referenceWord]
  exact pair_acc_eq input n

theorem pair_exit_state_eq (input : ByteArray) :
    pairExitState submissionBytecode input =
      { DirectGuard.loopExitState input with pc := UInt256.ofNat 67 } := by
  simp [pairExitState, DirectGuard.loopExitState, pairLoopAcc, pairReferenceWord,
    KnownInputCompactState.loopAcc, KnownInputCompactState.referenceWord]

def gasSteps_pair_core (input : ByteArray)
    (hdest5231 : Decode.isValidJumpDest submissionBytecode 5231 = true) :
    GasSteps (pairLoopState submissionBytecode input 0)
      (pairExitState submissionBytecode input) :=
  gasSteps_pair_loop submissionBytecode input
    (assembleBytes artifact.instructions ++ artifact.data.take 280)
    pair_assembly pair_prefix_length hdest5231 DirectGuardPairedSequence.valid_67

def gasSteps_pair_core_verified (input : ByteArray) :
    GasSteps (pairLoopState submissionBytecode input 0)
      (pairExitState submissionBytecode input) :=
  gasSteps_pair_core input JumpDestSplitCertificate.valid_5231_split

#print axioms gasSteps_pair_core
#print axioms gasSteps_pair_core_verified

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedAdapter
