import Challenge.Ripemd160.Submission.H39Memo.A1000Advance
import Challenge.Ripemd160.Submission.H39Memo.A1000Single

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem run_first_match (s : State) (input : ByteArray) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input 0 = cacheWord) :
    Stepper.runLocatedBlock firstPath (entry s) = some (cached s) := by
  have hcond : ¬ UInt256.isTrue (UInt256.xor cacheWord (MachineState.readWord input 0)) := by
    rw [xor_true_iff]
    exact not_not_intro hword.symm
  have hbranch := branch_false (opAt 1117 .JUMPI) s 3156 3258
    (UInt256.xor cacheWord (MachineState.readWord input 0)) [cacheWord, 1000] rfl pc1117 (by decide) (by simp) hcond
  change Stepper.runLocatedBlock (firstPrefix ++ [opAt 1117 .JUMPI])
    (entry s) = some (cached s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_firstPrefix s input hinput hrun) hrun
  rw [run_singleton]
  simpa only [cached, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_first_mismatch (s : State) (input : ByteArray) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input 0 ≠ cacheWord)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock firstPath (entry s) = some (notAEntry s) := by
  have hcond : UInt256.isTrue (UInt256.xor cacheWord (MachineState.readWord input 0)) := by
    rw [xor_true_iff]
    exact Ne.symm hword
  have hbranch := branch_true (opAt 1117 .JUMPI) s 3156 3258
    (UInt256.xor cacheWord (MachineState.readWord input 0)) [cacheWord, 1000] rfl pc1117 (by decide) (by decide) (by simp) hcond hcode jump_notA
  change Stepper.runLocatedBlock (firstPrefix ++ [opAt 1117 .JUMPI])
    (entry s) = some (notAEntry s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_firstPrefix s input hinput hrun) hrun
  rw [run_singleton]
  simpa only [notAEntry, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_check_match (s : State) (input : ByteArray) (n : Nat) (hn : n < 30) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input (32 * (n + 1)) = cacheWord) :
    Stepper.runLocatedBlock checkPath (loop s n) = some (checked s n) := by
  have hcond : ¬ UInt256.isTrue (UInt256.xor cacheWord (MachineState.readWord input (32 * (n + 1)))) := by
    rw [xor_true_iff]
    exact not_not_intro hword.symm
  have hbranch := branch_false (opAt 1127 .JUMPI) s 3169 3251
    (UInt256.xor cacheWord (MachineState.readWord input (32 * (n + 1)))) [UInt256.ofNat (32 * (n + 1)), cacheWord] rfl pc1127 (by decide) (by simp) hcond
  change Stepper.runLocatedBlock (loopPrefix ++ [opAt 1127 .JUMPI])
    (loop s n) = some (checked s n)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_loopPrefix s input n hn hinput hrun) hrun
  rw [run_singleton]
  simpa only [checked, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_check_mismatch (s : State) (input : ByteArray) (n : Nat) (hn : n < 30) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input (32 * (n + 1)) ≠ cacheWord)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock checkPath (loop s n) = some (failEntry s (UInt256.ofNat (32 * (n + 1)))) := by
  have hcond : UInt256.isTrue (UInt256.xor cacheWord (MachineState.readWord input (32 * (n + 1)))) := by
    rw [xor_true_iff]
    exact Ne.symm hword
  have hbranch := branch_true (opAt 1127 .JUMPI) s 3169 3251
    (UInt256.xor cacheWord (MachineState.readWord input (32 * (n + 1)))) [UInt256.ofNat (32 * (n + 1)), cacheWord] rfl pc1127 (by decide) (by decide) (by simp) hcond hcode jump_fail
  change Stepper.runLocatedBlock (loopPrefix ++ [opAt 1127 .JUMPI])
    (loop s n) = some (failEntry s (UInt256.ofNat (32 * (n + 1))))
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_loopPrefix s input n hn hinput hrun) hrun
  rw [run_singleton]
  simpa only [failEntry, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_tail_match (s : State) (input : ByteArray) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input 992 = tailWord) :
    Stepper.runLocatedBlock tailPath (tailEntry s) = some (answerEntry s) := by
  have hcond : ¬ UInt256.isTrue (UInt256.xor tailWord (MachineState.readWord input 992)) := by
    rw [xor_true_iff]
    exact not_not_intro hword.symm
  have hbranch := branch_false (opAt 1142 .JUMPI) s 3223 1006
    (UInt256.xor tailWord (MachineState.readWord input 992)) [] rfl pc1142 (by decide) (by simp) hcond
  change Stepper.runLocatedBlock (tailPrefix ++ [opAt 1142 .JUMPI])
    (tailEntry s) = some (answerEntry s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_tailPrefix s input hinput hrun) hrun
  rw [run_singleton]
  simpa only [answerEntry, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

theorem run_tail_mismatch (s : State) (input : ByteArray) 
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hword : MachineState.readWord input 992 ≠ tailWord)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock tailPath (tailEntry s) = some (fallback s) := by
  have hcond : UInt256.isTrue (UInt256.xor tailWord (MachineState.readWord input 992)) := by
    rw [xor_true_iff]
    exact Ne.symm hword
  have hbranch := branch_true (opAt 1142 .JUMPI) s 3223 1006
    (UInt256.xor tailWord (MachineState.readWord input 992)) [] rfl pc1142 (by decide) (by decide) (by simp) hcond hcode jump_fallback
  change Stepper.runLocatedBlock (tailPrefix ++ [opAt 1142 .JUMPI])
    (tailEntry s) = some (fallback s)
  apply Stepper.runLocatedBlock_append _ _ _ _ _ (run_tailPrefix s input hinput hrun) hrun
  rw [run_singleton]
  simpa only [fallback, atPC,
    Challenge.EvmProof.Word.literal_eq_ofNat] using hbranch

end Challenge.Ripemd160.Submission.H39Memo.A1000
