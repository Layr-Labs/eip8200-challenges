import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastP6
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.EvmProof.Memory
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.ZeroMod12
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open CycleSubmission.Global.Fast
def entry (s : State) (input : ByteArray) : State :=
 {s with pc := UInt256.ofNat 10961,stack := [UInt256.ofNat (modulusSize input)]}
def oldEntry (s : State) : State :=
 {s with pc := UInt256.ofNat 10302,stack := []}
def memo (s : State) : State :=
 {s with pc := UInt256.ofNat 903,stack := []}
def rawWord (input : ByteArray) : UInt256 :=
 UInt256.shiftRight (MachineState.readWord input (96+baseSize input+exponentSize input)) (UInt256.ofNat 160)
def memory (s : State) : ByteArray :=
 s.memory
def finalState (s : State) : State :=
 {s with
   pc := UInt256.ofNat 10989
   stack := []
   memory := memory s
   activeWords := UInt256.ofNat 1
   halt := .Returned
   hReturn := MachineState.readPadded (memory s) 0 12}
theorem run_width_miss (s : State) (input : ByteArray)
 (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
 (hsize : modulusSize input ≤ 1024) (hne : modulusSize input ≠ 12) :
 Stepper.runLocatedBlock blkZero12WidthMiss (entry s input) = some (oldEntry s) := by
 have hword : UInt256.ofNat (modulusSize input) ≠ UInt256.ofNat 12 := by
  intro h
  have hh := congrArg UInt256.toNat h
  simp only [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (show modulusSize input < 2^256 by omega)] at hh
  exact hne (by simpa using hh)
 have hx : (UInt256.xor (UInt256.ofNat 12) (UInt256.ofNat (modulusSize input))).toNat ≠ 0 := by
  intro h
  have hw : UInt256.xor (UInt256.ofNat 12) (UInt256.ofNat (modulusSize input)) = 0 :=
   Word.word_ext h
  exact hword ((WindowGuardLogic.wordXor_eq_zero_iff _ _).mp hw).symm
 simp (config := { maxSteps := 400000 }) [packedZero12PCs,blkZero12WidthMiss,opAt,pushAt,wfOp,
  Stepper.runLocatedBlock,Stepper.runLocated,Stepper.runInstr,entry,oldEntry,
  hrun,hcode,jumpDestZeroExp,hx,UInt256.isTrue,Word.literal_eq_ofNat,
  Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem pointer (input : ByteArray) (hb : baseSize input ≤ 1024)
 (he : exponentSize input ≤ 1024) :
 (UInt256.ofNat 96 + (UInt256.ofNat (exponentSize input) + UInt256.ofNat (baseSize input))).toNat =
 96+baseSize input+exponentSize input := by
 rw [Word.ofNat_add_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,
  Nat.mod_eq_of_lt (show 96+(exponentSize input+baseSize input)<2^256 by omega)]
 omega
theorem run_nonzero (s : State) (input : ByteArray)
 (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
 (hdata : s.executionEnv.calldata = input)
 (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
 (hsize : modulusSize input = 12) (hne : (rawWord input).toNat ≠ 0) :
 Stepper.runLocatedBlock blkZero12Nonzero (entry s input) = some (memo s) := by
 simp only [rawWord] at hne
 have hoff : (96+(exponentSize input+baseSize input)) % 2^256 = 96+baseSize input+exponentSize input := by
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
 change (96+(exponentSize input+baseSize input)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+baseSize input+exponentSize input at hoff
 have hz0 : ({val := 0} : UInt256).toNat = 0 := rfl
 have hbase : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
 have hexp : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
 have hx : UInt256.xor (UInt256.ofNat 12) (UInt256.ofNat 12) = UInt256.ofNat 0 := by decide
 simp (config := { maxSteps := 600000 }) [packedZero12PCs,blkZero12Nonzero,opAt,pushAt,wfOp,
  Stepper.runLocatedBlock,Stepper.runLocated,Stepper.runInstr,entry,memo,
  hrun,hcode,hdata,hz0,hoff,hbase,hexp,hsize,hx,pointer input hb he,rawWord,hne,
  UInt256.isTrue,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,jumpDest698]
theorem run_zero (s : State) (input : ByteArray)
 (hrun : s.halt = .Running) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
 (hdata : s.executionEnv.calldata = input)
 (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
 (hsize : modulusSize input = 12) (hz : (rawWord input).toNat = 0)
 (hwords : s.activeWords.toNat ≤ 1) :
 Stepper.runLocatedBlock blkZero12Zero (entry s input) = some (finalState s) := by
 simp only [rawWord] at hz
 have hoff : (96+(exponentSize input+baseSize input)) % 2^256 = 96+baseSize input+exponentSize input := by
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
 change (96+(exponentSize input+baseSize input)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+baseSize input+exponentSize input at hoff
 have hz0 : ({val := 0} : UInt256).toNat = 0 := rfl
 have hbase : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
 have hexp : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
 have hx : UInt256.xor (UInt256.ofNat 12) (UInt256.ofNat 12) = UInt256.ofNat 0 := by decide
 simp (config := { maxSteps := 600000 }) [packedZero12PCs,blkZero12Zero,opAt,pushAt,wfOp,
  Stepper.runLocatedBlock,Stepper.runLocated,Stepper.runInstr,entry,finalState,memory,
  hrun,hcode,hdata,hz0,hoff,hbase,hexp,hsize,hx,pointer input hb he,rawWord,hz,
  UInt256.isTrue,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,State.activeWordsAfterUInt256,
  State.activeWordsAfterUInt256_2,MachineState.activeWordsAfter]
 all_goals simp [Nat.max_eq_right hwords]
theorem rawWord_value (input : ByteArray) :
 rawWord input = UInt256.ofNat (Precompile.bytesToNatPadded input
  (96+baseSize input+exponentSize input) 12) :=
 Bytes.shiftRight_readWord input (96+baseSize input+exponentSize input) 12 (by decide) (by decide)
theorem memory_output (s : State) (hmem : s.memory = ByteArray.empty) :
 MachineState.readPadded (memory s) 0 12 = Precompile.natToBytes 0 12 := by
 rw [memory,hmem]
 exact Algorithm.zeroBytes 0 12
theorem isDone (s : State) (hcall : s.callStack = []) :
 (finalState s).isDone = true := by
 simp [finalState,State.isDone,State.isHalted,State.isRunning,hcall]
theorem result (s : State) (input : ByteArray) (hsize : modulusSize input = 12)
 (hz : (rawWord input).toNat = 0) (hmem : s.memory = ByteArray.empty) :
 (finalState s).toResult = .returned (spec input) := by
 have hm : Precompile.bytesToNatPadded input (96+baseSize input+exponentSize input) 12 = 0 := by
  rw [rawWord_value,Word.word_toNat_ofNat] at hz
  have hlt := Bytes.bytesToNatPadded_lt_pow input (96+baseSize input+exponentSize input) 12
  rw [Nat.mod_eq_of_lt (by norm_num at hlt ⊢; omega)] at hz
  exact hz
 change ExecutionResult.returned (MachineState.readPadded (memory s) 0 12) = _
 rw [memory_output s hmem]
 simp [spec,hsize,hm,Precompile.modPow]
#print axioms run_width_miss
#print axioms run_nonzero
#print axioms run_zero
#print axioms result
end CycleSubmission.Global.ZeroMod12
