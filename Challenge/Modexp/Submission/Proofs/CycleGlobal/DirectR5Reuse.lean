import Challenge.Modexp.Submission.Proofs.CycleGlobal.R5Route
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.DirectR5Reuse
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
def program : List Instr :=
 [.op .JUMPDEST,.op (.Swap ⟨12,by decide⟩),.push 2 2720,.op .MLOAD,
  .op (.Swap ⟨10,by decide⟩),.push 2 5229,.op .JUMP]
def result (s : State) (mem : ByteArray) (count : UInt256) (bsize esize msize : Nat) : State :=
 R5Route.entry s mem (MachineState.readWord mem 1664)
 (CycleSubmission.Global.Fast.Shift.hdSlot mem)
 (UInt256.ofNat 128)
 (MachineState.readWord mem 1312) (MachineState.readWord mem 1344)
 (MachineState.readWord mem 1376) (MachineState.readWord mem 1408)
 (MachineState.readWord mem 1440) (MachineState.readWord mem 1472)
 (MachineState.readWord mem 1504) (MachineState.readWord mem 1632)
 (MachineState.readWord mem 2720) (MachineState.readWord mem 1568)
 (CycleSubmission.Global.Fast.Shift.aprevSlot mem) count (UInt256.ofNat 2519)
 ((SlimFrames.outer mem 4 bsize esize msize).drop 13)
theorem run (s : State) (mem : ByteArray) (count : UInt256) (bsize esize msize : Nat)
 (hact : 88 ≤ s.activeWords.toNat)
 (hd : Decode.isValidJumpDest s.executionEnv.code 5229 = true) :
 runInstructions program {s with pc := UInt256.ofNat 3226,memory := mem, stack := [count,UInt256.ofNat 128]++SlimFrames.outer mem 4 bsize esize msize} =
 some (result s mem count bsize esize msize) := by
 have hf := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
 simp [program,result,R5Route.entry,SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,
  Exp.outer,runInstructions,Stepper.runInstr,List.exchange,hd,State.activeWordsAfterUInt256,hf,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
#print axioms run
/-- The actual width-four entry carries the conventional return word in field fifteen. -/
theorem result_return (s : State) (mem : ByteArray) (count : UInt256) (bsize esize msize : Nat) :
 (result s mem count bsize esize msize).stack[15]? = some (UInt256.ofNat 2519) := rfl
#print axioms result_return
end CycleSubmission.Global.DirectR5Reuse
