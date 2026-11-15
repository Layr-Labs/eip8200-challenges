import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPhaseRun
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace CycleSubmission.DirectCounterExit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global
local notation "N" => UInt256.ofNat
def program : List Instr := [.op .POP,.op (.Swap ⟨12,by decide⟩),.op .JUMP]
def input (z : UInt256) (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with pc:=N pc,memory:=mem,stack:=N 0::Fast.Shift.entrySlots z mem n bsize esize++Exp.outer n bsize esize msize}
def output (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 SlimFrames.frameState s mem z.toNat n bsize esize msize
theorem run (z : UInt256) (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat)
 (hj : Decode.isValidJumpDest s.executionEnv.code z.toNat=true) :
 runInstructions program (input z s mem pc n bsize esize msize) =
 some (output z s mem n bsize esize msize) := by
 have hz : N z.toNat=z := by
  apply Word.word_ext
  rw [Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt z.val.isLt
 simp [program,input,output,SlimFrames.frameState,SlimFrames.outer,
  Fast.Shift.entrySlots,Fast.Shift.aprevSlot,Fast.Shift.hdSlot,
  Exp.outer,runInstructions,Stepper.runInstr,List.exchange,hj,hz,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
end CycleSubmission.DirectCounterExit
