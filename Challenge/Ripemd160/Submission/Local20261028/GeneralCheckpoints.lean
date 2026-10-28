import Challenge.Ripemd160.Submission.Local20261028.TableComposition
import Challenge.Ripemd160.Submission.Local20261028.EntryValuation
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdMemoryBridge20261028.GeneralCheckpoints
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdSubmissionTables20261028
def state0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 548, stack := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 (MachineState.readWord (s.memory) 146))) 196 (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 128 (MachineState.readWord (s.memory) 146))) 178))) 218 (MachineState.readWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 (MachineState.readWord (s.memory) 146))) 196 (MachineState.readWord ((PairedScheduleMemory.writeWord (s.memory) 128 (MachineState.readWord (s.memory) 146))) 178))) 236))}
theorem eq0 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result0 s x rho = state0 s x rho := by
  rfl
def memory1 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (fanMemory s.memory) 828 (MachineState.readWord (fanMemory s.memory) 236))
def state1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 609, stack := [(MachineState.readWord (fanMemory s.memory) 176), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 172), (MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 258), (MachineState.readWord (fanMemory s.memory) 134), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory1 s}
theorem eq1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result1 s x rho = state1 s x rho := by
  simp only [GeneralTable.result1, eq0]
  rfl
def memory2 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory1 s) 684 (MachineState.readWord (fanMemory s.memory) 266))
def memory3 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory2 s) 666 (MachineState.readWord (fanMemory s.memory) 180))
def memory4 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory3 s) 108 (MachineState.readWord (fanMemory s.memory) 258))
def memory5 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory4 s) 648 (MachineState.readWord (fanMemory s.memory) 142))
def state2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 630, stack := [(MachineState.readWord (fanMemory s.memory) 176), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 172), (MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 258), (MachineState.readWord (fanMemory s.memory) 134), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory5 s}
theorem eq2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result2 s x rho = state2 s x rho := by
  simp only [GeneralTable.result2, eq1]
  rfl
def memory6 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory5 s) 630 (MachineState.readWord (fanMemory s.memory) 176))
def memory7 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory6 s) 18 (MachineState.readWord (fanMemory s.memory) 266))
def memory8 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory7 s) 558 (MachineState.readWord (fanMemory s.memory) 134))
def memory9 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory8 s) 414 (MachineState.readWord (fanMemory s.memory) 258))
def memory10 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory9 s) 540 (MachineState.readWord (fanMemory s.memory) 228))
def state3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 651, stack := [(MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 172), (MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 258), (MachineState.readWord (fanMemory s.memory) 134), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory10 s}
theorem eq3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result3 s x rho = state3 s x rho := by
  simp only [GeneralTable.result3, eq2]
  rfl
def memory11 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory10 s) 252 (MachineState.readWord (fanMemory s.memory) 142))
def memory12 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory11 s) 522 (MachineState.readWord (fanMemory s.memory) 224))
def memory13 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory12 s) 90 (MachineState.readWord (fanMemory s.memory) 224))
def memory14 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory13 s) 216 (MachineState.readWord (fanMemory s.memory) 172))
def memory15 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory14 s) 72 (MachineState.readWord (fanMemory s.memory) 258))
def state4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 670, stack := [(MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 258), (MachineState.readWord (fanMemory s.memory) 134), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory15 s}
theorem eq4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result4 s x rho = state4 s x rho := by
  simp only [GeneralTable.result4, eq3]
  rfl
def memory16 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory15 s) 594 (MachineState.readWord (fanMemory s.memory) 146))
def memory17 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory16 s) 846 (MachineState.readWord (fanMemory s.memory) 146))
def memory18 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory17 s) 54 (MachineState.readWord (fanMemory s.memory) 168))
def memory19 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory18 s) 936 (MachineState.readWord (fanMemory s.memory) 134))
def memory20 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory19 s) 972 (MachineState.readWord (fanMemory s.memory) 236))
def state5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 693, stack := [(MachineState.readWord (fanMemory s.memory) 258), (MachineState.readWord (fanMemory s.memory) 134), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory20 s}
theorem eq5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result5 s x rho = state5 s x rho := by
  simp only [GeneralTable.result5, eq4]
  rfl
def memory21 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory20 s) 360 (MachineState.readWord (fanMemory s.memory) 258))
def memory22 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory21 s) 756 (MachineState.readWord (fanMemory s.memory) 134))
def memory23 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory22 s) 198 (MachineState.readWord (fanMemory s.memory) 142))
def memory24 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory23 s) 738 (MachineState.readWord (fanMemory s.memory) 262))
def memory25 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory24 s) 504 (MachineState.readWord (fanMemory s.memory) 228))
def memory26 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory25 s) 486 (MachineState.readWord (fanMemory s.memory) 168))
def state6 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 749, stack := [(MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory26 s}
theorem eq6 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result6 s x rho = state6 s x rho := by
  simp only [GeneralTable.result6, eq5]
  rfl
def memory27 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory26 s) 468 (MachineState.readWord (fanMemory s.memory) 262))
def memory28 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory27 s) 450 (MachineState.readWord (fanMemory s.memory) 168))
def memory29 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory28 s) 792 (MachineState.readWord (fanMemory s.memory) 138))
def memory30 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory29 s) 864 (MachineState.readWord (fanMemory s.memory) 236))
def memory31 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory30 s) 1008 (MachineState.readWord (fanMemory s.memory) 180))
def state7 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 803, stack := [(MachineState.readWord (fanMemory s.memory) 138), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 232), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory31 s}
theorem eq7 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result7 s x rho = state7 s x rho := by
  simp only [GeneralTable.result7, eq6]
  rfl
def memory32 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory31 s) 900 (MachineState.readWord (fanMemory s.memory) 138))
def memory33 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory32 s) 612 (MachineState.readWord (fanMemory s.memory) 180))
def memory34 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory33 s) 396 (MachineState.readWord (fanMemory s.memory) 266))
def memory35 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory34 s) 720 (MachineState.readWord (fanMemory s.memory) 262))
def memory36 (s : State) : ByteArray := (PairedScheduleMemory.writeWord (memory35 s) 324 (MachineState.readWord (fanMemory s.memory) 232))
def state8 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 823, stack := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory36 s}
theorem eq8 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    GeneralTable.result8 s x rho = state8 s x rho := by
  simp only [GeneralTable.result8, eq7]
  rfl
theorem actual_memory (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    (GeneralTable.result8 s x rho).memory =
      resultMemory (fanMemory s.memory) RipemdTableOrder20261027.selected := by
  rw [eq8]
  rfl
#print axioms actual_memory
end RipemdMemoryBridge20261028.GeneralCheckpoints
