import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryComposition
import Challenge.Ripemd160.Submission.Local20261028.EntryValuation
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option trace.profiler false
namespace RipemdSubmission20261101.OrdinaryMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdMemoryBridge20261028 PairedScheduleMemory
theorem read_raw_disjoint (m : ByteArray) (a b : Nat) (w : UInt256)
    (h : a+32 ≤ b ∨ b+32 ≤ a) :
    MachineState.readWord (MachineState.writeBytes m (Data.Bytes.natToBytesPadded w.toNat 32) b) a =
      MachineState.readWord m a := read_writeWord_disjoint m a b w h
def memory0 (s : State) : ByteArray := fanMemory s.memory
def state0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 556, stack := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory0 s}
theorem eq0 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result0 s x rho = state0 s x rho := by rfl
def memory1 (s : State) : ByteArray := writeWord (memory0 s) 594 (MachineState.readWord (fanMemory s.memory) 146)
def memory2 (s : State) : ByteArray := writeWord (memory1 s) 684 (MachineState.readWord (fanMemory s.memory) 266)
def memory3 (s : State) : ByteArray := writeWord (memory2 s) 108 (MachineState.readWord (fanMemory s.memory) 258)
def memory4 (s : State) : ByteArray := writeWord (memory3 s) 252 (MachineState.readWord (fanMemory s.memory) 142)
def memory5 (s : State) : ByteArray := writeWord (memory4 s) 324 (MachineState.readWord (fanMemory s.memory) 232)
def memory6 (s : State) : ByteArray := writeWord (memory5 s) 18 (MachineState.readWord (fanMemory s.memory) 266)
def memory7 (s : State) : ByteArray := writeWord (memory6 s) 666 (MachineState.readWord (fanMemory s.memory) 180)
def memory8 (s : State) : ByteArray := writeWord (memory7 s) 216 (MachineState.readWord (fanMemory s.memory) 172)
def memory9 (s : State) : ByteArray := writeWord (memory8 s) 756 (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134))
def memory10 (s : State) : ByteArray := writeWord (memory9 s) 198 (MachineState.readWord (fanMemory s.memory) 142)
def memory11 (s : State) : ByteArray := writeWord (memory10 s) 360 (MachineState.readWord (fanMemory s.memory) 258)
def memory12 (s : State) : ByteArray := writeWord (memory11 s) 90 (MachineState.readWord (fanMemory s.memory) 224)
def memory13 (s : State) : ByteArray := writeWord (memory12 s) 900 (MachineState.readWord (fanMemory s.memory) 138)
def memory14 (s : State) : ByteArray := writeWord (memory13 s) 648 (MachineState.readWord (fanMemory s.memory) 142)
def memory15 (s : State) : ByteArray := writeWord (memory14 s) 738 (MachineState.readWord (fanMemory s.memory) 262)
def memory16 (s : State) : ByteArray := writeWord (memory15 s) 630 (MachineState.readWord (fanMemory s.memory) 176)
def memory17 (s : State) : ByteArray := writeWord (memory16 s) 828 (MachineState.readWord (fanMemory s.memory) 236)
def memory18 (s : State) : ByteArray := writeWord (memory17 s) 612 (MachineState.readWord (fanMemory s.memory) 180)
def memory19 (s : State) : ByteArray := writeWord (memory18 s) 720 (MachineState.readWord (fanMemory s.memory) 262)
def memory20 (s : State) : ByteArray := writeWord (memory19 s) 846 (MachineState.readWord (fanMemory s.memory) 146)
def memory21 (s : State) : ByteArray := writeWord (memory20 s) 72 (MachineState.readWord (fanMemory s.memory) 258)
def memory22 (s : State) : ByteArray := writeWord (memory21 s) 558 (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134))
def memory23 (s : State) : ByteArray := writeWord (memory22 s) 864 (MachineState.readWord (fanMemory s.memory) 236)
def memory24 (s : State) : ByteArray := writeWord (memory23 s) 54 (MachineState.readWord (fanMemory s.memory) 168)
def memory25 (s : State) : ByteArray := writeWord (memory24 s) 1008 (MachineState.readWord (fanMemory s.memory) 180)
def memory26 (s : State) : ByteArray := writeWord (memory25 s) 414 (MachineState.readWord (fanMemory s.memory) 258)
def memory27 (s : State) : ByteArray := writeWord (memory26 s) 540 (MachineState.readWord (fanMemory s.memory) 228)
def memory28 (s : State) : ByteArray := writeWord (memory27 s) 936 (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134))
def memory29 (s : State) : ByteArray := writeWord (memory28 s) 522 (MachineState.readWord (fanMemory s.memory) 224)
def memory30 (s : State) : ByteArray := writeWord (memory29 s) 504 (MachineState.readWord (fanMemory s.memory) 228)
def memory31 (s : State) : ByteArray := writeWord (memory30 s) 396 (MachineState.readWord (fanMemory s.memory) 266)
def memory32 (s : State) : ByteArray := writeWord (memory31 s) 486 (MachineState.readWord (fanMemory s.memory) 168)
def memory33 (s : State) : ByteArray := writeWord (memory32 s) 972 (MachineState.readWord (fanMemory s.memory) 236)
def memory34 (s : State) : ByteArray := writeWord (memory33 s) 468 (MachineState.readWord (fanMemory s.memory) 262)
def memory35 (s : State) : ByteArray := writeWord (memory34 s) 450 (MachineState.readWord (fanMemory s.memory) 168)
def memory36 (s : State) : ByteArray := writeWord (memory35 s) 792 (MachineState.readWord (fanMemory s.memory) 138)
def state1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 621, stack := [(MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 258), (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134)), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory1 s}
theorem eq1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result1 s x rho = state1 s x rho := by
  simp only [OrdinaryTable.result1, OrdinaryTable.args1, eq0, state0, state1,
    Ordinary1.outputs, Ordinary1.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 646, stack := [(MachineState.readWord (fanMemory s.memory) 232), (MachineState.readWord (fanMemory s.memory) 172), (MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 176), (MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 258), (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134)), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory4 s}
theorem eq2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result2 s x rho = state2 s x rho := by
  simp only [OrdinaryTable.result2, OrdinaryTable.args2, eq1, state1, state2,
    Ordinary2.outputs, Ordinary2.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 680, stack := [(MachineState.readWord (fanMemory s.memory) 142), (MachineState.readWord (fanMemory s.memory) 176), (MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 258), (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134)), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory10 s}
theorem eq3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result3 s x rho = state3 s x rho := by
  simp only [OrdinaryTable.result3, OrdinaryTable.args3, eq2, state2, state3,
    Ordinary3.outputs, Ordinary3.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory10, memory9, memory8, memory7, memory6, memory5, memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 707, stack := [(MachineState.readWord (fanMemory s.memory) 146), (MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 258), (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134)), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory16 s}
theorem eq4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result4 s x rho = state4 s x rho := by
  simp only [OrdinaryTable.result4, OrdinaryTable.args4, eq3, state3, state4,
    Ordinary4.outputs, Ordinary4.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory16, memory15, memory14, memory13, memory12, memory11, memory10, memory9, memory8, memory7, memory6, memory5, memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 735, stack := [(MachineState.readWord (fanMemory s.memory) 180), (MachineState.readWord (fanMemory s.memory) 258), (UInt256.add (UInt256.ofNat 63353157587505792712163362468939828208675924746436608) (MachineState.readWord (fanMemory s.memory) 134)), (MachineState.readWord (fanMemory s.memory) 224), (MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory22 s}
theorem eq5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result5 s x rho = state5 s x rho := by
  simp only [OrdinaryTable.result5, OrdinaryTable.args5, eq4, state4, state5,
    Ordinary5.outputs, Ordinary5.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory22, memory21, memory20, memory19, memory18, memory17, memory16, memory15, memory14, memory13, memory12, memory11, memory10, memory9, memory8, memory7, memory6, memory5, memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state6 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 765, stack := [(MachineState.readWord (fanMemory s.memory) 228), (MachineState.readWord (fanMemory s.memory) 266), (MachineState.readWord (fanMemory s.memory) 236), (MachineState.readWord (fanMemory s.memory) 262), (MachineState.readWord (fanMemory s.memory) 168), (MachineState.readWord (fanMemory s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory29 s}
theorem eq6 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result6 s x rho = state6 s x rho := by
  simp only [OrdinaryTable.result6, OrdinaryTable.args6, eq5, state5, state6,
    Ordinary6.outputs, Ordinary6.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory29, memory28, memory27, memory26, memory25, memory24, memory23, memory22, memory21, memory20, memory19, memory18, memory17, memory16, memory15, memory14, memory13, memory12, memory11, memory10, memory9, memory8, memory7, memory6, memory5, memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
def state7 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 794, stack := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory36 s}
theorem eq7 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    OrdinaryTable.result7 s x rho = state7 s x rho := by
  simp only [OrdinaryTable.result7, OrdinaryTable.args7, eq6, state6, state7,
    Ordinary7.outputs, Ordinary7.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  try simp (discharger := omega) only [memory36, memory35, memory34, memory33, memory32, memory31, memory30, memory29, memory28, memory27, memory26, memory25, memory24, memory23, memory22, memory21, memory20, memory19, memory18, memory17, memory16, memory15, memory14, memory13, memory12, memory11, memory10, memory9, memory8, memory7, memory6, memory5, memory4, memory3, memory2, memory1, memory0,
    read_raw_disjoint, read_writeWord_disjoint]
  all_goals rfl
theorem actual_memory (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    (OrdinaryTable.result7 s x rho).memory = memory36 s := by rw [eq7]; rfl
theorem actual_stack (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    (OrdinaryTable.result7 s x rho).stack = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho := by rw [eq7]; rfl
#print axioms actual_memory
#print axioms actual_stack
end RipemdSubmission20261101.OrdinaryMemory
