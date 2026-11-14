import Challenge.Ripemd160.Submission.Local20261028.PrepFirstComposition
import Challenge.Ripemd160.Submission.Local20261028.MemoryBridge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.FirstMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdMemoryBridge20261028 PairedScheduleMemory
def memory0 (s : State) : ByteArray := s.memory
def memory1 (s : State) : ByteArray := writeWord (memory0 s) 218 (MachineState.readWord (memory0 s) 236)
def memory2 (s : State) : ByteArray := writeWord (memory1 s) 286 (MachineState.readWord (memory1 s) 268)
def memory3 (s : State) : ByteArray := MachineState.writeBytes (memory2 s) (ByteArray.mk #[UInt8.ofNat ((UInt256.ofNat 128).toNat % 256)]) 147
def memory4 (s : State) : ByteArray := writeWord (memory3 s) 216 (UInt256.ofNat 1329227995784915872903807060280344576)
def memory5 (s : State) : ByteArray := writeWord (memory4 s) 252 (UInt256.ofNat 0)
def memory6 (s : State) : ByteArray := memory5 s
def memory7 (s : State) : ByteArray := writeWord (memory6 s) 936 (UInt256.ofNat 63353160442001178124083124585511767107666197511929984)
def memory8 (s : State) : ByteArray := writeWord (memory7 s) 18 (MachineState.readWord (memory2 s) 266)
def memory9 (s : State) : ByteArray := writeWord (memory8 s) 108 (MachineState.readWord (memory2 s) 258)
def memory10 (s : State) : ByteArray := writeWord (memory9 s) 90 (MachineState.readWord (memory2 s) 224)
def memory11 (s : State) : ByteArray := writeWord (memory10 s) 72 (MachineState.readWord (memory2 s) 258)
def memory12 (s : State) : ByteArray := writeWord (memory11 s) 54 (UInt256.ofNat 309485009821345068724781056)
def memory13 (s : State) : ByteArray := writeWord (memory12 s) 324 (MachineState.readWord (memory2 s) 232)
def memory14 (s : State) : ByteArray := writeWord (memory13 s) 360 (MachineState.readWord (memory2 s) 258)
def memory15 (s : State) : ByteArray := writeWord (memory14 s) 414 (MachineState.readWord (memory2 s) 258)
def memory16 (s : State) : ByteArray := writeWord (memory15 s) 396 (MachineState.readWord (memory2 s) 266)
def memory17 (s : State) : ByteArray := MachineState.writeBytes (writeWord (memory16 s) 482 (UInt256.shiftLeft (MachineState.readWord (memory2 s) 262) (UInt256.ofNat 112))) (ByteArray.mk #[UInt8.ofNat ((UInt256.ofNat 10112).toNat % 256)]) 787
def memory18 (s : State) : ByteArray := writeWord (memory17 s) 522 (MachineState.readWord (memory2 s) 228)
def memory19 (s : State) : ByteArray := writeWord (memory18 s) 540 (MachineState.readWord (memory2 s) 224)
def memory20 (s : State) : ByteArray := writeWord (memory19 s) 558 (MachineState.readWord (memory2 s) 228)
def memory21 (s : State) : ByteArray := writeWord (memory20 s) 684 (MachineState.readWord (memory2 s) 266)
def memory22 (s : State) : ByteArray := MachineState.writeBytes (memory21 s) (MachineState.readPadded s.executionEnv.code 10426 122) 576
def memory23 (s : State) : ByteArray := writeWord (memory22 s) 738 (MachineState.readWord (memory2 s) 262)
def memory24 (s : State) : ByteArray := writeWord (memory23 s) 720 (MachineState.readWord (memory2 s) 262)
def memory25 (s : State) : ByteArray := writeWord (memory24 s) 814 (UInt256.shiftRight (MachineState.readWord (memory2 s) 236) (UInt256.ofNat 112))
def memory26 (s : State) : ByteArray := writeWord (memory25 s) 972 (MachineState.readWord (memory2 s) 236)
def memory27 (s : State) : ByteArray := writeWord (memory26 s) 864 (MachineState.readWord (memory2 s) 236)
def state0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 9987, stack := [(MachineState.readWord (memory2 s) 232), (MachineState.readWord (memory2 s) 258), (MachineState.readWord (memory2 s) 224), (MachineState.readWord (memory2 s) 228), (MachineState.readWord (memory2 s) 266), (MachineState.readWord (memory2 s) 262), (MachineState.readWord (memory2 s) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory3 s}
theorem eq0 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result0 s x rho = state0 s x rho := by
  rfl
def state1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10052, stack := [(MachineState.readWord (memory2 s) 232), (MachineState.readWord (memory2 s) 258), (MachineState.readWord (memory2 s) 224), (MachineState.readWord (memory2 s) 228), (MachineState.readWord (memory2 s) 266), (MachineState.readWord (memory2 s) 262), (MachineState.readWord (memory2 s) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory9 s}
theorem eq1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result1 s x rho = state1 s x rho := by
  simp only [FirstTable.result1, FirstTable.args1, eq0, state0, state1,
    First1.outputs, First1.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  rfl
def state2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10089, stack := [(MachineState.readWord (memory2 s) 224), (MachineState.readWord (memory2 s) 228), (MachineState.readWord (memory2 s) 266), (MachineState.readWord (memory2 s) 262), (MachineState.readWord (memory2 s) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory15 s}
theorem eq2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result2 s x rho = state2 s x rho := by
  simp only [FirstTable.result2, FirstTable.args2, eq1, state1, state2,
    First2.outputs, First2.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  rfl
def state3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10136, stack := [(MachineState.readWord (memory2 s) 262), (MachineState.readWord (memory2 s) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory21 s}
theorem eq3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result3 s x rho = state3 s x rho := by
  simp only [FirstTable.result3, FirstTable.args3, eq2, state2, state3,
    First3.outputs, First3.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  rfl
def state4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10181, stack := [(MachineState.readWord (memory2 s) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory26 s}
theorem eq4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result4 s x rho = state4 s x rho := by
  simp only [FirstTable.result4, FirstTable.args4, eq3, state3, state4,
    First4.outputs, First4.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  rfl
def state5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10185, stack := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho, memory := memory27 s}
theorem eq5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    FirstTable.result5 s x rho = state5 s x rho := by
  simp only [FirstTable.result5, FirstTable.args5, eq4, state4, state5,
    First5.outputs, First5.memory, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd,
    Nat.reduceLT, Option.getD_some]
  rfl
theorem actual_memory (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    (FirstTable.result5 s x rho).memory = memory27 s := by rw [eq5]; rfl
#print axioms actual_memory
end RipemdSubmission20261101.FirstMemory
