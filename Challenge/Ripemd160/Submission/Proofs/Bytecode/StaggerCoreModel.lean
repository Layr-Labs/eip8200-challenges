import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
open EvmSemantics EvmSemantics.EVM PairedLaneUInt256Bridge Paired80WordRound
open Paired80WordBoolean Paired80WordRotate

def initial (memory : ByteArray) : WordLane :=
  ⟨MachineState.readWord memory 832, MachineState.readWord memory 864,
    MachineState.readWord memory 896, MachineState.readWord memory 928, MachineState.readWord memory 960⟩

def pairWord (l r : UInt256) : UInt256 := UInt256.lor (UInt256.shiftLeft r (UInt256.ofNat 80)) l
def pair (l r : WordLane) : WordLane :=
  ⟨pairWord l.a r.a, pairWord l.b r.b, pairWord l.c r.c, pairWord l.d r.d, pairWord l.e r.e⟩
def left (q : WordLane) : WordLane :=
  ⟨StaggerScalarWord.mask q.a, StaggerScalarWord.mask q.b, StaggerScalarWord.mask q.c,
    StaggerScalarWord.mask q.d, StaggerScalarWord.mask q.e⟩

def message (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (10 * StaggerTableLayout.pairIndices[i]!)
def right0 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true true 4 8 (MachineState.readWord memory 50) (UInt256.ofNat 1352829926) q
def right1 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true true 4 9 (MachineState.readWord memory 310) (UInt256.ofNat 1352829926) q
def right2 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true true 4 9 (MachineState.readWord memory 350) (UInt256.ofNat 1352829926) q
def left77 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 8 (MachineState.readWord memory 0) (UInt256.ofNat 2840853838) q
def left78 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 5 (MachineState.readWord memory 80) (UInt256.ofNat 2840853838) q
def left79 (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerScalarWord.step false false 4 6 (MachineState.readWord memory 140) (UInt256.ofNat 2840853838) q

def prologue (memory : ByteArray) (q : WordLane) : WordLane :=
  right2 memory (right1 memory (right0 memory q))
def paired (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerAlgorithm.fold (message memory) 77 (pair q (prologue memory q))
def epilogue (memory : ByteArray) (q : WordLane) : WordLane :=
  left79 memory (left78 memory (left77 memory (left q)))

def addResult (memory : ByteArray) (l r : UInt256) (haddr : Nat) : UInt256 :=
  StaggerScalarWord.mask (UInt256.add (UInt256.add l
    (UInt256.shiftRight r (UInt256.ofNat 80))) (MachineState.readWord memory haddr))
def rawHash (memory : ByteArray) (l r : WordLane) : Compression.EvmHashState :=
  ⟨addResult memory l.c r.d 864, addResult memory l.d r.e 896,
    addResult memory l.e r.a 928, addResult memory l.a r.b 960, addResult memory l.b r.c 832⟩
def tailMemory (memory : ByteArray) (l r : WordLane) : ByteArray :=
  let h := rawHash memory l r
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory 832 h.h0) 864 h.h1)
      896 h.h2) 928 h.h3) 960 h.h4

def resultMemory (memory : ByteArray) : ByteArray :=
  let q := paired memory (initial memory)
  tailMemory memory (epilogue memory q) q

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
