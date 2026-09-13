import YulEvmCompiler.BytesLemmas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Cleanup
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def write (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

def memory (m : ByteArray) : ByteArray :=
  write (write m 22 27) 26 24

theorem read_write (m : ByteArray) (address writeAt : Nat) (value : UInt256)
    (h : writeAt + 32 ≤ address) :
    MachineState.readWord (write m writeAt value) address = MachineState.readWord m address := by
  apply Memory.readWord_writeBytes_disjoint
  right
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

@[simp] theorem read_memory (m : ByteArray) (address : Nat) (h : 58 ≤ address) :
    MachineState.readWord (memory m) address = MachineState.readWord m address := by
  simp (discharger := omega) only [memory, read_write]

@[simp] theorem hash_memory (m : ByteArray) :
    StackMemory.hashAt (memory m) = StackMemory.hashAt m := by
  simp only [StackMemory.hashAt, read_memory m 832 (by decide),
    read_memory m 864 (by decide), read_memory m 896 (by decide),
    read_memory m 928 (by decide), read_memory m 960 (by decide)]

#print axioms read_memory
#print axioms hash_memory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Cleanup
