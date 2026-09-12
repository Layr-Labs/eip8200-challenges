import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.EvmProof.Memory
import EvmSemantics.EVM.State
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def wordAt (s : State) (address : Nat) : UInt256 :=
  MachineState.readWord s.memory address

def hashAt32 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 832
    h1 := wordAt s 864
    h2 := wordAt s 896
    h3 := wordAt s 928
    h4 := wordAt s 960 }

def embedHashArray (a : Array UInt32) : Compression.EvmHashState :=
  { h0 := Word.ofUInt32 a[0]!
    h1 := Word.ofUInt32 a[1]!
    h2 := Word.ofUInt32 a[2]!
    h3 := Word.ofUInt32 a[3]!
    h4 := Word.ofUInt32 a[4]! }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
