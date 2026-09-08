import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryDefs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNRowPrograms MonproKNRowFrames MonproKNCache
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def cacheProgram : List Instr := [.op .JUMPDEST] ++ createProgram
def zeroProgram : List Instr := (entryProgram.drop 8).take 8
def pointersProgram : List Instr := entryProgram.drop 16

theorem entryProgram_eq : entryProgram = (cacheProgram ++ zeroProgram) ++ pointersProgram := rfl

def cached (s : State) (mem : ByteArray) (pa pb : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1948
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, negative32, allOnes, dst, ret] ++ rest
           memory := mem }

def cleared (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1961
           stack := [UInt256.ofNat (32*n), UInt256.ofNat pa, UInt256.ofNat pb,
             negative32, allOnes, dst, ret] ++ rest
           memory := mpZeroed s mem n }

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryDefs
