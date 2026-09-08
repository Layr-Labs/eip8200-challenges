import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidDefs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open MonproKNCache MonproKNRowPrograms
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def storeProgram : List Instr := midProgram.take 13
def productProgram : List Instr := (midProgram.drop 13).take 28
def pointersProgram : List Instr := midProgram.drop 41

theorem program_eq : midProgram = (storeProgram ++ productProgram) ++ pointersProgram := rfl

def baseStack (bi pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [bi, pbi, paEnd, pbEnd, negative32, allOnes, dst, ret] ++ rest

def input (s : State) (paj ptj c bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 2008) ([paj, ptj, c] ++ baseStack bi pbi paEnd pbEnd dst ret rest)

def stored (s : State) (c bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed { s with memory := midMem s.memory c } (UInt256.ofNat 2027)
    (baseStack bi pbi paEnd pbEnd dst ret rest)

def product (s : State) (n : Nat) (bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 2061)
    ([rowC0 s.memory n, rowMu s.memory n] ++ baseStack bi pbi paEnd pbEnd dst ret rest)

def result (s : State) (n : Nat) (bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 2077)
    ([UInt256.ofNat (32*n-64), UInt256.ofNat (8192+32*n),
      rowC0 s.memory n, rowMu s.memory n] ++ baseStack bi pbi paEnd pbEnd dst ret rest)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidDefs
