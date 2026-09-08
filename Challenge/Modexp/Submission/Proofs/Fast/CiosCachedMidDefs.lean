import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CiosCachedMacCore CiosCached CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def storeProgram : List Instr := midProgram.take 12
def productProgram : List Instr := (midProgram.drop 12).take 28
def pointersProgram : List Instr := midProgram.drop 40

theorem program_eq : midProgram = (storeProgram ++ productProgram) ++ pointersProgram := rfl

def baseStack (bi pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest

def input (s : State) (paj ptj c bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4651) ([paj, ptj, c] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)

def stored (s : State) (c bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed { s with memory := midMem s.memory c } (UInt256.ofNat 4669)
    (baseStack bi pbi paEnd pbEnd flag dst ret rest)

def product (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4703)
    ([rowC0 s.memory n, rowMu s.memory n] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)

def result (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4719)
    ([UInt256.ofNat (32*n-64), UInt256.ofNat (8192+32*n),
      rowC0 s.memory n, rowMu s.memory n] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs
