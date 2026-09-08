import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailDefs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open MonproKNCache MonproKNRowPrograms
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def cleanupProgram : List Instr := tailProgram.take 5
def storeProgram : List Instr := (tailProgram.drop 5).take 14
def testProgram : List Instr := tailProgram.drop 19

theorem program_eq : tailProgram = (cleanupProgram ++ storeProgram) ++ testProgram := rfl

def baseStack (pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, paEnd, pbEnd, negative32, allOnes, dst, ret] ++ rest

def input (s : State) (pmj ptj c mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 2435) ([pmj, ptj, c, mu, bi] ++ baseStack pbi paEnd pbEnd dst ret rest)

def cleaned (s : State) (c pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 2440) ([c] ++ baseStack pbi paEnd pbEnd dst ret rest)

def stored (s : State) (c pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c } (UInt256.ofNat 2462)
    (baseStack pbi paEnd pbEnd dst ret rest)

def result (s : State) (c pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c }
    (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then UInt256.ofNat 1982
      else UInt256.ofNat 2471)
    (baseStack (negative32+pbi) paEnd pbEnd dst ret rest)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailDefs
