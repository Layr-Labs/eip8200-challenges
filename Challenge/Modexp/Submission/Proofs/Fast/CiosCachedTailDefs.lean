import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CiosCachedMacCore CiosCached CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def tailLoopProgram : List Instr := CiosCached.tailProgram.take 23
def exitProgram : List Instr := CiosCached.tailProgram.drop 23

def exitState (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := mem } (UInt256.ofNat 4790)
    ([pbi, UInt256.ofNat pa, UInt256.ofNat (pb-32),
      l1Target n, negative32, allOnes, l2Target n, dst, ret] ++ rest)

def cleanupProgram : List Instr := tailLoopProgram.take 3
def storeProgram : List Instr := (tailLoopProgram.drop 3).take 13
def testProgram : List Instr := tailLoopProgram.drop 16

theorem program_eq : tailLoopProgram = (cleanupProgram ++ storeProgram) ++ testProgram := rfl

def baseStack (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, paEnd, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest

def input (s : State) (c mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4761) ([c, mu, bi] ++ baseStack pbi paEnd pbEnd flag dst ret rest)

def cleaned (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4764) ([c] ++ baseStack pbi paEnd pbEnd flag dst ret rest)

def stored (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c } (UInt256.ofNat 4780)
    (baseStack pbi paEnd pbEnd flag dst ret rest)

def result (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c }
    (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then UInt256.ofNat 4169
      else UInt256.ofNat 4790)
    (baseStack (negative32+pbi) paEnd pbEnd flag dst ret rest)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs
