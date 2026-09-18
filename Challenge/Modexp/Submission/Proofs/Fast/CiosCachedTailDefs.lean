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

/-- The row loop's `JUMPI` (pc 4057) falls through into the R0 kernel-exit **dispatch**
(pc 4058), which flushes the carry cell `cy` to the scratch word (E14) and sends a
square (`hd = sq_row`) to `sq_exit` while every multiply falls through to `nx` (pc 4072). -/
def exitState (s : State) (mem : ByteArray) (pbi : UInt256) (pb _n : Nat)
    (hd ent cy dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := mem } (UInt256.ofNat 4058)
    ([pbi, hd, UInt256.ofNat (pb-32),
      ent, negative32, allOnes, cy, dst, ret] ++ rest)

/-- The `nx` side of the R0 dispatch (pc 4072): the 14 `POP`s that drop the row frame. -/
def nxState (s : State) (mem : ByteArray) (pbi : UInt256) (pb _n : Nat)
    (hd ent cy dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := mem } (UInt256.ofNat 4072)
    ([pbi, hd, UInt256.ofNat (pb-32),
      ent, negative32, allOnes, cy, dst, ret] ++ rest)

/-- The `nx` `JUMPDEST` itself (pc 4072): the last square jumps here from `sq_exit`. -/
def nxJdState (s : State) (mem : ByteArray) (pbi : UInt256) (pb _n : Nat)
    (hd ent cy dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := mem } (UInt256.ofNat 4072)
    ([pbi, hd, UInt256.ofNat (pb-32),
      ent, negative32, allOnes, cy, dst, ret] ++ rest)

/-- `sq_exit` (pc 4128): the in-kernel squaring loop keeps the row frame. -/
def sqExitState (s : State) (mem : ByteArray) (pbi : UInt256) (pb _n : Nat)
    (hd ent cy dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := mem } (UInt256.ofNat 4128)
    ([pbi, hd, UInt256.ofNat (pb-32),
      ent, negative32, allOnes, cy, dst, ret] ++ rest)

def cleanupProgram : List Instr := tailLoopProgram.take 3
def storeProgram : List Instr := (tailLoopProgram.drop 3).take 13
def testProgram : List Instr := tailLoopProgram.drop 16

theorem program_eq : tailLoopProgram = (cleanupProgram ++ storeProgram) ++ testProgram := rfl

def baseStack (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, paEnd, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest

def input (s : State) (c mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4039) ([c, mu, bi] ++ baseStack pbi paEnd pbEnd flag dst ret rest)

def cleaned (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed s (UInt256.ofNat 4034) ([c] ++ baseStack pbi paEnd pbEnd flag dst ret rest)

def stored (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c } (UInt256.ofNat 4051)
    (baseStack pbi paEnd pbEnd flag dst ret rest)

def result (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : State :=
  framed { s with memory := tailMem s.memory c }
    (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then paEnd
      else UInt256.ofNat 3949)
    (baseStack (negative32+pbi) paEnd pbEnd flag dst ret rest)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs
