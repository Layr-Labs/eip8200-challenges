import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
set_option warningAsError true
set_option maxRecDepth 40000
namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareRows

def pcNx : Nat := 3888
def pcLast : Nat := 3997
/-- The four-limb exit into the lazy gate (`m4j`, inside `last`). -/
def pcM4j : Nat := 3999
/-- The four-limb loop head: R4. -/
def pcH2 : Nat := 4280

def frameStack (mem : ByteArray) (_n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 5297, MachineState.readWord mem 192, ent, m32, allOnes,
    MachineState.readWord mem 128, m64, m0, tl, m96, inv, UInt256.ofNat 0, aprev, pdst, ret] ++ rest

def frameAt (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := mem
    stack := frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest}

abbrev lastProgram := TnM128SquareExit.lastProgram
abbrev cProgram := TnM128SquareExit.cProgram
abbrev m4jProgram := TnM128SquareExit.m4jProgram
abbrev m4jBlock := TnM128SquareExit.m4jBlock
abbrev lastBlock := TnM128SquareExit.lastBlock
abbrev jumpDestLazy := TnM128SquareExit.jumpDestLazy

/-- The square counter lives in the frame's `pdst` slot, so a round no longer stores it in
memory.  `countMem` stays as the identity to keep the round memory models' shape. -/
def countMem (mem : ByteArray) (_c : Nat) : ByteArray := mem

theorem readWord_countMem_disjoint (mem : ByteArray) (c addr : Nat)
    (_hd : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (countMem mem c) addr = MachineState.readWord mem addr := rfl

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
