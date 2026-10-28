import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerModeSeven
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadModel
open EvmSemantics EvmSemantics.EVM PairedLaneUInt256Bridge Paired144WordRound
open Paired144WordRotation

def initial (n : UInt256) : WordLane :=
  ⟨PadValues.load n 832, PadValues.load n 864,
    PadValues.load n 896, PadValues.load n 928, PadValues.load n 960⟩

def pairWord (l r : UInt256) : UInt256 := UInt256.lor (UInt256.shiftLeft r (UInt256.ofNat 144)) l
def pair (l r : WordLane) : WordLane :=
  ⟨pairWord l.a r.a, pairWord l.b r.b, pairWord l.c r.c, pairWord l.d r.d, pairWord l.e r.e⟩
def left (q : WordLane) : WordLane := q

def message (n : UInt256) (i : Nat) : UInt256 :=
  if i = 76 then
    PadValues.load n (18 * StaggerTableLayout.pairIndices[i]!)
  else PadValues.load n (18 * StaggerTableLayout.pairIndices[i]!)
def right0 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 8 (PadValues.load n 486) (UInt256.ofNat 1352829926) q
def right1 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 9 (PadValues.load n 162) (UInt256.ofNat 1352829926) q
def right2 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 9 (PadValues.load n 252) (UInt256.ofNat 1352829926) q
def left77 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step true false 4 8 (PadValues.load n 0) (UInt256.ofNat 2840853838) q
def left78 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step false false 4 5 (PadValues.load n 612) (UInt256.ofNat 2840853838) q
def left79 (n : UInt256) (q : WordLane) : WordLane :=
  StaggerScalarWord.step false false 4 6 (PadValues.load n 198) (UInt256.ofNat 2840853838) q

def prologue (n : UInt256) (q : WordLane) : WordLane :=
  right2 n (right1 n (right0 n q))
def paired (n : UInt256) (q : WordLane) : WordLane :=
  StaggerModeSeven.fold (message n) 77 (pair q (prologue n q))
def epilogue (n : UInt256) (q : WordLane) : WordLane :=
  left79 n (left78 n (left77 n (left q)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadModel
