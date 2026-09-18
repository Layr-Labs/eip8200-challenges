import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
set_option warningAsError true
set_option maxRecDepth 40000
namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareRows

def pcNx : Nat := 4152
def pcSqExit : Nat := 4208
def pcLast : Nat := 4230
def pcAgain : Nat := 4252
def pcH2 : Nat := 4242

def frameStack (mem : ByteArray) (_n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 4268, UInt256.ofNat 2336, ent, UInt256.ofNat 0, allOnes,
    MachineState.readWord mem 128, inv, m0, tl, m96, m64, m32, aprev, pdst, ret] ++ rest

def frameAt (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := mem
    stack := frameStack mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest}

abbrev sqExitProgram := TnM128SquareExit.sqExitProgram
abbrev lastProgram := TnM128SquareExit.lastProgram
abbrev sqExitBlock := TnM128SquareExit.sqExitBlock
abbrev lastBlock := TnM128SquareExit.lastBlock
abbrev jumpDestLazy := TnM128SquareExit.jumpDestLazy

def countMem (mem : ByteArray) (c : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded c 32) 2624

theorem readWord_countMem (mem : ByteArray) (c : Nat) (hc : c < 2 ^ 256) :
    MachineState.readWord (countMem mem c) 2624 = UInt256.ofNat c := by
  have h : (UInt256.ofNat c).toNat = c := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hc]
  calc MachineState.readWord (countMem mem c) 2624
      = MachineState.readWord
          (MachineState.writeBytes mem
            (Data.Bytes.natToBytesPadded (UInt256.ofNat c).toNat 32) 2624) 2624 := by
        rw [countMem, h]
    _ = UInt256.ofNat c := Challenge.EvmProof.Memory.readWord_writeWord mem 2624 (UInt256.ofNat c)

theorem readWord_countMem_disjoint (mem : ByteArray) (c addr : Nat)
    (hd : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (countMem mem c) addr = MachineState.readWord mem addr := by
  simp only [countMem]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [show (Data.Bytes.natToBytesPadded c 32).size = 32 by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
