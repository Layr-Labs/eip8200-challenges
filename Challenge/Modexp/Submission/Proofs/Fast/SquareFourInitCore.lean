import Challenge.Modexp.Submission.Proofs.Fast.SquareInit

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourInit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.SquareInit (storeWord Doubling)
open Challenge.Modexp.Submission.Proofs.Fast.SquareWords

def doubleWords (mem : ByteArray) : Nat → Doubling
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j+1 =>
    let d := doubleWords mem j
    let addr := 8960+32*(3-j)
    let x := MachineState.readWord d.memory addr
    ⟨storeWord d.memory addr (doubled x d.carry), highBit x⟩

def initMemory (mem : ByteArray) : ByteArray :=
  storeWord (storeWord (doubleWords mem 4).memory 8928 (doubleWords mem 4).carry)
    9280 (UInt256.ofNat 5191)

theorem from_words (mem : ByteArray) (j : Nat) :
    SquareInit.doubleFrom ⟨mem, UInt256.ofNat 0⟩ 4 j = doubleWords mem j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp : 7-(4+j) = 3-j := by omega
    simp only [SquareInit.doubleFrom, ih, hp, doubleWords]

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourInit
