import Challenge.Modexp.Submission.Proofs.Fast.Ccb
import Challenge.Modexp.Submission.Proofs.Fast.CcbSeedPaths
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Generic execution of the width-selected CCB seed. The appendix performs
eight or sixteen doublings, then rejoins the unchanged CCB squaring loop with
five or four iterations. Arithmetic memory effects remain abstract contracts. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

def flag (n : Nat) : Nat := if 128 < 32 * n then 1 else 0
def doubles (n : Nat) : Nat := if 128 < 32 * n then 16 else 8
def squares (n : Nat) : Nat := if 128 < 32 * n then 4 else 5

theorem flag_le_one (n : Nat) : flag n ≤ 1 := by
  unfold flag
  split <;> omega

theorem doubles_pos (n : Nat) : 1 ≤ doubles n := by
  unfold doubles
  split <;> omega

theorem doubles_le_sixteen (n : Nat) : doubles n ≤ 16 := by
  unfold doubles
  split <;> omega

theorem squares_pos (n : Nat) : 1 ≤ squares n := by
  unfold squares
  split <;> omega

theorem squares_le_eight (n : Nat) : squares n ≤ 8 := by
  unfold squares
  split <;> omega

def loopStack (px n k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat (flag n), UInt256.ofNat px, ret] ++ rest

def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2298
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

def loopState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2311
           stack := loopStack px n k ret rest
           memory := mem }

def amCallState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1097
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 2322] ++ loopStack px n k ret rest
           memory := mem }

def retState (s : State) (mem : ByteArray) (px n k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2322
           stack := loopStack px n k ret rest
           memory := mem }

def exitState (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2331
           stack := loopStack px n 0 ret rest
           memory := mem }

