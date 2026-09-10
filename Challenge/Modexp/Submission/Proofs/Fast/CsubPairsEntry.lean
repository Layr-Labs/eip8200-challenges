import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsEntry

theorem entry_odd_test (n : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32) :
    UInt256.isZero
      (UInt256.land (UInt256.ofNat 32) (UInt256.ofNat (8224 + 32 * n))) =
      UInt256.ofNat (n % 2) := by
  interval_cases n <;> decide

theorem peel_then_pairs (n : Nat) : n % 2 + 2 * (n / 2) = n := by
  omega

theorem two_pointer_steps (n j : Nat) (hj : j + 2 ≤ n) :
    affinePt n j - 64 = affinePt n (j + 2) := by
  unfold affinePt
  omega


open EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

def entryProgram : List Instr :=
  [Instr.op .JUMPDEST, Instr.push 2 9440, Instr.op .MLOAD,
   Instr.push 0 0, Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Dup ⟨0, by decide⟩), Instr.push 1 32, Instr.op .AND,
   Instr.op .ISZERO, Instr.push 2 2366, Instr.op .JUMPI]

def entryState (s : State) (memory : ByteArray) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 2225, memory := memory, stack := [dst, ret] ++ rest}

def enteredState (s : State) (memory : ByteArray) (n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (if n % 2 = 0 then 2241 else 2366)
    memory := memory
    stack := [UInt256.ofNat (8224 + 32*n), UInt256.ofNat 0, dst, ret] ++ rest}

theorem run_entry (s : State) (memory : ByteArray) (n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32*n))
    (hdest : Decode.isValidJumpDest s.executionEnv.code 2366 = true) :
    runRaw entryProgram (entryState s memory dst ret rest) =
      some (enteredState s memory n dst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have h2366 : (2366 : UInt256).toNat = 2366 := by decide
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := by decide
  have hactA : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hparity : (UInt256.land (32 : UInt256)
      (UInt256.ofNat (8224 + 32 * n))).isZero.isTrue = decide (n % 2 ≠ 0) := by
    interval_cases n <;> decide
  by_cases hz : n % 2 = 0 <;> simp (config := { maxSteps := 400000 })
    [runRaw, entryProgram, Challenge.EvmProof.Stepper.runInstr,
      entryState, enteredState, hc2, hc3, hc4, hc5, hc6, hrun,
      h9440, h2366, hzero, htl, hactA, hparity, hdest, hz,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Nat.mod_eq_of_lt,
      List.exchange]
  all_goals decide


end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsEntry
