import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUnsigned
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- Exact U bytes [482,486). -/
def entryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 1024]

/-- Exact U bytes [486,492). -/
def initProgram : List Instr :=
  [.op .JUMPDEST, .push 1 1, .push 1 64, .op .CALLDATALOAD]

/-- Exact U bytes [492,527). -/
def cellProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .NOT, .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩), .op .ADD, .op .MLOAD, .push 0 0, .op .BYTE,
   .op (.Dup ⟨1, by decide⟩), .op .MLOAD, .push 0 0, .op .BYTE, .op .ADD,
   .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .ADD, .op .MLOAD, .push 0 0,
   .op .BYTE, .push 1 255, .op .SUB, .op .ADD, .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MSTORE8, .push 1 8, .op .SHR,
   .op (.Swap ⟨1, by decide⟩), .op .POP]

/-- Exact U bytes [527,532). -/
def guardProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 494, .op .JUMPI]

/-- Exact U bytes [532,537). -/
def decideProgram : List Instr :=
  [.op .POP, .push 2 548, .op .JUMPI]

/-- Exact U bytes [537,546). -/
def retryProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .op .POP, .push 2 8192, .push 2 488, .op .JUMP]

/-- Exact U bytes [546,551). -/
def finishProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op (.Swap ⟨0, by decide⟩), .op .POP, .op .JUMP]

syntax "unsigned_run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| unsigned_run [$ts,*]) =>
    `(tactic| simp (config := { maxSteps := 2000000 })
      [runInstructions, Challenge.EvmProof.Stepper.runInstr,
       st, AW, LIM, byteW, sumWord, nextCarry, writeByte,
       UInt256.isTrue, List.exchange, State.activeWordsAfterUInt256,
       State.activeWordsAfterUInt256_2, Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, $ts,*])

theorem run_entry (s : State) (ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) :
    runInstructions entryProgram (st s 484 (ret :: src :: rest) mem AW) =
      some (st s 488 (UInt256.ofNat 1024 :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [entryProgram, hc]

#check run_entry

theorem run_init (s : State) (ml : Nat) (z ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml) :
    runInstructions initProgram (st s 488 (z :: ret :: src :: rest) mem AW) =
      some (st s 494 (UInt256.ofNat ml :: UInt256.ofNat 1 :: z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [initProgram, hc, hm]

#check run_init

def loadYProgram : List Instr := cellProgram.take 10
def loadXProgram : List Instr := (cellProgram.drop 10).take 5
def loadZProgram : List Instr := (cellProgram.drop 15).take 6
def mathProgram : List Instr := (cellProgram.drop 21).take 5
def cellTailProgram : List Instr := cellProgram.drop 26

theorem run_loadY (s : State) (i src : Nat) (c z ret : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : 1 ≤ i) (hi' : i ≤ 1024)
    (hsrc : src ≤ 8192) :
    runInstructions loadYProgram
      (st s 494 (UInt256.ofNat i :: c :: z :: ret :: UInt256.ofNat src :: rest) mem AW) =
      some (st s 504 (byteW mem (src + (i - 1)) :: UInt256.ofNat (i - 1) :: c :: z :: ret ::
        UInt256.ofNat src :: rest) mem AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat i hi (by omega)
  have hadd : UInt256.ofNat src + UInt256.ofNat (i - 1) = UInt256.ofNat (src + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : src + (i - 1) < LIM := by simp only [LIM]; omega
  have h2 : i - 1 < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 (src + (i - 1)) 32 = 289 := aw_keep _ _ (by omega)
  unsigned_run [loadYProgram, cellProgram, hc, zero_lit, hdec, hadd, h1, h2, haw1]

#check run_loadY

theorem run_loadX (s : State) (i : Nat) (y c z ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : i < 1024) :
    runInstructions loadXProgram
      (st s 504 (y :: UInt256.ofNat i :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 509 ((byteW mem i + y) :: UInt256.ofNat i :: c :: z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  have h1 : i < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 i 32 = 289 := aw_keep _ _ (by omega)
  unsigned_run [loadXProgram, cellProgram, hc, zero_lit, h1, haw]

#check run_loadX

theorem run_loadZ (s : State) (i z : Nat) (xy c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : i < 1024) (hz : z ≤ 8192) :
    runInstructions loadZProgram
      (st s 509 (xy :: UInt256.ofNat i :: c :: UInt256.ofNat z :: ret :: src :: rest) mem AW) =
      some (st s 515 (byteW mem (z + i) :: xy :: UInt256.ofNat i :: c :: UInt256.ofNat z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat i + UInt256.ofNat z = UInt256.ofNat (z + i) := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_comm]
  have h1 : z + i < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (z + i) 32 = 289 := aw_keep _ _ (by omega)
  unsigned_run [loadZProgram, cellProgram, hc, zero_lit, hadd, h1, haw]

#check run_loadZ

theorem run_math (s : State) (zb xy i c z ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) :
    runInstructions mathProgram (st s 515 (zb :: xy :: i :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 521 ((c + ((UInt256.ofNat 255 - zb) + xy)) :: i :: c :: z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [mathProgram, cellProgram, hc]

#check run_math

theorem run_cell_tail (s : State) (i : Nat) (w c z ret src : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000) (hi : i < 1024) :
    runInstructions cellTailProgram
      (st s 521 (w :: UInt256.ofNat i :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 529 (UInt256.ofNat i :: nextCarry w :: z :: ret :: src :: rest)
        (writeByte mem i w) AW) := by
  have hc := caps _ hcap
  have h1 : i < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 i 1 = 289 := aw_keep _ _ (by omega)
  unsigned_run [cellTailProgram, cellProgram, hc, h1, haw]

#check run_cell_tail

theorem run_cell (s : State) (i src z : Nat) (c ret : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : 1 ≤ i) (hi' : i ≤ 1024)
    (hsrc : src ≤ 8192) (hz : z ≤ 8192) :
    let w := sumWord mem src z (i - 1) c
    runInstructions cellProgram
      (st s 494 (UInt256.ofNat i :: c :: UInt256.ofNat z :: ret :: UInt256.ofNat src :: rest) mem AW) =
      some (st s 529 (UInt256.ofNat (i - 1) :: nextCarry w :: UInt256.ofNat z :: ret ::
        UInt256.ofNat src :: rest) (writeByte mem (i - 1) w) AW) := by
  have hY := run_loadY s i src c (UInt256.ofNat z) ret rest mem hcap hi hi' hsrc
  have hX := run_loadX s (i - 1) (byteW mem (src + (i - 1))) c (UInt256.ofNat z) ret
    (UInt256.ofNat src) rest mem hcap (by omega)
  have hZ := run_loadZ s (i - 1) z (byteW mem (i - 1) + byteW mem (src + (i - 1))) c ret
    (UInt256.ofNat src) rest mem hcap (by omega) hz
  have hM := run_math s (byteW mem (z + (i - 1))) (byteW mem (i - 1) + byteW mem (src + (i - 1)))
    (UInt256.ofNat (i - 1)) c (UInt256.ofNat z) ret (UInt256.ofNat src) rest mem hcap
  have hT := run_cell_tail s (i - 1) (sumWord mem src z (i - 1) c) c (UInt256.ofNat z) ret
    (UInt256.ofNat src) rest mem hcap (by omega)
  have hMT := runInstructions_append_some _ _ _ _ _ hM hT
  have hZMT := runInstructions_append_some _ _ _ _ _ hZ hMT
  have hXZMT := runInstructions_append_some _ _ _ _ _ hX hZMT
  have h := runInstructions_append_some _ _ _ _ _ hY hXZMT
  exact h

#check run_cell

theorem run_guard_back (s : State) (i : Nat) (c z ret src : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hi : 1 ≤ i) (hi' : i ≤ 1024)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 494 = true) :
    runInstructions guardProgram (st s 529 (UInt256.ofNat i :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 494 (UInt256.ofNat i :: c :: z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  have hi0 : i < LIM := by simp only [LIM]; omega
  have hne : i ≠ 0 := by omega
  unsigned_run [guardProgram, hc, hjump, hi0, hne]

theorem run_guard_exit (s : State) (c z ret src : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000) :
    runInstructions guardProgram (st s 529 (UInt256.ofNat 0 :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 534 (UInt256.ofNat 0 :: c :: z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [guardProgram, hc]

theorem run_decide_yes (s : State) (c z ret src : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hc0 : c.toNat ≠ 0) (hjump : Decode.isValidJumpDest s.executionEnv.code 548 = true) :
    runInstructions decideProgram (st s 534 (UInt256.ofNat 0 :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 548 (z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [decideProgram, hc, hc0, hjump]

theorem run_decide_no (s : State) (c z ret src : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hc0 : c.toNat = 0) :
    runInstructions decideProgram (st s 534 (UInt256.ofNat 0 :: c :: z :: ret :: src :: rest) mem AW) =
      some (st s 539 (z :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [decideProgram, hc, hc0]

theorem run_retry (s : State) (ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 488 = true) :
    runInstructions retryProgram (st s 539 (UInt256.ofNat 1024 :: ret :: src :: rest) mem AW) =
      some (st s 488 (UInt256.ofNat 8192 :: ret :: UInt256.ofNat 1024 :: rest) mem AW) := by
  have hc := caps _ hcap
  unsigned_run [retryProgram, hc, hjump]

theorem run_finish (s : State) (z ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions finishProgram (st s 548 (z :: ret :: src :: rest) mem AW) =
      some { st s 548 rest mem AW with pc := ret } := by
  have hc := caps _ hcap
  unsigned_run [finishProgram, hc, hjump]

#print axioms run_cell
#print axioms run_retry
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned
