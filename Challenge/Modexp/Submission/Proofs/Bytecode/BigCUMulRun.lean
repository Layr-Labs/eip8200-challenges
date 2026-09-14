import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUnsignedGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- Exact U raw interval [411,419). -/
def mEntryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 1 64,
   .op .CALLDATALOAD,
   .op .CALLDATASIZE,
   .push 0 0,
   .op .CALLDATACOPY,
   .push 0 0]

/-- Exact U raw interval [419,430). -/
def mGuardProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 3,
   .op .SHL,
   .op (.Dup ⟨1, by decide⟩),
   .op .EQ,
   .push 2 475,
   .op .JUMPI]

/-- Exact U raw interval [430,438). -/
def mDoubleProgram : List Instr :=
  [.push 0 0,
   .push 2 438,
   .push 2 482,
   .op .JUMP]

/-- Exact U raw interval [438,459). -/
def m2Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 3,
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 7,
   .op .AND,
   .op .SHL,
   .push 1 255,
   .op .SHR,
   .op .ISZERO,
   .push 2 467,
   .op .JUMPI]

/-- Exact U raw interval [459,467). -/
def mAddProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 2 467,
   .push 2 482,
   .op .JUMP]

/-- Exact U raw interval [467,475). -/
def m3Program : List Instr :=
  [.op .JUMPDEST,
   .push 1 1,
   .op .ADD,
   .push 2 419,
   .op .JUMP]

/-- Exact U raw interval [475,482). -/
def m9Program : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .JUMP]

structure MulJumps (code : ByteArray) : Prop where
  j419 : Decode.isValidJumpDest code 419 = true
  j438 : Decode.isValidJumpDest code 438 = true
  j467 : Decode.isValidJumpDest code 467 = true
  j475 : Decode.isValidJumpDest code 475 = true
  j482 : Decode.isValidJumpDest code 482 = true

structure MulBlocks (artifact : ProgramArtifact) where
  mEntry : Block artifact .Osaka 411 mEntryProgram
  mGuard : Block artifact .Osaka 419 mGuardProgram
  mDouble : Block artifact .Osaka 430 mDoubleProgram
  m2 : Block artifact .Osaka 438 m2Program
  mAdd : Block artifact .Osaka 459 mAddProgram
  m3 : Block artifact .Osaka 467 m3Program
  m9 : Block artifact .Osaka 475 m9Program
  jumps : MulJumps artifact.code

syntax "u_run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| u_run [$ts,*]) =>
    `(tactic| simp (config := { maxSteps := 2000000 })
      [runInstructions, Challenge.EvmProof.Stepper.runInstr,
       st, rt, AW, LIM, bitWord, byteW,
       UInt256.isTrue, List.exchange, State.activeWordsAfterUInt256,
       State.activeWordsAfterUInt256_2, Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, $ts,*])

theorem run_mEntry (s : State) (ml : Nat) (ret x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hmsv : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions mEntryProgram
      (st s 411 (ret :: x :: y :: k :: rest) mem AW) =
        some (st s 419 (UInt256.ofNat 0 :: ret :: x :: y :: k :: rest)
          (MachineState.writeBytes mem
            (MachineState.readPadded s.executionEnv.calldata
              s.executionEnv.calldata.size ml) 0) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have h3 : s.executionEnv.calldata.size < LIM := by simp only [LIM]; omega
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  have haw1 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  u_run [mEntryProgram, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, zero_lit, hmsv, h2, h3, haw0, haw1]

theorem run_mGuard_done (s : State) (j k : Nat) (ret x y : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hk : k ≤ 1024) (hj : j = k * 8)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions mGuardProgram
      (st s 419 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest) mem AW) =
        some (st s 475 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat k (by omega)
  have heq := eq_ofNat_toNat j (k * 8) (by omega) (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat j) (UInt256.ofNat (k * 8))).toNat ≠ 0 := by
    rw [heq, if_pos hj]; norm_num
  u_run [mGuardProgram, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, hshl, hcond]

theorem run_mGuard_go (s : State) (j k : Nat) (ret x y : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hk : k ≤ 1024) (hj : j ≠ k * 8) (hj' : j < 2 ^ 256)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions mGuardProgram
      (st s 419 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest) mem AW) =
        some (st s 430 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat k (by omega)
  have heq := eq_ofNat_toNat j (k * 8) hj' (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat j) (UInt256.ofNat (k * 8))).toNat = 0 := by
    rw [heq, if_neg hj]
  u_run [mGuardProgram, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, hshl, hcond]

theorem run_mDouble (s : State) (j : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions mDoubleProgram
      (st s 430 (UInt256.ofNat j :: rest) mem AW) =
        some (st s 482 (UInt256.ofNat 438 :: UInt256.ofNat 0 :: UInt256.ofNat j :: rest)
          mem AW) := by
  have hc := caps _ hcap
  u_run [mDoubleProgram, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, zero_lit]

theorem run_m2_skip (s : State) (j yb : Nat) (ret x k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hj : j < 8192) (hy : yb ≤ 7168)
    (hbit : (bitWord mem (yb + j / 8) (j % 8)).toNat = 0)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions m2Program
      (st s 438 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest) mem AW) =
        some (st s 467 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat j (by omega)
  have hand := and7_ofNat j (by omega)
  have hadd : UInt256.ofNat yb + UInt256.ofNat (j / 8) = UInt256.ofNat (yb + j / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : yb + j / 8 < LIM := by simp only [LIM]; omega
  have h3 : j % 8 < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (yb + j / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  u_run [m2Program, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, hshr, hand, hadd, h1, h3, haw, hz]

theorem run_m2_add (s : State) (j yb : Nat) (ret x k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hj : j < 8192) (hy : yb ≤ 7168)
    (hbit : (bitWord mem (yb + j / 8) (j % 8)).toNat ≠ 0)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions m2Program
      (st s 438 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest) mem AW) =
        some (st s 459 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat j (by omega)
  have hand := and7_ofNat j (by omega)
  have hadd : UInt256.ofNat yb + UInt256.ofNat (j / 8) = UInt256.ofNat (yb + j / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : yb + j / 8 < LIM := by simp only [LIM]; omega
  have h3 : j % 8 < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (yb + j / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  u_run [m2Program, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, hshr, hand, hadd, h1, h3, haw, hz]

theorem run_mAdd (s : State) (j : Nat) (ret x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions mAddProgram
      (st s 459 (UInt256.ofNat j :: ret :: x :: y :: k :: rest) mem AW) =
        some (st s 482 (UInt256.ofNat 467 :: x :: UInt256.ofNat j :: ret :: x :: y :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  u_run [mAddProgram, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482]

theorem run_m3 (s : State) (j : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hj : j < 8192)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions m3Program
      (st s 467 (UInt256.ofNat j :: rest) mem AW) =
        some (st s 419 (UInt256.ofNat (j + 1) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 1 + UInt256.ofNat j = UInt256.ofNat (j + 1) := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_comm]
  u_run [m3Program, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, hadd]

theorem run_m9 (s : State) (j retPc : Nat) (x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hret : retPc < 2 ^ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code retPc = true)
    (hJ : MulJumps s.executionEnv.code) :
    runInstructions m9Program
      (st s 475 (UInt256.ofNat j :: UInt256.ofNat retPc :: x :: y :: k :: rest) mem AW) =
        some (st s retPc rest mem AW) := by
  have hc := caps _ hcap
  have h1 : retPc < LIM := by simp only [LIM]; omega
  u_run [m9Program, hc, hJ.j419, hJ.j438, hJ.j467, hJ.j475, hJ.j482, h1, hjump]


#print axioms run_m2_skip
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
