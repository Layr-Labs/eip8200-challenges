import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMul

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- Exact U raw interval [310,321). -/
def eGuardProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .push 1 3, .op .SHL, .op (.Dup ⟨1, by decide⟩),
   .op .EQ, .push 2 396, .op .JUMPI]

/-- Exact U raw interval [321,333). -/
def eSquareProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 2 3072, .op (.Dup ⟨0, by decide⟩), .push 2 335, .push 2 413,
   .op .JUMP]

/-- Exact U raw interval [333,364). -/
def e2Program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩), .push 0 0, .push 2 3072, .op .MCOPY,
   .op (.Dup ⟨0, by decide⟩), .push 1 3, .op .SHR, .push 0 0, .op .CALLDATALOAD, .op .ADD,
   .push 1 96, .op .ADD, .op .CALLDATALOAD, .op (.Dup ⟨1, by decide⟩), .push 1 7, .op .AND,
   .op .SHL, .push 1 255, .op .SHR, .op .ISZERO, .push 2 388, .op .JUMPI]

/-- Exact U raw interval [364,379). -/
def eMulProgram : List Instr :=
  [.push 0 0, .op .CALLDATALOAD, .push 2 5120, .push 2 3072, .push 2 381, .push 2 413, .op .JUMP]

/-- Exact U raw interval [379,386). -/
def e4Program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩), .push 0 0, .push 2 3072, .op .MCOPY]

/-- Exact U raw interval [386,394). -/
def e3Program : List Instr :=
  [.op .JUMPDEST, .push 1 1, .op .ADD, .push 2 312, .op .JUMP]

/-- Exact U raw interval [394,411). -/
def e9Program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩), .push 2 3072, .push 0 0, .op .MCOPY, .push 2 8192,
   .push 2 297, .push 2 484, .op .JUMP]

structure ExpJumps (code : ByteArray) : Prop where
  j295 : Decode.isValidJumpDest code 297 = true
  j310 : Decode.isValidJumpDest code 312 = true
  j333 : Decode.isValidJumpDest code 335 = true
  j379 : Decode.isValidJumpDest code 381 = true
  j386 : Decode.isValidJumpDest code 388 = true
  j394 : Decode.isValidJumpDest code 396 = true
  j411 : Decode.isValidJumpDest code 413 = true
  j482 : Decode.isValidJumpDest code 484 = true

structure ExpBlocks (artifact : ProgramArtifact) where
  eGuard : Block artifact .Osaka 312 eGuardProgram
  eSquare : Block artifact .Osaka 323 eSquareProgram
  e2 : Block artifact .Osaka 335 e2Program
  eMul : Block artifact .Osaka 366 eMulProgram
  e4 : Block artifact .Osaka 381 e4Program
  e3 : Block artifact .Osaka 388 e3Program
  e9 : Block artifact .Osaka 396 e9Program
  jumps : ExpJumps artifact.code

theorem run_eGuard_done (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hel : el ≤ 1024)
    (hi : i = el * 8)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions eGuardProgram
      (st s 312 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 396 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat el (by omega)
  have heq := eq_ofNat_toNat i (el * 8) (by omega) (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (el * 8))).toNat ≠ 0 := by
    rw [heq, if_pos hi]; norm_num
  u_run [eGuardProgram, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482, hshl, hcond]

theorem run_eGuard_go (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hel : el ≤ 1024)
    (hi : i ≠ el * 8) (hi' : i < 2 ^ 256)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions eGuardProgram
      (st s 312 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 323 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat el (by omega)
  have heq := eq_ofNat_toNat i (el * 8) hi' (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (el * 8))).toNat = 0 := by
    rw [heq, if_neg hi]
  u_run [eGuardProgram, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482, hshl, hcond]

theorem run_eSquare (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions eSquareProgram
      (st s 323 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 413 (UInt256.ofNat 335 :: UInt256.ofNat 3072 :: UInt256.ofNat 3072 ::
          UInt256.ofNat ml :: UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  u_run [eSquareProgram, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482]


def eCopyProgram := e2Program.take 5
def eReadProgram := (e2Program.drop 5).take 9
def eBitProgram := (e2Program.drop 14).take 6
def eBranchProgram := e2Program.drop 20

theorem run_eCopy (s : State) (i el ml : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hml : ml ≤ 1024) :
    runInstructions eCopyProgram
      (st s 335 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
    some (st s 342 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
      (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  have hc := caps _ hcap
  have h1 : ml < LIM := by simp only [LIM]; omega
  have ha := aw_keep 0 ml (by omega)
  have hb := aw_keep 3072 ml (by omega)
  u_run [eCopyProgram, e2Program, hc, zero_lit, h1, ha, hb]

theorem run_eRead (s : State) (i bl : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hi : i < 8192) (hbl : bl ≤ 1024)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl) :
    runInstructions eReadProgram (st s 342 (UInt256.ofNat i :: rest) mem AW) =
      some (st s 353 (MachineState.readWord s.executionEnv.calldata (96 + (bl + i / 8)) ::
        UInt256.ofNat i :: rest) mem AW) := by
  have hc := caps _ hcap
  have hs := shr3_ofNat i (by omega)
  have ha : UInt256.ofNat bl + UInt256.ofNat (i / 8) = UInt256.ofNat (bl + i / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have ha2 : UInt256.ofNat 96 + UInt256.ofNat (bl + i / 8) = UInt256.ofNat (96 + (bl + i / 8)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 96 + (bl + i / 8) < LIM := by simp only [LIM]; omega
  u_run [eReadProgram, e2Program, hc, zero_lit, hb, hs, ha, ha2, h1]

theorem run_eBit (s : State) (i a : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hi : i < 8192) :
    runInstructions eBitProgram
      (st s 353 (MachineState.readWord s.executionEnv.calldata a :: UInt256.ofNat i :: rest) mem AW) =
      some (st s 361 (bitWord s.executionEnv.calldata a (i % 8) :: UInt256.ofNat i :: rest) mem AW) := by
  have hc := caps _ hcap
  have ha := and7_ofNat i (by omega)
  u_run [eBitProgram, e2Program, hc, ha]

theorem run_eBranch_zero (s : State) (bit : UInt256) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hbit : bit.toNat = 0) (hJ : ExpJumps s.executionEnv.code) :
    runInstructions eBranchProgram (st s 361 (bit :: rest) mem AW) =
      some (st s 388 rest mem AW) := by
  have hc := caps _ hcap
  u_run [eBranchProgram, e2Program, hc, hbit, hJ.j386]

theorem run_eBranch_nz (s : State) (bit : UInt256) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hbit : bit.toNat ≠ 0) :
    runInstructions eBranchProgram (st s 361 (bit :: rest) mem AW) =
      some (st s 366 rest mem AW) := by
  have hc := caps _ hcap
  u_run [eBranchProgram, e2Program, hc, hbit]

theorem run_e2_skip (s : State) (i bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 990) (hml : ml ≤ 1024)
    (hi : i < 8192) (hbl : bl ≤ 1024)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (hbit : (bitWord s.executionEnv.calldata
      (96 + (bl + i / 8)) (i % 8)).toNat = 0)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions e2Program
      (st s 335 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 388 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  let m1 := MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072
  have g1 := run_eCopy s i el ml rest mem (by omega) hml
  have g2 := run_eRead s i bl (UInt256.ofNat el :: UInt256.ofNat ml :: rest) m1
    (by simp; omega) hi hbl hb
  have g3 := run_eBit s i (96 + (bl + i / 8)) (UInt256.ofNat el :: UInt256.ofNat ml :: rest)
    m1 (by simp; omega) hi
  have g4 := run_eBranch_zero s (bitWord s.executionEnv.calldata (96 + (bl + i / 8)) (i % 8))
    (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) m1
    (by simp; omega) hbit hJ
  have g34 := runInstructions_append_some _ _ _ _ _ g3 g4
  have g234 := runInstructions_append_some _ _ _ _ _ g2 g34
  have g := runInstructions_append_some _ _ _ _ _ g1 g234
  exact g

theorem run_e2_mul (s : State) (i bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 990) (hml : ml ≤ 1024)
    (hi : i < 8192) (hbl : bl ≤ 1024)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (hbit : (bitWord s.executionEnv.calldata
      (96 + (bl + i / 8)) (i % 8)).toNat ≠ 0)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions e2Program
      (st s 335 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 366 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  let m1 := MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072
  have g1 := run_eCopy s i el ml rest mem (by omega) hml
  have g2 := run_eRead s i bl (UInt256.ofNat el :: UInt256.ofNat ml :: rest) m1
    (by simp; omega) hi hbl hb
  have g3 := run_eBit s i (96 + (bl + i / 8)) (UInt256.ofNat el :: UInt256.ofNat ml :: rest)
    m1 (by simp; omega) hi
  have g4 := run_eBranch_nz s (bitWord s.executionEnv.calldata (96 + (bl + i / 8)) (i % 8))
    (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) m1
    (by simp; omega) hbit
  have g34 := runInstructions_append_some _ _ _ _ _ g3 g4
  have g234 := runInstructions_append_some _ _ _ _ _ g2 g34
  have g := runInstructions_append_some _ _ _ _ _ g1 g234
  exact g

theorem run_eMul (s : State) (i bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions eMulProgram
      (st s 366 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 413 (UInt256.ofNat 381 :: UInt256.ofNat 3072 :: UInt256.ofNat 5120 ::
          UInt256.ofNat bl :: UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  u_run [eMulProgram, hc, zero_lit, hb, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482]

theorem run_e4 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions e4Program
      (st s 381 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 388 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  u_run [e4Program, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482, zero_lit, h2, haw1, haw2]

theorem run_e3 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : i < 8192)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions e3Program
      (st s 388 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 312 (UInt256.ofNat (i + 1) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_comm]
  u_run [e3Program, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482, hadd]

theorem run_e9 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hJ : ExpJumps s.executionEnv.code) :
    runInstructions e9Program
      (st s 396 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 484 (UInt256.ofNat 297 :: UInt256.ofNat 8192 ::
          UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 3072 ml) 0) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  u_run [e9Program, hc, hJ.j295, hJ.j310, hJ.j333, hJ.j379, hJ.j386, hJ.j394, hJ.j411, hJ.j482, zero_lit, h2, haw1, haw2]


#print axioms run_e2_skip
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
