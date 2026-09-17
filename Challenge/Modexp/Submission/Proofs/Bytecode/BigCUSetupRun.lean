import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMulRun

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- Exact U raw interval [236,271). -/
def setupProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 9248,
   .op .CALLDATASIZE,
   .push 0 0,
   .op .CALLDATACOPY,
   .push 1 64,
   .op .CALLDATALOAD,
   .push 1 32,
   .op .CALLDATALOAD,
   .push 0 0,
   .op .CALLDATALOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .ADD,
   .push 2 1024,
   .op .CALLDATACOPY,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .push 2 5120,
   .op .CALLDATACOPY,
   .push 0 0,
   .op (.Dup ⟨3, by decide⟩)]

/-- Exact U raw interval [271,290). -/
def zLoopProgram : List Instr :=
  [.op .JUMPDEST,
   .push 0 0,
   .op .SUB,
   .op .NOT,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1024,
   .op .ADD,
   .op .MLOAD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .OR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .push 2 273,
   .op .JUMPI]

/-- Exact U raw interval [290,295). -/
def zExitProgram : List Instr :=
  [.op .POP,
   .push 2 301,
   .op .JUMPI]

/-- Exact U raw interval [295,299). -/
def zeroRetProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨2, by decide⟩),
   .push 0 0,
   .op .RETURN]

/-- Exact U raw interval [299,310). -/
def nzProgram : List Instr :=
  [.op .JUMPDEST,
   .push 1 1,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 3071,
   .op .ADD,
   .op .MSTORE8,
   .op .POP,
   .push 0 0]

structure SetupJumps (code : ByteArray) : Prop where
  j236 : Decode.isValidJumpDest code 238 = true
  j271 : Decode.isValidJumpDest code 273 = true
  j295 : Decode.isValidJumpDest code 297 = true
  j299 : Decode.isValidJumpDest code 301 = true

structure SetupBlocks (artifact : ProgramArtifact) where
  setup : Block artifact .Osaka 238 setupProgram
  zLoop : Block artifact .Osaka 273 zLoopProgram
  zExit : Block artifact .Osaka 292 zExitProgram
  zeroRet : Block artifact .Osaka 297 zeroRetProgram
  nz : Block artifact .Osaka 301 nzProgram
  jumps : SetupJumps artifact.code

theorem run_zLoop_back (s : State) (i : Nat) (acc : UInt256)
    (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hi : 2 ≤ i) (hi' : i ≤ 1024)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions zLoopProgram
      (st s 273 (UInt256.ofNat i :: acc :: rest) mem AW) =
        some (st s 273 (UInt256.ofNat (i - 1) ::
          UInt256.lor acc (MachineState.readWord mem (1024 + (i - 1))) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat i (by omega) (by omega)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat (i - 1) =
      UInt256.ofNat (1024 + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 1024 + (i - 1) < LIM := by simp only [LIM]; omega
  have h2 : i - 1 < LIM := by simp only [LIM]; omega
  have hne : ¬ i - 1 = 0 := by omega
  have haw : MachineState.activeWordsAfter 289 (1024 + (i - 1)) 32 = 289 :=
    aw_keep _ _ (by omega)
  u_run [zLoopProgram, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, zero_lit, hdec, hadd, h1, h2, hne, haw]

theorem run_zLoop_exit (s : State) (acc : UInt256)
    (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions zLoopProgram
      (st s 273 (UInt256.ofNat 1 :: acc :: rest) mem AW) =
        some (st s 292 (UInt256.ofNat 0 ::
          UInt256.lor acc (MachineState.readWord mem 1024) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat 1 (by omega) (by norm_num)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat 0 = UInt256.ofNat 1024 := by decide
  have haw : MachineState.activeWordsAfter 289 1024 32 = 289 := aw_keep _ _ (by omega)
  u_run [zLoopProgram, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, zero_lit, hdec, hadd, haw]

theorem run_zExit_nz (s : State) (acc : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hacc : acc.toNat ≠ 0)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions zExitProgram
      (st s 292 (UInt256.ofNat 0 :: acc :: rest) mem AW) =
        some (st s 301 rest mem AW) := by
  have hc := caps _ hcap
  u_run [zExitProgram, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, hacc]

theorem run_zExit_zero (s : State) (acc : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hacc : acc.toNat = 0)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions zExitProgram
      (st s 292 (UInt256.ofNat 0 :: acc :: rest) mem AW) =
        some (st s 297 rest mem AW) := by
  have hc := caps _ hcap
  u_run [zExitProgram, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, hacc]

theorem run_zeroRet (s : State) (bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions zeroRetProgram
      (st s 297 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (rt s 300 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW (MachineState.readPadded mem 0 ml)) := by
  have hc := caps _ hcap
  have h1 : ml < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  u_run [zeroRetProgram, zero_lit, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, h1, haw]

/-! ## Base reduction call and exponent loop -/

theorem run_nz (s : State) (bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hJ : SetupJumps s.executionEnv.code) :
    runInstructions nzProgram
      (st s 301 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 312 (UInt256.ofNat 0 :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat 1]) (3071 + ml)) AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 3071 + UInt256.ofNat ml = UInt256.ofNat (3071 + ml) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 3071 + ml < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (3071 + ml) 1 = 289 := aw_keep _ _ (by omega)
  u_run [nzProgram, zero_lit, hc, hJ.j236, hJ.j271, hJ.j295, hJ.j299, hadd, h1, haw]

def setupMem (mem cd : ByteArray) (bl el ml : Nat) : ByteArray :=
  let m1 := MachineState.writeBytes mem (MachineState.readPadded cd cd.size 9248) 0
  let m2 := MachineState.writeBytes m1 (MachineState.readPadded cd (96 + (el + bl)) ml) 1024
  MachineState.writeBytes m2 (MachineState.readPadded cd 96 bl) 5120

def setupZeroProgram := setupProgram.take 5
def setupHeadsProgram := (setupProgram.drop 5).take 6
def setupMProgram := (setupProgram.drop 11).take 8
def setupBProgram := setupProgram.drop 19

theorem aw_first (aw : UInt256) (haw : aw.toNat ≤ 289) :
    MachineState.activeWordsAfter aw.toNat 0 9248 = 289 := by
  unfold MachineState.activeWordsAfter
  split
  · omega
  · dsimp only
    rw [show Nat.max aw.toNat ((0 + 9248 - 1) / 32 + 1) =
      max aw.toNat ((0 + 9248 - 1) / 32 + 1) from rfl]
    omega

theorem run_setupZero (s : State) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (hcap : stk.length < 1000) (haw : aw.toNat ≤ 289)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64) :
    runInstructions setupZeroProgram (st s 238 stk mem aw) =
      some (st s 245 stk (MachineState.writeBytes mem
        (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size 9248) 0) AW) := by
  have hc := caps _ hcap
  have hc0 : stk.length < 1024 := by omega
  have h0 := aw_first aw haw
  have h1 : s.executionEnv.calldata.size < LIM := by simp only [LIM]; omega
  u_run [setupZeroProgram, setupProgram, hc, hc0, zero_lit, h0, h1]

theorem run_setupHeads (s : State) (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (hcap : stk.length < 1000)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (he : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat el)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml) :
    runInstructions setupHeadsProgram (st s 245 stk mem AW) =
      some (st s 253 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) mem AW) := by
  have hc := caps _ hcap
  have hc0 : stk.length < 1024 := by omega
  u_run [setupHeadsProgram, setupProgram, hc, hc0, zero_lit, hb, he, hm]

theorem run_setupM (s : State) (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (hcap : stk.length < 1000) (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) :
    runInstructions setupMProgram
      (st s 253 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) mem AW) =
      some (st s 264 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk)
        (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata
          (96 + (el + bl)) ml) 1024) AW) := by
  have hc := caps _ hcap
  have h1 : ml < LIM := by simp only [LIM]; omega
  have h2 : 96 + (el + bl) < LIM := by simp only [LIM]; omega
  have ha : UInt256.ofNat el + UInt256.ofNat bl = UInt256.ofNat (el + bl) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have ha2 : UInt256.ofNat 96 + UInt256.ofNat (el + bl) = UInt256.ofNat (96 + (el + bl)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have haw := aw_keep 1024 ml (by omega)
  u_run [setupMProgram, setupProgram, hc, h1, h2, ha, ha2, haw]

theorem run_setupB (s : State) (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (hcap : stk.length < 1000) (hbl : bl ≤ 1024) :
    runInstructions setupBProgram
      (st s 264 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) mem AW) =
      some (st s 273 (UInt256.ofNat ml :: UInt256.ofNat 0 :: UInt256.ofNat bl ::
        UInt256.ofNat el :: UInt256.ofNat ml :: stk)
        (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata 96 bl) 5120) AW) := by
  have hc := caps _ hcap
  have h1 : bl < LIM := by simp only [LIM]; omega
  have haw := aw_keep 5120 bl (by omega)
  u_run [setupBProgram, setupProgram, hc, zero_lit, h1, haw]

theorem run_setup (s : State) (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (hcap : stk.length < 1000) (hbl : bl ≤ 1024) (hel : el ≤ 1024)
    (hml : ml ≤ 1024) (haw : aw.toNat ≤ 289)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (he : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat el)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml) :
    runInstructions setupProgram (st s 238 stk mem aw) =
      some (st s 273 (UInt256.ofNat ml :: UInt256.ofNat 0 :: UInt256.ofNat bl ::
        UInt256.ofNat el :: UInt256.ofNat ml :: stk)
        (setupMem mem s.executionEnv.calldata bl el ml) AW) := by
  let m1 := MachineState.writeBytes mem
    (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size 9248) 0
  let m2 := MachineState.writeBytes m1 (MachineState.readPadded s.executionEnv.calldata
    (96 + (el + bl)) ml) 1024
  have g1 := run_setupZero s stk mem aw hcap haw hcds
  have g2 := run_setupHeads s bl el ml stk m1 hcap hb he hm
  have g3 := run_setupM s bl el ml stk m1 hcap hbl hel hml
  have g4 := run_setupB s bl el ml stk m2 hcap hbl
  have g34 := runInstructions_append_some _ _ _ _ _ g3 g4
  have g234 := runInstructions_append_some _ _ _ _ _ g2 g34
  have g := runInstructions_append_some _ _ _ _ _ g1 g234
  exact g

theorem lift_any {artifact : ProgramArtifact} {s : State}
    (env : Environment artifact .Osaka s) {pc : Nat} {instructions : List Instr}
    (block : Block artifact .Osaka pc instructions) {stk : List UInt256}
    {mem : ByteArray} {aw : UInt256} {t : State}
    (h : runInstructions instructions (st s pc stk mem aw) = some t) :
    Reach (st s pc stk mem aw) t := ⟨block.steps (env.transfer rfl rfl) rfl h⟩

#print axioms run_setup
#print axioms run_zLoop_back
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U

