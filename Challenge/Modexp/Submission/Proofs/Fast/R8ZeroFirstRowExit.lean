import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowModel

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro

def quotientA : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .MLOAD, .op .MUL]
def quotientB : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨13, by decide⟩), .op .MULMOD, .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADDMOD]
/-- The back-jump feed (E4): the second-loop join 3791 is pushed as an immediate (the
cell, which used to hold it, now carries the row carry). -/
def quotientJump : List Instr := [.push 2 3791, .op .JUMP]
def exitProgram : List Instr := (quotientA ++ quotientB) ++ quotientJump

def endFrame (flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) : List UInt256 :=
  flag :: P :: hd :: tt :: next :: stride :: M :: target :: inv :: m0 :: UInt256.ofNat 2336 ::
    m96 :: m64 :: m32 :: x :: rest

theorem run_quotientA (s : State)
    (pc flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory 2336
    runInstructions quotientA
      { s with pc := pc, stack := endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := advancePC 4 pc,
                  stack := (t0*inv) :: endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have ht : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [quotientA, endFrame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h15, h16, h17, State.activeWordsAfterUInt256, ht, hT, advancePC]

theorem run_quotientB (s : State)
    (pc mu flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory 2336
    runInstructions quotientB
      { s with pc := pc, stack := mu :: endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := advancePC 8 pc,
                  stack := UInt256.addMod t0 (UInt256.mulMod m0 mu M) M :: mu ::
                    endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have h19 : rest.length + 19 < 1024 := by omega
  have h20 : rest.length + 20 < 1024 := by omega
  have ht : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [quotientB, endFrame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h16, h17, h18, h19, h20, State.activeWordsAfterUInt256, ht, hT, advancePC]

theorem run_quotientJump (s : State)
    (pc c0 mu flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3791 = true) :
    runInstructions quotientJump
      { s with pc := pc, stack := c0 :: mu :: endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := UInt256.ofNat 3791,
                  stack := c0 :: mu :: endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have h3791 : (3791 : UInt256).toNat = 3791 := by decide
  have heq3791 : (3791 : UInt256) = UInt256.ofNat 3791 := by decide
  simp [quotientJump, endFrame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h17, h18, h3791, heq3791, hjump]

theorem run_exit (s : State)
    (pc flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3791 = true) :
    let t0 := MachineState.readWord s.memory 2336
    let mu := t0*inv
    runInstructions exitProgram
      { s with pc := pc, stack := endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := UInt256.ofNat 3791,
                  stack := UInt256.addMod t0 (UInt256.mulMod m0 mu M) M :: mu ::
                    endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  let t0 := MachineState.readWord s.memory 2336
  have h0 := run_quotientA s pc flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap hact
  have h1 := run_quotientB s (advancePC 4 pc) (t0*inv) flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap hact
  have h2 := run_quotientJump s (advancePC 12 pc)
    (UInt256.addMod t0 (UInt256.mulMod m0 (t0*inv) M) M) (t0*inv)
    flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  exact runInstructions_append_some _ _ _ _ _ h01 h2

#print axioms run_exit
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
