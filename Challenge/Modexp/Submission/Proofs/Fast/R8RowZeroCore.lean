import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def coreProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .POP,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .SUB,
   .op .SUB]

def tailProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MSTORE,
   .push 2 3779, .op (.Swap ⟨5, by decide⟩), .op .JUMP]


def headProgram : List Instr := coreProgram.take 8
def mathProgram : List Instr := coreProgram.drop 8

theorem run_head (s : State) (pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) = s.activeWords) :
    let x := MachineState.readWord s.memory P.toNat
    runInstructions headProgram
      { s with pc := pc, stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: aprev :: rest } =
    some { s with pc := advancePC 8 pc,
                  stack := (x + x) :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  simp [headProgram, coreProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h14, h15, h16, h17, State.activeWordsAfterUInt256, hactP, List.exchange, advancePC]

theorem run_math (s : State) (pc b2 P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) :
    let lo := x * x
    let mm := UInt256.mulMod x x M
    runInstructions mathProgram
      { s with pc := pc, stack := b2 :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest } =
    some { s with pc := advancePC 14 pc,
                  stack := ((mm - UInt256.lt mm lo) - lo) :: lo :: b2 :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest } := by
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have h19 : rest.length + 19 < 1024 := by omega
  have h20 : rest.length + 20 < 1024 := by omega
  simp [mathProgram, coreProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h15, h16, h17, h18, h19, h20, List.exchange, advancePC]

theorem run_core (s : State) (pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) = s.activeWords) :
    let x := MachineState.readWord s.memory P.toNat
    let lo := x * x
    let mm := UInt256.mulMod x x M
    runInstructions coreProgram
      { s with pc := pc, stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: aprev :: rest } =
    some { s with pc := advancePC 22 pc,
                  stack := ((mm - UInt256.lt mm lo) - lo) :: lo :: (x + x) :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest } := by
  dsimp only
  let x := MachineState.readWord s.memory P.toNat
  have h0 := run_head s pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev rest hcap hactP
  have h1 := run_math s (advancePC 8 pc) (x+x) P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 x rest hcap
  exact runInstructions_append_some _ _ _ _ _ h0 h1

theorem run_tail (s : State) (pc C lo b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat w3.toNat 32) = s.activeWords)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions tailProgram
      { s with pc := pc, stack := C :: lo :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := ent,
                  stack := C :: b2 :: P :: hd :: w3 :: (UInt256.ofNat 3779) :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded lo.toNat 32) w3.toNat } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h3779 : (3779 : UInt256) = UInt256.ofNat 3779 := by decide
  simp [tailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h6, h7, h8, List.exchange, State.activeWordsAfterUInt256, h3779, hact, hjump]

end Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
