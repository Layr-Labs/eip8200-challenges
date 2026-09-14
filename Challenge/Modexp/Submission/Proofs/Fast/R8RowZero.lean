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


def program : List Instr := coreProgram ++ tailProgram

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
  have h3765 : (3779 : UInt256) = UInt256.ofNat 3779 := by decide
  simp [tailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h6, h7, h8, List.exchange, State.activeWordsAfterUInt256, h3765, hact, hjump]

theorem run_program (s : State) (pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) = s.activeWords)
    (hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat w3.toNat 32) = s.activeWords)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    let x := MachineState.readWord s.memory P.toNat
    let lo := x * x
    let mm := UInt256.mulMod x x M
    runInstructions program
      { s with pc := pc, stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: aprev :: rest } =
    some { s with pc := ent,
                  stack := ((mm - UInt256.lt mm lo) - lo) :: (x + x) :: P :: hd :: w3 :: (UInt256.ofNat 3779) :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded lo.toNat 32) w3.toNat } := by
  dsimp only
  let x := MachineState.readWord s.memory P.toNat
  let lo := x * x
  let mm := UInt256.mulMod x x M
  have h0 := run_core s pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev rest hcap hactP
  have h1 := run_tail s (advancePC 22 pc)
    ((mm - UInt256.lt mm lo) - lo) lo (x + x) P hd w3 ent
    (w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest)
    (by simp only [List.length_cons]; omega) hactT hjump
  exact runInstructions_append_some _ _ _ _ _ h0 h1

open Monpro CiosCached SquareModel

private theorem add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add]
  simp only [show (UInt256.ofNat 0).toNat = 0 by rfl, Nat.add_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt a.val.isLt

private theorem zero_add (a : UInt256) : UInt256.ofNat 0 + a = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add]
  simp only [show (UInt256.ofNat 0).toNat = 0 by rfl, Nat.add_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt a.val.isLt

private theorem sub_zero (a : UInt256) : a - UInt256.ofNat 0 = a := by
  change UInt256.mk (a.val - 0) = a
  rw [_root_.sub_zero]

private theorem lt_self (a : UInt256) : UInt256.lt a a = UInt256.ofNat 0 := by
  simp [UInt256.lt]

theorem run_rowZero (s : State) (mem : ByteArray) (pc : UInt256) (e : Nat)
    (inv m0 tl m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord mem 2336 = UInt256.ofNat 0)
    (hjump : Decode.isValidJumpDest s.executionEnv.code e = true)
    (_he : e + 37 < 2 ^ 256) (hentry : e + 37 = 3779) :
    runInstructions program
      { outState s mem 2368 8 0 (UInt256.ofNat 4436) (UInt256.ofNat e) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: rest) with pc := pc } =
    some (l1Q e s (sqPro mem 8 0 (UInt256.ofNat 0))
      (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 8 0
      (UInt256.ofNat 4436) (UInt256.ofNat (e + 37)) inv m0
      (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: rest)) := by
  let s' : State := { s with memory := mem }
  have hp : (UInt256.ofNat 2592).toNat = 2592 := by decide
  have hP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat 2592).toNat 32) = s'.activeWords := by
    rw [hp]
    exact activeWords_fix s' 2592 32 (by decide) (by decide) hact
  have h2336 : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat 2336 32) = s'.activeWords :=
    activeWords_fix s' 2336 32 (by decide) (by decide) hact
  have hj : Decode.isValidJumpDest s'.executionEnv.code (UInt256.ofNat e).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hjump
  have h := run_program s' pc (UInt256.ofNat 2592) (UInt256.ofNat 4436) (UInt256.ofNat 2336)
    (UInt256.ofNat e) negative32 allOnes (l2Target 8) inv m0 tl m96 m64 m32 aprev rest hcap hP hT hj
  have hnext : UInt256.ofNat 3779 = UInt256.ofNat (e + 37) := by rw [hentry]
  simpa only [h2336, hnext, s', hp, outState, ptrAt_zero, l1Q, sqPro_eq, sqB2, sqX, aAddr, tAddr,
    hzero, add_zero, sub_zero, lt_self, zero_add, allOnes, maxWord,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append] using h

def block : Block Artifact.submissionArtifact .Osaka 5296 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4052 28 5296 program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5296 = true :=
  Artifact.isValidJumpDest_index 4052 (by rfl)

def gasSteps_prologue (s : State) (mem : ByteArray) (e : Nat)
    (inv m0 tl m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord mem 2336 = UInt256.ofNat 0)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode e = true)
    (he : e + 37 < 2 ^ 256) (hentry : e + 37 = 3779) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4436) (UInt256.ofNat e) inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: rest) with pc := UInt256.ofNat 5296 }
      (l1Q e s (sqPro mem 8 0 (UInt256.ofNat 0))
        (sqB2 (sqX mem 8 0) (UInt256.ofNat 0)) 2368 8 0
        (UInt256.ofNat 4436) (UInt256.ofNat (e + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX mem 8 0 :: rest)) :=
  SquareRow.stepsOf block
    (run_rowZero s mem (UInt256.ofNat 5296) e inv m0 tl m96 m64 m32 aprev rest hcap hact hzero
      (by rw [hcode]; exact hjump) he hentry) rfl hcode hfork hrun hnp

#print axioms run_rowZero
#print axioms run_program
#print axioms run_head
#print axioms run_math
#print axioms run_core
#print axioms run_tail
end Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
