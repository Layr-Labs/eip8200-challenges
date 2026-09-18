import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowRuns
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowEnds
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowExit

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel CarryScratchAgreement

def program (next : UInt256) : List Instr :=
  (((diagonalProgram next ++ cellsProgram 6) ++ cellAB (UInt256.ofNat (SquareModel.aAddr 8 7)))
    ++ finishStore) ++ exitProgram

def initial (s : State) (pc hd ent stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc,
           stack := UInt256.ofNat 2592 :: hd :: UInt256.ofNat 2336 :: ent :: stride :: maxWord ::
             target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest }

/-- After the first-row program: the memory holds the seven cell sums (no scratch-word
store any more), the cell (the old `target` slot) holds the row carry, and the second
loop is entered at the join 3791 with the quotient words above the frame. -/
def result (s : State) (hd next stride inv m0 m96 m64 m32 : UInt256)
    (rest : List UInt256) : State :=
  let mem := (firstProduct s.memory).memory
  let t0 := MachineState.readWord mem 2336
  let mu := t0*inv
  { s with pc := UInt256.ofNat 3791, memory := mem,
           stack := UInt256.addMod t0 (UInt256.mulMod m0 mu maxWord) maxWord :: mu ::
             endFrame (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336)
               next stride maxWord (firstProduct s.memory).carry inv m0 m96 m64 m32
               (MachineState.readWord s.memory 2592) rest }

/-- Exact 246-byte straight-line first-row program, with its only code immediate
abstract. Incoming T and scratch memory and the cell are arbitrary. -/
theorem run_program (s : State)
    (pc hd ent next stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3791 = true) :
    runInstructions (program next) (initial s pc hd ent stride target inv m0 m96 m64 m32 aprev rest) =
      some (result s hd next stride inv m0 m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x+x
  let q6 := zeroRun (diagonal s.memory) bi 6
  let x7 := MachineState.readWord q6.memory (SquareModel.aAddr 8 7)
  have h0 := run_diagonal s pc hd ent next stride target inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := run_cells s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride
    (diagonal s.memory)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 6 (by decide)
  have h1b := run_cellAB { s with memory := q6.memory } (advancePC 198 pc) q6.carry bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord (SquareModel.aAddr 8 7)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) (by unfold SquareModel.aAddr; omega) hact
  have h2 := run_finishStore { s with memory := q6.memory } (advancePC 221 pc)
    (R4Math.zCarry x7 bi q6.carry maxWord) (R4Math.zSum x7 bi q6.carry) bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord target
    (inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hmem : MachineState.writeBytes q6.memory
      (Data.Bytes.natToBytesPadded (R4Math.zSum x7 bi q6.carry).toNat 32) 2112 =
      (firstProduct s.memory).memory := rfl
  have hcarry : R4Math.zCarry x7 bi q6.carry maxWord = (firstProduct s.memory).carry := rfl
  rw [hmem, hcarry] at h2
  have h3 := run_exit { s with memory := (firstProduct s.memory).memory } (advancePC 230 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord
    (firstProduct s.memory).carry inv m0 m96 m64 m32 x rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h01b := runInstructions_append_some _ _ _ _ _ h01 h1b
  have h012 := runInstructions_append_some _ _ _ _ _ h01b h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

theorem zeroed_first_overflow (s : State) (mem : ByteArray) :
    CarryRowModel.overflow (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry = UInt256.ofNat 0 := by
  unfold CarryRowModel.overflow
  rw [readWord_sqL1 _ 8 0 2080 _ (by decide) (Or.inl (by decide)),
    readWord_mpZeroed_tn, zero_add_word, lt_self_word]

#print axioms run_program
#print axioms zeroed_first_overflow
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
