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
  ((diagonalProgram next ++ cellsProgram 7) ++ finishStore) ++ exitProgram

def initial (s : State) (pc hd ent stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc,
           stack := UInt256.ofNat 2592 :: hd :: UInt256.ofNat 2336 :: ent :: stride :: maxWord ::
             target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest }

def result (s : State) (hd next stride target inv m0 m96 m64 m32 : UInt256)
    (rest : List UInt256) : State :=
  let mem := firstMemory s.memory
  let t0 := MachineState.readWord mem 2336
  let mu := t0*inv
  { s with pc := target, memory := mem,
           stack := UInt256.addMod t0 (UInt256.mulMod m0 mu maxWord) maxWord :: mu ::
             endFrame (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336)
               next stride maxWord target inv m0 m96 m64 m32 (MachineState.readWord s.memory 2592) rest }

/-- Exact246-byte straight-line first-row program, with its only code immediate
and final computed target abstract. Incoming T and scratch memory are arbitrary. -/
theorem run_program (s : State)
    (pc hd ent next stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions (program next) (initial s pc hd ent stride target inv m0 m96 m64 m32 aprev rest) =
      some (result s hd next stride target inv m0 m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x+x
  have h0 := run_diagonal s pc hd ent next stride target inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := run_cells s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride
    (diagonal s.memory)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 7 (by decide)
  have h2 := run_finishStore { s with memory := (firstProduct s.memory).memory }
    (advancePC 226 pc) (firstProduct s.memory).carry bi
    (UInt256.ofNat 2592 :: hd :: UInt256.ofNat 2336 :: next :: stride :: maxWord :: target ::
      inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h3 := run_exit { s with memory := firstMemory s.memory } (advancePC 232 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord target
    inv m0 m96 m64 m32 x rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

/-- Full instruction semantics together with the exact old-model bridge. -/
theorem run_program_bridge (s : State)
    (pc hd ent next stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions (program next) (initial s pc hd ent stride target inv m0 m96 m64 m32 aprev rest) =
        some (result s hd next stride target inv m0 m96 m64 m32 rest) ∧
      Agree (result s hd next stride target inv m0 m96 m64 m32 rest).memory
        (midMem1 (sqL1 (mpZeroed s s.memory 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s s.memory 8) 8 0 (UInt256.ofNat 0)).carry) :=
  ⟨run_program s pc hd ent next stride target inv m0 m96 m64 m32 aprev rest hcap hact hjump,
    firstMemory_bridge s s.memory⟩

theorem zeroed_first_overflow (s : State) (mem : ByteArray) :
    CarryRowModel.overflow (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry = UInt256.ofNat 0 := by
  unfold CarryRowModel.overflow
  rw [readWord_sqL1 _ 8 0 2080 _ (by decide) (Or.inl (by decide)),
    readWord_mpZeroed_tn, zero_add_word, lt_self_word]

#print axioms run_program
#print axioms run_program_bridge
#print axioms zeroed_first_overflow
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
