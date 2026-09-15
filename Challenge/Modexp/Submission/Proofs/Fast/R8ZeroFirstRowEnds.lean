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

def diagonalTail (next : UInt256) : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MSTORE,
   .push 2 next, .op (.Swap ⟨5, by decide⟩), .op .POP]

def diagonalProgram (next : UInt256) : List Instr :=
  R8RowZero.coreProgram ++ diagonalTail next

theorem run_diagonalTail (s : State) (pc c lo bi P hd ent next : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (diagonalTail next)
      { s with pc := pc, stack := c :: lo :: bi :: P :: hd :: UInt256.ofNat 2336 :: ent :: rest } =
    some { s with pc := advancePC 8 pc,
                  stack := c :: bi :: P :: hd :: UInt256.ofNat 2336 :: next :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded lo.toNat 32) 2336 } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have ht : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [diagonalTail, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h6, h7, h8, State.activeWordsAfterUInt256, ht, hT, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

theorem subtract_hi (a : UInt256) :
    (UInt256.mulMod a a maxWord - UInt256.lt (UInt256.mulMod a a maxWord) (a*a)) - (a*a) =
      mulHi a a := by
  have h := diagHi_self a
  have hs : ∀ x : UInt256, x - UInt256.ofNat 0 = x := by
    intro x
    change UInt256.mk (x.val - 0) = x
    rw [_root_.sub_zero]
  simpa only [SquareDiag.diagHi, lt_self_word, hs] using h

theorem run_diagonal (s : State)
    (pc hd ent next stride target inv m0 tl m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory 2592
    runInstructions (diagonalProgram next)
      { s with pc := pc,
               stack := UInt256.ofNat 2592 :: hd :: UInt256.ofNat 2336 :: ent :: stride :: maxWord ::
                 target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: aprev :: rest } =
    some { s with pc := advancePC 30 pc,
                  stack := (diagonal s.memory).carry :: (x+x) :: UInt256.ofNat 2592 :: hd ::
                    UInt256.ofNat 2336 :: next :: stride :: maxWord :: target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest,
                  memory := (diagonal s.memory).memory } := by
  let x := MachineState.readWord s.memory 2592
  have hn : (UInt256.ofNat 2592).toNat = 2592 := by decide
  have hP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (UInt256.ofNat 2592).toNat 32) = s.activeWords := by
    rw [hn]
    exact activeWords_fix s 2592 32 (by decide) (by decide) hact
  have h0 := R8RowZero.run_core s pc (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) ent stride maxWord target inv m0 tl m96 m64 m32 aprev rest hcap hP
  have h1 := run_diagonalTail s (advancePC 22 pc)
    ((UInt256.mulMod x x maxWord - UInt256.lt (UInt256.mulMod x x maxWord) (x*x)) - (x*x))
    (x*x) (x+x) (UInt256.ofNat 2592) hd ent next
    (stride :: maxWord :: target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : advancePC 8 (advancePC 22 pc) = advancePC 30 pc := (advancePC_add 22 8 pc).symm
  simpa only [diagonalProgram, diagonal, hn, subtract_hi, x, hpc] using h

/-- Two writes to disjoint windows commute. -/
theorem writeBytes_comm_disjoint (bs b1 b2 : ByteArray) (a1 a2 : Nat)
    (h1 : b1.size ≠ 0) (h2 : b2.size ≠ 0) (hd : a1 + b1.size ≤ a2 ∨ a2 + b2.size ≤ a1) :
    MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2 =
      MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1 := by
  have hsize : (MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2).size =
      (MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1).size := by
    rw [MachineState.writeBytes_size, MachineState.writeBytes_size, MachineState.writeBytes_size,
      MachineState.writeBytes_size, if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [MachineState.writeBytes_getElem?_getD]
  split_ifs <;> first | rfl | omega

/-- The tail of the first row after the last cell's arithmetic: the carry is stored to
`0x820`, the last cell's sum to `0x840` (store address widened to `PUSH3`), then the
loop counter is dropped and the quotient word starts at zero. -/
def finishStore : List Instr :=
  [.push 2 2080, .op .MSTORE, .push 3 2112, .op .MSTORE, .op .POP, .push 0 0]

theorem run_finishStore (s : State) (pc c u bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1019) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions finishStore
      { s with pc := pc, stack := c :: u :: bi :: rest } =
    some { s with pc := advancePC 11 pc, stack := UInt256.ofNat 0 :: rest,
                  memory := MachineState.writeBytes
                    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded c.toNat 32) 2080)
                    (Data.Bytes.natToBytesPadded u.toNat 32) 2112 } := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have ht : (2080 : UInt256).toNat = 2080 := by decide
  have ht2 : (2112 : UInt256).toNat = 2112 := by decide
  have hT := activeWords_fix s 2080 32 (by decide) (by decide) hact
  have hT2 := activeWords_fix s 2112 32 (by decide) (by decide) hact
  have hz : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp [finishStore, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h0, h1, h2, h3, h4, State.activeWordsAfterUInt256, ht, ht2, hT, hT2, hz, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

#print axioms run_finishStore
end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
