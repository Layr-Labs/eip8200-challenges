import Challenge.Modexp.Submission.Proofs.Fast.TnR8FirstRow
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel
open R8ZeroFirstRow

/-- The first-row frame with word 10 abstract: under the tl cut that slot holds `n0`, not `0x920`. -/
def endFrameC (flag P hd tt next stride M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) : List UInt256 :=
  flag :: P :: hd :: tt :: next :: stride :: M :: target :: inv :: m0 :: tl ::
    m96 :: m64 :: m32 :: x :: rest

/-- Exit by a code literal while keeping modulus[128] in the frame. -/
def quotientJump (destination : UInt256) : List Instr := [.push 2 destination, .op .JUMP]

/-- The quotient `mu = t0·inv` reads `t0` at the constant `0x920`. -/
def quotientAC : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .push 2 2336, .op .MLOAD, .op .MUL]

/-- The first reduction carry reads `n0` from frame word 10 (`DUP15`) and `t0` at `0x920`. -/
def quotientBC : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩), .op .MULMOD, .push 2 2336, .op .MLOAD, .op .ADDMOD]

def exitProgram (destination : UInt256) : List Instr :=
  (quotientAC ++ quotientBC) ++ quotientJump destination

theorem run_quotientAC (s : State)
    (pc flag P hd tt next stride M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory 2336
    runInstructions quotientAC
      { s with pc := pc, stack := endFrameC flag P hd tt next stride M target m64 m0 tl m96 inv m32 x rest } =
    some { s with pc := advancePC 6 pc,
                  stack := (t0*inv) :: endFrameC flag P hd tt next stride M target m64 m0 tl m96 inv m32 x rest } := by
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have ht : (2336 : UInt256).toNat = 2336 := by decide
  have ht' : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [quotientAC, endFrameC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h15, h16, h17, State.activeWordsAfterUInt256, ht, ht', hT, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  exact congrArg (pc + ·) (by decide)

theorem run_quotientBC (s : State)
    (pc mu flag P hd tt next stride M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory 2336
    runInstructions quotientBC
      { s with pc := pc, stack := mu :: endFrameC flag P hd tt next stride M target inv m0 tl m96 m64 m32 x rest } =
    some { s with pc := advancePC 10 pc,
                  stack := UInt256.addMod t0 (UInt256.mulMod tl mu M) M :: mu ::
                    endFrameC flag P hd tt next stride M target inv m0 tl m96 m64 m32 x rest } := by
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have h19 : rest.length + 19 < 1024 := by omega
  have h20 : rest.length + 20 < 1024 := by omega
  have ht : (2336 : UInt256).toNat = 2336 := by decide
  have ht' : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [quotientBC, endFrameC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h16, h17, h18, h19, h20, State.activeWordsAfterUInt256, ht, ht', hT, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  exact congrArg (pc + ·) (by decide)

theorem run_quotientJump (s : State)
    (pc c0 mu flag P hd tt next tn M m128 inv m0 tl m96 m64 m32 x destination : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    runInstructions (quotientJump destination)
      {s with pc := pc, stack := c0 :: mu :: endFrameC flag P hd tt next tn M m128 inv m0 tl m96 m64 m32 x rest} =
    some {s with pc := destination,
                 stack := c0 :: mu :: endFrameC flag P hd tt next tn M m128 inv m0 tl m96 m64 m32 x rest} := by
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [quotientJump, endFrameC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h17, h18, hjump]

theorem run_exit (s : State)
    (pc flag P hd tt next tn M m128 inv m0 tl m96 m64 m32 x destination : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    let t0 := MachineState.readWord s.memory 2336
    let mu := t0*inv
    runInstructions (exitProgram destination)
      {s with pc := pc, stack := endFrameC flag P hd tt next tn M m128 m64 m0 tl m96 inv m32 x rest} =
    some {s with pc := destination,
                 stack := UInt256.addMod t0 (UInt256.mulMod tl mu M) M :: mu ::
                   endFrameC flag P hd tt next tn M m128 m64 m0 tl m96 inv m32 x rest} := by
  let t0 := MachineState.readWord s.memory 2336
  have h0 := run_quotientAC s pc flag P hd tt next tn M m128 inv m0 tl m96 m64 m32 x rest hcap hact
  have h1 := run_quotientBC s (advancePC 6 pc) (t0*inv) flag P hd tt next tn M m128 m64 m0 tl m96 inv m32 x
    rest hcap hact
  have h2 := run_quotientJump s (advancePC 10 (advancePC 6 pc))
    (UInt256.addMod t0 (UInt256.mulMod tl (t0*inv) M) M) (t0*inv)
    flag P hd tt next tn M m128 m64 m0 tl m96 inv m32 x destination rest hcap hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  exact runInstructions_append_some _ _ _ _ _ h01 h2

/-- frq: the first row reads `a_0` at the constant `0xa20`; the row pointer stays on the stack. -/
def headProgramC : List Instr :=
  [.op .JUMPDEST, .push 2 2592, .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨15, by decide⟩), .op .POP, .op .ADD]

theorem run_headC (s : State) (pc P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory 2592
    runInstructions headProgramC
      { s with pc := pc, stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: aprev :: rest } =
    some { s with pc := advancePC 10 pc,
                  stack := (x + x) :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: x :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have ha : (2592 : UInt256).toNat = 2592 := by decide
  have ha' : (UInt256.ofNat 2592).toNat = 2592 := by decide
  have hA := activeWords_fix s 2592 32 (by decide) (by decide) hact
  simp [headProgramC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h14, h15, h16, h17, State.activeWordsAfterUInt256, ha, ha', hA, List.exchange, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  exact congrArg (pc + ·) (by decide)

/-- p2: the low diagonal word is stored at the constant `0x920` (frame word 3 holds `n1`). -/
def diagonalMathTailC (next : UInt256) : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL,
   .op (.Dup ⟨0, by decide⟩), .push 2 2336, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT,
   .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB,
   .push 2 next, .op (.Swap ⟨5, by decide⟩), .op .POP]

def diagonalProgramC (next : UInt256) : List Instr :=
  headProgramC ++ diagonalMathTailC next

private theorem sub_sub_comm_diagC (a b c : UInt256) : (a - b) - c = (a - c) - b := by
  apply Challenge.EvmProof.Word.word_ext
  change ((a.val - b.val) - c.val).val = ((a.val - c.val) - b.val).val
  rw [sub_right_comm]

theorem run_diagonalMathTailC (s : State)
    (pc bi P hd tt ent next stride target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let lo := x * x
    let mm := UInt256.mulMod x x maxWord
    runInstructions (diagonalMathTailC next)
      { s with pc := pc,
               stack := bi :: P :: hd :: tt :: ent :: stride :: maxWord ::
                 target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest } =
    some { s with pc := advancePC 23 pc,
                  stack := ((mm - UInt256.lt mm lo) - lo) :: bi :: P :: hd ::
                    tt :: next :: stride :: maxWord :: target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded lo.toNat 32) 2336 } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have h19 : rest.length + 19 < 1024 := by omega
  have h20 : rest.length + 20 < 1024 := by omega
  have ht : (2336 : UInt256).toNat = 2336 := by decide
  have ht' : (UInt256.ofNat 2336).toNat = 2336 := by decide
  have hT := activeWords_fix s 2336 32 (by decide) (by decide) hact
  simp [diagonalMathTailC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h14, h15, h16, h17, h18, h19, h20, State.activeWordsAfterUInt256, ht, ht', hT,
    advancePC]
  simp only [succ_eq_add, word_add_assoc, R4Math.gt_eq_lt, sub_sub_comm_diagC]
  exact ⟨congrArg (pc + ·) (by decide), trivial⟩

theorem run_diagonalC (s : State)
    (pc P hd tt ent next stride target inv m0 tl m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory 2592
    runInstructions (diagonalProgramC next)
      { s with pc := pc,
               stack := P :: hd :: tt :: ent :: stride :: maxWord ::
                 target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: aprev :: rest } =
    some { s with pc := advancePC 33 pc,
                  stack := (diagonal s.memory).carry :: (x+x) :: P :: hd ::
                    tt :: next :: stride :: maxWord :: target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest,
                  memory := (diagonal s.memory).memory } := by
  let x := MachineState.readWord s.memory 2592
  have h0 := run_headC s pc P hd tt ent stride maxWord target inv m0 tl m96 m64 m32 aprev rest hcap hact
  have h1 := run_diagonalMathTailC s (advancePC 10 pc) (x+x) P hd tt ent next stride target inv m0 tl
    m96 m64 m32 x rest hcap hact
  have h := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : advancePC 23 (advancePC 10 pc) = advancePC 33 pc := (advancePC_add 10 23 pc).symm
  simpa only [diagonalProgramC, diagonal, subtract_hi, x, hpc] using h

/-- `cellFastBC` with a `PUSH2` store address: the V1 layout narrows cells 6 and 7. -/
def cellFastBCNarrow (t : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 t, .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op .SUB, .op .SUB]

private theorem sub_sub_comm_word' (a b c : UInt256) : (a - b) - c = (a - c) - b := by
  apply Challenge.EvmProof.Word.word_ext
  change ((a.val - b.val) - c.val).val = ((a.val - c.val) - b.val).val
  rw [sub_right_comm]

private theorem gt_add_comm_word' (c lo : UInt256) : UInt256.gt lo (lo + c) = UInt256.gt c (c + lo) := by
  rw [R4Math.gt_eq_lt, R4Math.gt_eq_lt, Challenge.EvmProof.Word.word_add_comm lo c]
  exact (R4Math.lt_add_left_eq c lo).symm

theorem run_cellFastBCNarrow (s : State) (pc mm lo c : UInt256) (t : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1017)
    (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (cellFastBCNarrow (UInt256.ofNat t))
      { s with pc := pc, stack := mm :: lo :: c :: rest } =
    some { s with pc := advancePC 16 pc,
                  stack := ((UInt256.gt c (c + lo) - (UInt256.gt lo mm - mm)) - lo) :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (c + lo).toNat 32) t } := by
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have htn : (UInt256.ofNat t).toNat = t := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hT := activeWords_fix s t 32 (by decide) ht hact
  simp [cellFastBCNarrow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h2, h3, h4, h5, State.activeWordsAfterUInt256, htn, hT, advancePC]
  simp only [succ_eq_add, word_add_assoc, Nat.add_comm lo.toNat c.toNat, gt_add_comm_word', sub_sub_comm_word']
  exact ⟨trivial, congrArg (pc + ·) (by decide), trivial⟩

def cellProgramNarrow (a t : UInt256) : List Instr :=
  cellA a ++ cellFastBCNarrow t

theorem run_cellNarrow (s : State) (pc c bi w0 w1 w2 w3 w4 M : UInt256)
    (a t : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (ha : a + 32 ≤ 2816) (ht : t + 32 ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    let x := MachineState.readWord s.memory a
    runInstructions (cellProgramNarrow (UInt256.ofNat a) (UInt256.ofNat t))
      { s with pc := pc, stack := c :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest } =
    some { s with pc := advancePC 27 pc,
                  stack := R4Math.zCarry x bi c M :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest,
                  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (R4Math.zSum x bi c).toNat 32) t } := by
  let x := MachineState.readWord s.memory a
  have h0 := run_cellA s pc c bi w0 w1 w2 w3 w4 M a rest hcap ha hact
  have h1 := run_cellFastBCNarrow s (advancePC 11 pc) (UInt256.mulMod bi x M) (x*bi) c t
    (bi :: w0 :: w1 :: w2 :: w3 :: w4 :: M :: rest) (by simp only [List.length_cons]; omega) ht hact
  exact runInstructions_append_some _ _ _ _ _ h0 h1

theorem run_cellNarrowStep (s : State) (pc bi w0 w1 w2 w3 w4 : UInt256)
    (q : MacState) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat) (k : Nat) (hk : k + 1 ≤ 7) :
    runInstructions (cellProgramNarrow (UInt256.ofNat (SquareModel.aAddr 8 (k+1)))
        (UInt256.ofNat (Monpro.tAddr 8 (k+1))))
      { s with pc := pc, stack := (zeroRun q bi k).carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
               memory := (zeroRun q bi k).memory } =
    some { s with pc := advancePC 27 pc,
                  stack := (zeroRun q bi (k+1)).carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
                  memory := (zeroRun q bi (k+1)).memory } := by
  have h1 := run_cellNarrow { s with memory := (zeroRun q bi k).memory }
    pc (zeroRun q bi k).carry bi w0 w1 w2 w3 w4 maxWord
    (SquareModel.aAddr 8 (k+1)) (Monpro.tAddr 8 (k+1)) rest hcap
    (by unfold SquareModel.aAddr; omega) (by unfold Monpro.tAddr; omega) hact
  simpa only [zeroRun, zeroStep] using h1

/-- The V1 first-row cells: cells 1-5 store through `PUSH3`, cells 6-7 through `PUSH2`. -/
def cellsProgramV1 : List Instr :=
  (cellsProgramM128 5 ++
    cellProgramNarrow (UInt256.ofNat (SquareModel.aAddr 8 (5+1))) (UInt256.ofNat (Monpro.tAddr 8 (5+1)))) ++
    cellProgramNarrow (UInt256.ofNat (SquareModel.aAddr 8 (6+1))) (UInt256.ofNat (Monpro.tAddr 8 (6+1)))

theorem run_cellsV1 (s : State) (pc bi w0 w1 w2 w3 w4 : UInt256)
    (q : MacState) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions cellsProgramV1
      { s with pc := pc, stack := q.carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
               memory := q.memory } =
    some { s with pc := advancePC 189 pc,
                  stack := (zeroRun q bi 7).carry :: bi :: w0 :: w1 :: w2 :: w3 :: w4 :: maxWord :: rest,
                  memory := (zeroRun q bi 7).memory } := by
  have h0 := run_cellsM128 s pc bi w0 w1 w2 w3 w4 q rest hcap hact 5 (by decide)
  have h1 := run_cellNarrowStep s (advancePC (27*5) pc) bi w0 w1 w2 w3 w4 q rest hcap hact 5 (by decide)
  have h2 := run_cellNarrowStep s (advancePC 27 (advancePC (27*5) pc)) bi w0 w1 w2 w3 w4 q rest hcap hact
    6 (by decide)
  have h := runInstructions_append_some _ _ _ _ _ (runInstructions_append_some _ _ _ _ _ h0 h1) h2
  have hpc : advancePC 27 (advancePC 27 (advancePC (27*5) pc)) = advancePC 189 pc := by
    rw [← advancePC_add, ← advancePC_add]
  rw [hpc] at h
  exact h

/-- The first row's store as the V1 artifact spells it: the 7 cells of `cellsProgramV1`
(storing `t[1..7]` directly), and the 3-byte suffix swaps the carry with
`tn = 0` and drops `bi`. -/
def finishStoreNarrow : List Instr :=
  [.op (.Swap ⟨13, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem run_finishStoreNarrow (s : State)
    (pc c bi P hd tt next w7 M target w10 m0 tl m96 w14 tn x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) :
    runInstructions finishStoreNarrow
      {s with pc := pc, stack := c :: bi :: P :: hd :: tt :: next :: w7 :: M ::
        target :: w10 :: m0 :: tl :: m96 :: w14 :: tn :: x :: rest} =
    some {s with
      pc := advancePC 3 pc
      stack := tn :: P :: hd :: tt :: next :: w7 :: M ::
        target :: w10 :: m0 :: tl :: m96 :: w14 :: c :: x :: rest} := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [finishStoreNarrow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h14, h15, h16, advancePC]


def program (next destination : UInt256) : List Instr :=
  ((diagonalProgramC next ++ cellsProgramV1)
    ++ finishStoreNarrow) ++ exitProgram destination

/-- The first-row entry frame: row pointer `P` (`q`), frame word 3 `tt` (`n1`), word 10 `tl` (`n0`). -/
def initialC (s : State) (pc P hd tt ent stride target inv m0 tl m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc,
           stack := P :: hd :: tt :: ent :: stride :: maxWord ::
             target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: aprev :: rest }

def result (s : State) (P hd tt next m128 destination inv m0 tl m96 m64 m32 : UInt256)
    (rest : List UInt256) : State :=
  let q := firstProduct s.memory
  let t0 := MachineState.readWord q.memory 2336
  let mu := t0 * inv
  {s with
    pc := destination
    memory := q.memory
    stack := UInt256.addMod t0 (UInt256.mulMod tl mu maxWord) maxWord :: mu ::
      endFrameC (UInt256.ofNat 0) P hd tt
        next m32 maxWord m128 m64 m0 tl m96 inv q.carry
        (MachineState.readWord s.memory 2592) rest}

/-- The complete specialized first row for arbitrary incoming scratch memory
and zero incoming carry-register value. This is a universal instruction-semantics theorem. -/
theorem run_program (s : State)
    (pc P hd tt ent next m128 destination inv m0 tl m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    runInstructions (program next destination)
      (initialC s pc P hd tt ent m32 m128 m64 m0 tl m96 inv (UInt256.ofNat 0) aprev rest) =
      some (result s P hd tt next m128 destination inv m0 tl m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x + x
  have h0 := run_diagonalC s pc P hd tt ent next m32 m128 m64 m0 tl
    m96 inv (UInt256.ofNat 0) aprev rest hcap hact
  have h1 := run_cellsV1 s (advancePC 33 pc) bi P hd tt next m32
    (diagonal s.memory)
    (m128 :: m64 :: m0 :: tl :: m96 :: inv :: UInt256.ofNat 0 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hpc1 : advancePC 189 (advancePC 33 pc) = advancePC 222 pc := by
    rw [← advancePC_add]
  rw [hpc1] at h1
  have h2 := run_finishStoreNarrow {s with memory := (firstProduct s.memory).memory} (advancePC 222 pc)
    (firstProduct s.memory).carry bi
    P hd tt next m32 maxWord m128 m64 m0
    tl m96 inv (UInt256.ofNat 0) x rest hcap
  have hpc2 : advancePC 3 (advancePC 222 pc) = advancePC 225 pc := by
    rw [← advancePC_add]
  rw [hpc2] at h2
  have h3 := run_exit {s with memory := (firstProduct s.memory).memory} (advancePC 225 pc)
    (UInt256.ofNat 0) P hd tt next
    m32 maxWord m128 inv m0 tl m96 m64 (firstProduct s.memory).carry x destination rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

/-- Binding to the lane image: 205 instructions from index 3996 (pc 5092). -/
def block : Block TnM128CandidateArtifact.submissionArtifact .Osaka 5092
    (program (UInt256.ofNat 3616) (UInt256.ofNat 3862)) :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 3996 205 5092
    (program (UInt256.ofNat 3616) (UInt256.ofNat 3862))
    (by decide) (by rfl) (by rfl) (by decide)

#print axioms run_quotientAC
#print axioms run_exit
#print axioms run_program
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow
