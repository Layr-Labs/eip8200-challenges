import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# The `sq_row` prologue of the square rows (sqCP1m, new idx 3604..3653, pc 0x1266)

`sq_row` is the row head `hd = 4710` of a square call.  On the kernel row frame
`[P, hd, pb-32, ent, -32, M, l2T, …, aprev, …]` (`P` = pointer to `x = a_i`,
slot 14 = `aprev`) it

* loads `x`, parks it in slot 14 (`DUP1 SWAP15`), and computes `tb = SGT 0 aprev`;
* computes `f = x + tb`, `b2 = f + x`, `lo = x * f`, `hi` (512-bit high word via
  `MULMOD … 2^256-1`), stores `s = lo + t_i` at `P + 0x1840 = tAddr n i` and leaves the
  carry `C = [s < lo] + hi` above `b2`;
* advances the frame's `ent` slot by 38 and jumps to the old `ent` — the entry of the
  first-loop block that performs limb step `i + 1` (`KernelChain`).

The memory/carry it produces is exactly WP-S1's `SquareModel.sqPro mem n i tb`.

The block is split at the `SGT` (the shared stepper has no `SGT` case): block A
(idx 3604..3609, pc 4710, 6 instructions), `SgtStep.gasSteps_sqRowSgt_framed`
(idx 3610, pc 4716), block B (idx 3611..3653, pc 4717, 43 instructions; its
`runInstructions` proof is split into five sub-programs).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

/-! ## Programs -/

/-- `JUMPDEST DUP1 MLOAD DUP1 SWAP15 PUSH0` (idx 3604..3609). -/
def programA : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩), .push 0 0]

/-- `DUP2 ADD DUP2 DUP2 ADD SWAP2 DUP9 DUP3 DUP3 MULMOD` (idx 3611..3620). -/
def programB1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MULMOD]

/-- `SWAP2 DUP2 DUP2 LT SWAP2 MUL SWAP2 SUB DUP2 DUP2 LT DUP3 SWAP2 SUB SUB` (idx 3621..3635). -/
def programB2 : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

/-- `SWAP1 DUP4 PUSH2 0x1840 ADD` (idx 3636..3639). -/
def programB3a : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .push 2 1600, .op .ADD]

/-- `DUP1 MLOAD DUP3 ADD DUP1 SWAP2 MSTORE LT ADD` (idx 3640..3648). -/
def programB3b : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .MSTORE, .op .LT, .op .ADD]

/-- `PUSH1 0x26 DUP7 ADD SWAP6 JUMP` (idx 3649..3653). -/
def programB4 : List Instr :=
  [.push 1 38, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .JUMP]

/-- Everything after the `SGT` (idx 3611..3653). -/
def programB : List Instr :=
  (((programB1 ++ programB2) ++ programB3a) ++ programB3b) ++ programB4

/-! ## Location certificates -/

def blockA : Block Artifact.submissionArtifact .Osaka 4788 programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3638 6 4788 programA
    (by decide) (by rfl) (by rfl) (by decide)

def blockB : Block Artifact.submissionArtifact .Osaka 4795 programB :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3645 43 4795 programB
    (by decide) (by rfl) (by rfl) (by decide)

/-- `sq_row` itself is a jump destination (the frame's row head for square calls). -/
theorem jumpDest4710 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4788 = true :=
  Artifact.isValidJumpDest_index 3638 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
      rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `Block.steps` with the symbolic run first, so that the block's start state is read off
the run (used on record-update states). -/
def stepsOf {pc : Nat} {instructions : List Instr}
    (block : Block Artifact.submissionArtifact .Osaka pc instructions) {s t : State}
    (hrun' : runInstructions instructions s = some t) (hpc : s.pc = UInt256.ofNat pc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  block.steps (environment s hcode hfork hrun hnp) hpc hrun'

/-! ## Symbolic runs (generic stacks) -/

theorem run_A (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions programA
      { s with pc := UInt256.ofNat 4788,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 4794,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions programB1
      { s with pc := UInt256.ofNat 4795,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 4805,
                  stack := UInt256.mulMod x (x + tb) M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B2 (s : State) (mmr x f b2 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016) :
    runInstructions programB2
      { s with pc := UInt256.ofNat 4805, stack := mmr :: x :: f :: b2 :: rest } =
    some { s with pc := UInt256.ofNat 4820,
                  stack := (((mmr - UInt256.lt f x) - UInt256.lt (mmr - UInt256.lt f x) (x * f)) - x * f) ::
                    (x * f) :: b2 :: rest } := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [programB2, runInstructions, Challenge.EvmProof.Stepper.runInstr, h3, h4, h5, h6,
    List.exchange]
  decide

theorem run_B3a (s : State) (hi lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016) :
    runInstructions programB3a
      { s with pc := UInt256.ofNat 4820, stack := hi :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4826,
                  stack := ((1600 : UInt256) + P) :: lo :: hi :: b2 :: P :: rest } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [programB3a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h4, h5, h6,
    List.exchange]
  decide

theorem run_B3b (s : State) (tA lo hi b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions programB3b
      { s with pc := UInt256.ofNat 4826, stack := tA :: lo :: hi :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4835,
                  stack := (UInt256.lt (lo + MachineState.readWord s.memory tA.toNat) lo + hi) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  simp [programB3b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h4, h5, h6, h7,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_B4 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB4
      { s with pc := UInt256.ofNat 4835, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := ent,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 38) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [programB4, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange, hjump]
  rfl

/-- The word after the prologue: `lo = x * (x + tb)`. -/
abbrev loOf (x tb : UInt256) : UInt256 := x * (x + tb)

/-- The high word as the machine computes it (with the modulus word `M`). -/
abbrev hiOf (x tb M : UInt256) : UInt256 :=
  ((UInt256.mulMod x (x + tb) M - UInt256.lt (x + tb) x) -
    UInt256.lt (UInt256.mulMod x (x + tb) M - UInt256.lt (x + tb) x) (x * (x + tb))) - x * (x + tb)

/-- Block B on a generic stack: from the `SGT` result `tb` to the jump to `ent`. -/
theorem run_B (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      ((1600 : UInt256) + P).toNat 32) = s.activeWords)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB
      { s with pc := UInt256.ofNat 4795,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := ent,
                  stack := (UInt256.lt (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat)
                      (loOf x tb) + hiOf x tb M) ::
                    ((x + tb) + x) :: P :: hd :: w3 :: (ent + UInt256.ofNat 38) :: w5 :: M :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat).toNat 32)
                    ((1600 : UInt256) + P).toNat } := by
  have h1 := run_B1 s tb x P hd w3 ent w5 M rest (by omega)
  have h2 := run_B2 s (UInt256.mulMod x (x + tb) M) x (x + tb) ((x + tb) + x)
    (P :: hd :: w3 :: ent :: w5 :: M :: rest) (by simp only [List.length_cons]; omega)
  have h3 := run_B3a s (hiOf x tb M) (loOf x tb) ((x + tb) + x) P
    (hd :: w3 :: ent :: w5 :: M :: rest) (by simp only [List.length_cons]; omega)
  have h4 := run_B3b s ((1600 : UInt256) + P) (loOf x tb) (hiOf x tb M) ((x + tb) + x) P
    (hd :: w3 :: ent :: w5 :: M :: rest) (by simp only [List.length_cons]; omega) hact
  have h5 := run_B4
    { s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded
        (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat).toNat 32)
      ((1600 : UInt256) + P).toNat) }
    (UInt256.lt (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat)
      (loOf x tb) + hiOf x tb M) ((x + tb) + x) P hd w3 ent (w5 :: M :: rest)
    (by simp only [List.length_cons]; omega) hjump
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _
        (runInstructions_append_some _ _ _ _ _ h1 h2) h3) h4) h5

/-! ## The prologue on the kernel row frame -/

/-- The row pointer of square row `i` is the address of `a_i`. -/
theorem ptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    (UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)).toNat = aAddr n i := by
  rw [ptrAt_toNat _ _ (by omega) (by omega), aAddr]
  omega

/-- ... and `P + 0x1840` is the address of `t_i`. -/
theorem tptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    ((1600 : UInt256) + UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)).toNat = tAddr n i := by
  rw [Challenge.EvmProof.Word.word_toNat_add, ptr_toNat n i hi hn, aAddr, tAddr]
  have h6208 : (1600 : UInt256).toNat = 1600 := rfl
  rw [h6208, Nat.mod_eq_of_lt (by omega)]
  omega

theorem push0_eq : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-- **The `sq_row` prologue of square row `i`** (`i < n ≤ 8`, operand at 512): from the
row head (`hd = 4710`, frame slot `ent = e`, slot 14 = `aprev`) to the first-loop entry
`e` with memory/carry `SquareModel.sqPro mem n i tb` (`tb = SGT 0 aprev`), multiplier
`b2 = sqB2 x tb`, frame slot `ent := e + 38` and slot 14 := `x = a_i`. -/
def gasSteps_prologue (s : State) (mem : ByteArray) (n i e : Nat)
    (pdst ret w10 w11 w12 w13 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 93 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode e = true)
    (he : e + 38 < 2 ^ 256) :
    Challenge.EvmProof.GasSteps
      (outState s mem 512 n i (UInt256.ofNat 4788) (UInt256.ofNat e) pdst ret
        (w10 :: w11 :: w12 :: w13 :: aprev :: rest))
      (l1Q e s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev))
        (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 512 n i
        (UInt256.ofNat 4788) (UInt256.ofNat (e + 38)) pdst ret
        (w10 :: w11 :: w12 :: w13 :: sqX mem n i :: rest)) := by
  let P : UInt256 := UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)
  let s' : State := { s with memory := mem }
  have hP : P.toNat = aAddr n i := ptr_toNat n i hi (by omega)
  have hT : ((1600 : UInt256) + P).toNat = tAddr n i := tptr_toNat n i hi (by omega)
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat P.toNat 32) =
      s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat
      ((1600 : UInt256) + P).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  have hjumpE : Decode.isValidJumpDest s'.executionEnv.code (UInt256.ofNat e).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change Decode.isValidJumpDest s.executionEnv.code e = true
    rw [hcode]; exact hjump
  -- block A
  have hA := run_A s' P (UInt256.ofNat 4788) (UInt256.ofNat (512 - 32)) (UInt256.ofNat e)
    negative32 allOnes (l2Target n) pdst ret w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [push0_eq] at hA
  have gA := stepsOf blockA hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := SgtStep.gasSteps_sqRowSgt
    { s' with pc := UInt256.ofNat 4794,
              stack := UInt256.ofNat 0 :: aprev :: MachineState.readWord s'.memory P.toNat :: P ::
                UInt256.ofNat 4788 :: UInt256.ofNat (512 - 32) :: UInt256.ofNat e :: negative32 ::
                allOnes :: l2Target n :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
                MachineState.readWord s'.memory P.toNat :: rest }
    (UInt256.ofNat 0) aprev _ hcode hfork rfl rfl (by simp only [List.length_cons]; omega) hrun hnp
  -- block B
  have hB := run_B s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory P.toNat) P
    (UInt256.ofNat 4788) (UInt256.ofNat (512 - 32)) (UInt256.ofNat e) negative32 allOnes
    (l2Target n :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
      MachineState.readWord s'.memory P.toNat :: rest)
    (by simp only [List.length_cons]; omega) hactT hjumpE
  have gB := stepsOf blockB hB rfl hcode hfork hrun hnp
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, outState,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.SquareRow
