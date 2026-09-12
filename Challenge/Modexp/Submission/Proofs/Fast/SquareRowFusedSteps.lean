import Challenge.Modexp.Submission.Proofs.Fast.SquareRowPrelude

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

/-- The arithmetic prefix through the first borrow subtraction. -/
def programB23a : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB]

/-- The second borrow and address setup. -/
def programB23b : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨3, by decide⟩), .push 4 1600, .op .ADD, .op (.Dup ⟨0, by decide⟩)]

/-- The memory update and final carry fold. -/
def programB23c : List Instr :=
  [.op .MLOAD, .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

theorem programB23_split : programB23 = (programB23a ++ programB23b) ++ programB23c := by
  rfl

theorem run_B23a (s : State) (mmr x f b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016) :
    runInstructions programB23a
      { s with pc := UInt256.ofNat 4727,
               stack := mmr :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4735,
                  stack := (mmr - UInt256.lt f x) :: (x * f) :: b2 :: P :: rest } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  simp [programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h4, h5, h6, h7, List.exchange]
  decide

theorem run_B23b (s : State) (carry lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1017) :
    runInstructions programB23b
      { s with pc := UInt256.ofNat 4735,
               stack := carry :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4747,
                  stack := ((1600 : UInt256) + P) :: ((1600 : UInt256) + P) ::
                    (UInt256.gt lo carry - carry) :: lo :: b2 :: P :: rest } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h4, h5, h6, List.exchange]
  decide

theorem run_B23c (s : State) (tA k lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions programB23c
      { s with pc := UInt256.ofNat 4747,
               stack := tA :: tA :: k :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4757,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - k) - lo) ::
                    b2 :: P :: rest,
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (lo + MachineState.readWord s.memory tA.toNat).toNat 32) tA.toNat } := by
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  simp [programB23c, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h5, h6, h7, List.exchange, State.activeWordsAfterUInt256, hact]
  constructor
  · omega
  · decide

theorem run_B23 (s : State) (mmr x f b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      ((1600 : UInt256) + P).toNat 32) = s.activeWords) :
    runInstructions programB23
      { s with pc := UInt256.ofNat 4727,
               stack := mmr :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4757,
                  stack := (UInt256.lt (x * f + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat)
                    (x * f) + (((mmr - UInt256.lt f x) -
                      UInt256.lt (mmr - UInt256.lt f x) (x * f)) - x * f)) :: b2 :: P :: rest,
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (x * f + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat).toNat 32)
                    ((1600 : UInt256) + P).toNat } := by
  have ha := run_B23a s mmr x f b2 P rest (by omega)
  have hb := run_B23b s (mmr - UInt256.lt f x) (x * f) b2 P rest (by omega)
  have hc := run_B23c s ((1600 : UInt256) + P)
    (UInt256.gt (x * f) (mmr - UInt256.lt f x) - (mmr - UInt256.lt f x))
    (x * f) b2 P rest (by omega) hact
  rw [programB23_split]
  have hrun := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ ha hb) hc
  simpa only [UInt256.gt, UInt256.lt, fused_carry_eq] using hrun

theorem run_B4 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB4
      { s with pc := UInt256.ofNat 4757, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
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


end Challenge.Modexp.Submission.Proofs.Fast.SquareRow
