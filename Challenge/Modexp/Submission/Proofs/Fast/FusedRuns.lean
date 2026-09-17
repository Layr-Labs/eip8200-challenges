import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Fused-pc variants of hardcoded run lemmas. Generated. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedRuns

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel
open CiosCachedMacCore CarryRowModel

theorem run_AF0 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 5830,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 5836,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F0 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 5837,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 5845,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF0 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 5845, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 5863,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF0 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 5863, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 5874,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF1 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 6400,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 6406,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F1 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 6407,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 6415,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF1 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 6415, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 6433,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF1 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 6433, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 6444,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF2 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 6933,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 6939,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F2 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 6940,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 6948,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF2 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 6948, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 6966,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF2 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 6966, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 6977,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF3 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 7429,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 7435,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F3 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 7436,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 7444,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF3 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 7444, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 7462,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF3 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 7462, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 7473,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF4 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 7888,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 7894,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F4 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 7895,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 7903,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF4 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 7903, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 7921,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF4 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 7921, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 7932,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF5 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 8310,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 8316,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F5 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 8317,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 8325,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF5 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 8325, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 8343,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF5 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 8343, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 8354,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_AF6 (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programA
      { s with pc := UInt256.ofNat 8695,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 8701,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [SquareRow.programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1F6 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions SquareRow.programB1
      { s with pc := UInt256.ofNat 8702,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 8710,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [SquareRow.programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B23aF6 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions SquareRow.programB23a
      { s with pc := UInt256.ofNat 8710, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 8728,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [SquareRow.programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23bF6 (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions SquareRow.programB23b
      { s with pc := UInt256.ofNat 8728, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 8739,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [SquareRow.programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

theorem run_tailStoreF0 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 5809)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 5826)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF1 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 6379)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6396)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF2 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 6912)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6929)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF3 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 7408)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7425)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF4 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 7867)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7884)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF5 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 8289)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8306)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

theorem run_tailStoreF6 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 8674)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8691)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

end Challenge.Modexp.Submission.Proofs.Fast.FusedRuns
