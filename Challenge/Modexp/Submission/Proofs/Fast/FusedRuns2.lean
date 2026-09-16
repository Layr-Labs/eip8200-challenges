import Challenge.Modexp.Submission.Proofs.Fast.FusedRuns
import Challenge.Modexp.Submission.Proofs.Fast.FusedBlocks
import Challenge.Modexp.Submission.Proofs.Fast.FusedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRowExit
import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedControl
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Fused-region run lemmas, round 2: POP-tails, SGT, mid, l2, rejoin. Generated. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedRuns2

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel
open CiosCachedMacCore CarryRowModel CiosReadonly CiosCachedMidMemory StagedOperand

/-- Prologue tail with `POP` fall-through instead of the join jump. -/
def exitPOPProgram : List Instr :=
  (R8ZeroFirstRow.quotientA ++ R8ZeroFirstRow.quotientB) ++ FusedPrograms.quotientDupPOP

theorem run_quotientDupPOP (s : State)
    (pc c0 mu flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) :
    runInstructions FusedPrograms.quotientDupPOP
      { s with pc := pc, stack := c0 :: mu :: R8ZeroFirstRow.endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := advancePC 2 pc,
                  stack := c0 :: mu :: R8ZeroFirstRow.endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [FusedPrograms.quotientDupPOP, R8ZeroFirstRow.endFrame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h17, h18, advancePC]

theorem run_exitPOP (s : State)
    (pc flag P hd tt next stride M target inv m0 m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    let t0 := MachineState.readWord s.memory 2336
    let mu := t0*inv
    runInstructions exitPOPProgram
      { s with pc := pc, stack := R8ZeroFirstRow.endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } =
    some { s with pc := advancePC 2 (advancePC 12 pc),
                  stack := UInt256.addMod t0 (UInt256.mulMod m0 mu M) M :: mu ::
                    R8ZeroFirstRow.endFrame flag P hd tt next stride M target inv m0 m96 m64 m32 x rest } := by
  let t0 := MachineState.readWord s.memory 2336
  have h0 := R8ZeroFirstRow.run_quotientA s pc flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap hact
  have h1 := R8ZeroFirstRow.run_quotientB s (advancePC 4 pc) (t0*inv) flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap hact
  have h2 := run_quotientDupPOP s (advancePC 12 pc)
    (UInt256.addMod t0 (UInt256.mulMod m0 (t0*inv) M) M) (t0*inv)
    flag P hd tt next stride M target inv m0 m96 m64 m32 x rest hcap
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  exact runInstructions_append_some _ _ _ _ _ h01 h2

theorem run_prologuePOP (s : State)
    (pc hd ent next stride target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (FusedPrograms.prologuePOPProgram next) (R8ZeroFirstRow.initial s pc hd ent stride target inv m0 m96 m64 m32 aprev rest) =
      some ({R8ZeroFirstRow.result s hd next stride target inv m0 m96 m64 m32 rest with pc := advancePC 2 (advancePC 12 (advancePC 232 pc))}) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x+x
  let q6 := R8ZeroFirstRow.zeroRun (R8ZeroFirstRow.diagonal s.memory) bi 6
  let x7 := MachineState.readWord q6.memory (SquareModel.aAddr 8 7)
  have h0 := R8ZeroFirstRow.run_diagonal s pc hd ent next stride target inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := R8ZeroFirstRow.run_cells s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride
    (R8ZeroFirstRow.diagonal s.memory)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 6 (by decide)
  have h1b := R8ZeroFirstRow.run_cellAB { s with memory := q6.memory } (advancePC 198 pc) q6.carry bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord (SquareModel.aAddr 8 7)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) (by unfold SquareModel.aAddr; omega) hact
  have h2 := R8ZeroFirstRow.run_finishStore { s with memory := q6.memory } (advancePC 221 pc)
    (R4Math.zCarry x7 bi q6.carry maxWord) (R4Math.zSum x7 bi q6.carry) bi
    (UInt256.ofNat 2592 :: hd :: UInt256.ofNat 2336 :: next :: stride :: maxWord :: target ::
      inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hmem : MachineState.writeBytes
      (MachineState.writeBytes q6.memory
        (Data.Bytes.natToBytesPadded (R4Math.zCarry x7 bi q6.carry maxWord).toNat 32) 2080)
      (Data.Bytes.natToBytesPadded (R4Math.zSum x7 bi q6.carry).toNat 32) 2112 =
      R8ZeroFirstRow.firstMemory s.memory := by
    rw [R8ZeroFirstRow.writeBytes_comm_disjoint _ _ _ 2080 2112
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; decide)
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; decide)
      (Or.inl (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]))]
    rfl
  rw [hmem] at h2
  have h3 := run_exitPOP { s with memory := R8ZeroFirstRow.firstMemory s.memory } (advancePC 232 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next stride maxWord target
    inv m0 m96 m64 m32 x rest hcap hact
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h01b := runInstructions_append_some _ _ _ _ _ h01 h1b
  have h012 := runInstructions_append_some _ _ _ _ _ h01b h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

theorem run_B4POPF0 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 5874, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 5880,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF1 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 6444, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 6450,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF2 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 6977, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 6983,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF3 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 7473, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 7479,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF4 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 7932, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 7938,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF5 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 8354, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 8360,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_B4POPF6 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015) :
    runInstructions FusedPrograms.b4POPProgram
      { s with pc := UInt256.ofNat 8739, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := UInt256.ofNat 8745,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [FusedPrograms.b4POPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF0 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 5826)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 5830)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF1 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6396)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6400)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF2 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6929)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 6933)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF3 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7425)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7429)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF4 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7884)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 7888)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF5 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8306)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8310)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem run_headPOPF6 (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions FusedPrograms.headPOPProgram
      (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8691)
        ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 8695)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [FusedPrograms.headPOPProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h8, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

theorem decodedOp_fusedSgt0 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 5836) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 4546 := by
    rw [hpc, FusedBlocks.sgtPC0]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 4546 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex0 hwf

theorem succ_fusedSgt0 : (UInt256.ofNat 5836).succ = UInt256.ofNat 5837 := by
  decide

def gasSteps_fusedSgt0 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 5836)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 5837 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt0 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt0] at h
  exact h

def gasSteps_fusedSgt_framed0 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 5836, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 5837, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt0 { t with pc := UInt256.ofNat 5836, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt1 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 6406) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 5024 := by
    rw [hpc, FusedBlocks.sgtPC1]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 5024 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex1 hwf

theorem succ_fusedSgt1 : (UInt256.ofNat 6406).succ = UInt256.ofNat 6407 := by
  decide

def gasSteps_fusedSgt1 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 6406)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 6407 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt1 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt1] at h
  exact h

def gasSteps_fusedSgt_framed1 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 6406, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 6407, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt1 { t with pc := UInt256.ofNat 6406, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt2 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 6939) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 5471 := by
    rw [hpc, FusedBlocks.sgtPC2]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 5471 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex2 hwf

theorem succ_fusedSgt2 : (UInt256.ofNat 6939).succ = UInt256.ofNat 6940 := by
  decide

def gasSteps_fusedSgt2 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 6939)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 6940 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt2 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt2] at h
  exact h

def gasSteps_fusedSgt_framed2 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 6939, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 6940, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt2 { t with pc := UInt256.ofNat 6939, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt3 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 7435) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 5887 := by
    rw [hpc, FusedBlocks.sgtPC3]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 5887 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex3 hwf

theorem succ_fusedSgt3 : (UInt256.ofNat 7435).succ = UInt256.ofNat 7436 := by
  decide

def gasSteps_fusedSgt3 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 7435)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 7436 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt3 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt3] at h
  exact h

def gasSteps_fusedSgt_framed3 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 7435, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 7436, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt3 { t with pc := UInt256.ofNat 7435, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt4 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 7894) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 6272 := by
    rw [hpc, FusedBlocks.sgtPC4]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 6272 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex4 hwf

theorem succ_fusedSgt4 : (UInt256.ofNat 7894).succ = UInt256.ofNat 7895 := by
  decide

def gasSteps_fusedSgt4 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 7894)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 7895 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt4 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt4] at h
  exact h

def gasSteps_fusedSgt_framed4 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 7894, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 7895, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt4 { t with pc := UInt256.ofNat 7894, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt5 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 8316) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 6626 := by
    rw [hpc, FusedBlocks.sgtPC5]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 6626 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex5 hwf

theorem succ_fusedSgt5 : (UInt256.ofNat 8316).succ = UInt256.ofNat 8317 := by
  decide

def gasSteps_fusedSgt5 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 8316)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 8317 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt5 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt5] at h
  exact h

def gasSteps_fusedSgt_framed5 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 8316, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 8317, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt5 { t with pc := UInt256.ofNat 8316, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem decodedOp_fusedSgt6 (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 8701) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 6949 := by
    rw [hpc, FusedBlocks.sgtPC6]; decide
  have hwf : Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact s 6949 (.op .SGT)
    hcode hpcNat FusedBlocks.sgtIndex6 hwf

theorem succ_fusedSgt6 : (UInt256.ofNat 8701).succ = UInt256.ofNat 8702 := by
  decide

def gasSteps_fusedSgt6 (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 8701)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 8702 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt (decodedOp_fusedSgt6 s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_fusedSgt6] at h
  exact h

def gasSteps_fusedSgt_framed6 (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps { t with pc := UInt256.ofNat 8701, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 8702, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_fusedSgt6 { t with pc := UInt256.ofNat 8701, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

theorem run_middleStoreWideF0 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 6103)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 6119)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middleStoreWideF1 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 6636)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 6652)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middleStoreWideF2 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 7132)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 7148)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middleStoreWideF3 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 7591)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 7607)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middleStoreWideF4 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 8013)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 8029)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middleStoreWideF5 (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 8398)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 8414)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- Generic-pc `cachedProduct` run: the program is straight-line, so the same
stepping proof works at any entry pc (post pc is `pc + 12`). -/
theorem run_cachedProductWide_gen (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat) (pc : Nat) :
    let tl := UInt256.ofNat (2080+32*n)
    let t0 := MachineState.readWord s.memory (2080+32*n)
    runInstructions cachedProduct
      (framed s (UInt256.ofNat pc)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc + 12))
      ([UInt256.addMod t0 (UInt256.mulMod m0 (inv*t0) maxWord) maxWord,inv*t0] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hmod : (2080+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 2080+32*n := Nat.mod_eq_of_lt (by omega)
  have hmul : MachineState.readWord s.memory (2080+32*n) * inv = inv * MachineState.readWord s.memory (2080+32*n) := by
    apply Challenge.EvmProof.Word.word_ext
    change ((MachineState.readWord s.memory (2080+32*n)).val * inv.val).val =
      (inv.val * (MachineState.readWord s.memory (2080+32*n)).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hactQ := Csub.activeWords_fix s (2080+32*n) 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [cachedProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, cacheStack, CiosCachedMidDefs.baseStack,
    Nat.add_assoc, hc17, hc18, hc19, hc20, hc21, hc22, hmul, allOnes_value,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, hmod, hactQ, List.exchange]


theorem run_cachedProduct_modelWideF0 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 6119)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 6131)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 6119

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_cachedProduct_modelWideF1 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 6652)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 6664)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 6652

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_cachedProduct_modelWideF2 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 7148)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 7160)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 7148

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_cachedProduct_modelWideF3 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 7607)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 7619)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 7607

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_cachedProduct_modelWideF4 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 8029)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 8041)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 8029

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_cachedProduct_modelWideF5 (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 8414)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 8426)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProductWide_gen s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact 8414

  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]
    exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n)) hminv hguard
  dsimp only at hr
  rw [N0Carry.addMod_comm] at hr
  simpa only [hcarry, rowC0, rowMu] using hr

theorem run_middleWideF0 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 6102 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 6131 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 6102 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 6103)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF0 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF0 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_middleWideF1 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 6635 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 6664 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 6635 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 6636)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF1 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF1 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_middleWideF2 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 7131 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 7160 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 7131 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 7132)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF2 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF2 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_middleWideF3 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 7590 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 7619 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 7590 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 7591)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF3 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF3 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_middleWideF4 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 8012 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 8041 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 8012 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 8013)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF4 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF4 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_middleWideF5 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlockWide
      (CiosCached.midStateAt 8397 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 8426 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (CarryScratchAgreement.refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 8397 s mem c bi pb n i hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 8398)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := run_middleStoreWideF5 {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_modelWideF5 {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlockWide, CarryRowPrograms.middleWide, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h2

theorem run_l2Join8F0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 5561 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 5562 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 5709 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 5710 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 6131 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 6132 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 6279 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 6280 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 6664 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 6665 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 6812 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 6813 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 7160 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 7161 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 7308 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 7309 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 7619 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 7620 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 7767 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 7768 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 8041 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 8042 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 8189 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 8190 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2Join8F6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 8426 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 8427 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2JoinF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions joinProgram (l2At 8574 s mid bi mu c0 pb n i k hd ent pdst ret rest) =
      some (l2At 8575 s mid bi mu c0 pb n i k hd ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_l2LastF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 5776 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 5809, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 5776) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 5776 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 5809 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 6346 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 6379, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 6346) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 6346 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 6379 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 6879 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 6912, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 6879) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 6879 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 6912 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 7375 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 7408, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 7375) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 7375 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 7408 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 7834 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 7867, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 7834) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 7834 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 7867 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 8256 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 8289, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 8256) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 8256 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 8289 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

theorem run_l2LastF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At 8641 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) =
      some ({ s with pc := UInt256.ofNat 8674, stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest, memory := (l2Step mid mu c0 n (n-1)).memory }) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat 8641) mid bi mu c0 n (n-2) 0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  have hpc : UInt256.ofNat 8641 + UInt256.ofNat ((0 : Fin 33).val + 33) = UInt256.ofNat 8674 := by
    decide
  rw [hnn, hpc] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state, CiosCachedLast.lastState, l2At,
    tailState] using h

/-- Fused entry `JUMPDEST`: advance to the prologue. -/
theorem run_entry (s : State) (stk : List UInt256)
    (hcap : stk.length ≤ 1023) :
    runInstructions [.op .JUMPDEST]
      { s with pc := UInt256.ofNat 5314, stack := stk } =
    some { s with pc := UInt256.ofNat 5315, stack := stk } := by
  have h0 : stk.length < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, h0,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  try decide

/-- Row-7-cell `JUMPDEST` in the fused bytecode (original pc, new artifact). -/
theorem jumpDest3639 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3639 = true :=
  Artifact.isValidJumpDest_index 2727 (by rfl)

/-- Rejoin: push row-7-cell pc and jump back to the original code. -/
theorem run_rejoin (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3639 = true) :
    runInstructions FusedPrograms.rejoinProgram
      { s with pc := UInt256.ofNat 8745,
               stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } =
    some { s with pc := UInt256.ofNat 3639,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  simp [FusedPrograms.rejoinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7,
    List.exchange, hjump,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  try decide

end Challenge.Modexp.Submission.Proofs.Fast.FusedRuns2
