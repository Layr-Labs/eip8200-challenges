import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseGuardCore
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTEntry

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Block reductions of the shift-reduce base conversion, part 1

The dispatcher, the raw-base copy, the negation loop and the estimator
precomputation.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

@[simp] private theorem followupPC2659 : Artifact.submissionArtifact.instructionPC 2027 = 2596 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2665 : Artifact.submissionArtifact.instructionPC 2033 = 2604 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- A pc inside `blkNbTail`. -/
@[simp] private theorem followupPC1871 : Artifact.submissionArtifact.instructionPC 2043 = 2616 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

attribute [local simp] notThirtyOneOfNat

/-- `blk2862`: the guard `bsize = 32 n`; the modulus top bit was already required by the
fast-path entry, so with it the test decides `FullBase.Matches`. -/
theorem run_dispatch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn32 : n ≤ 8) (hb : bsize < 2 ^ 256) (htop : R1.TopBitSet mem)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2862
      (dispState s mem n bsize esize msize) =
      some (if FullBase.Matches mem n bsize
        then hitState s mem n bsize esize msize
        else missState s mem n bsize esize msize) := by
  have hsize : 32 * n < 2 ^ 256 :=
    lt_of_le_of_lt (show 32 * n ≤ 256 by omega) (by decide)
  have hz1 : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by decide
  have hz0 : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
  by_cases hm : FullBase.Matches mem n bsize
  · have heq : UInt256.eq (UInt256.ofNat bsize) (UInt256.ofNat (32 * n)) = UInt256.ofNat 1 := by
      rw [UInt256.eq, Exp.toNat_ofNat_self hb, Exp.toNat_ofNat_self hsize, if_pos hm.1]
    simp (config := { maxSteps := 300000 })
      [blk2862, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        dispState, hitState, frameState, pcDispatch, pcHit, outer, Exp.outer,
        hcode, hrun, heq, hz1, Exp.not_isTrue_zero, hm, jumpDestBigC,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]
  · have hne : bsize ≠ 32 * n := fun h => hm ⟨h, htop⟩
    have heq : UInt256.eq (UInt256.ofNat bsize) (UInt256.ofNat (32 * n)) = UInt256.ofNat 0 := by
      rw [UInt256.eq, Exp.toNat_ofNat_self hb, Exp.toNat_ofNat_self hsize, if_neg hne]
    simp (config := { maxSteps := 300000 })
      [blk2862, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        dispState, missState, frameState, pcDispatch, pcMiss, outer, Exp.outer,
        hcode, hrun, heq, hz0, Exp.isTrue_one, hm, jumpDestBigC,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2874`: copy the raw base to `TS`, clear `TN`, call the retained `CSUB` entry with the return address only. -/
theorem run_hit (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2874
      (hitState s mem n bsize esize msize) =
      some (RetainedT.entryState s (hitMem mem input n)
        (UInt256.ofNat pcCsubReturn) (outer n bsize esize msize)) := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 256 by omega) (by decide)
  have haw2 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 2112 (32 * n)) = s.activeWords :=
    Monpro.activeWords_fix s 2112 (32 * n) (by omega) (by omega) (by omega)
  have haw3 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) = s.activeWords :=
    Monpro.activeWords_fix s 2080 32 (by decide) (by omega) (by omega)
  simp (config := { maxSteps := 400000 })
    [blk2874, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hitState, frameState, pcHit, pcCsubReturn, RetainedT.entryState, hitMem, ShiftProducerCanonical.hitMemory,
      FullBase.copyBaseMem, Exp.storeWord, outer, Exp.outer,
      hcode, hrun, hdata, hsize, haw2, haw3, RetainedT.jumpDest4486, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## The straight-line negation (negun)

`NEG := radix ^ n - m` is written cell by cell: limb 0 as `0 - m_0`, every later limb as
`NOT m_j` (`m` is odd, so `NOT m_0 + 1` never carries).  `negStep_one` and
`negStep_succ_not` restate the loop model `negStep` in exactly that form. -/

theorem lnot_add_one (x : UInt256) : UInt256.lnot x + UInt256.ofNat 1 = UInt256.ofNat 0 - x := by
  apply Challenge.EvmProof.Word.word_ext
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub]
  unfold UInt256.lnot
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.size]
  omega

theorem add_ofNat_zero (x : UInt256) : x + UInt256.ofNat 0 = x := by
  apply Challenge.EvmProof.Word.word_ext
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat]
  omega

/-- Limb `0` of the negation: `0 - m_0`. -/
theorem negStep_one (mem : ByteArray) (n : Nat) :
    (negStep mem n 1).memory = MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded
        (UInt256.ofNat 0 - MachineState.readWord mem (32 * (n - 1))).toNat 32)
      (NEG + 32 * (n - 1)) := by
  show MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded
        (UInt256.lnot (MachineState.readWord mem (32 * (n - 1 - 0))) + UInt256.ofNat 1).toNat 32)
      (NEG + 32 * (n - 1 - 0)) = _
  rw [lnot_add_one, Nat.sub_zero]

/-- Every later limb: `NOT m_j` (the flag is already `0`). -/
theorem negStep_succ_not (mem : ByteArray) (n j : Nat) (hj : 1 ≤ j) :
    (negStep mem n (j + 1)).memory = MachineState.writeBytes (negStep mem n j).memory
      (Data.Bytes.natToBytesPadded
        (UInt256.lnot (MachineState.readWord (negStep mem n j).memory (32 * (n - 1 - j)))).toNat 32)
      (NEG + 32 * (n - 1 - j)) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  show MachineState.writeBytes (negStep mem n (k + 1)).memory
      (Data.Bytes.natToBytesPadded
        (UInt256.lnot (MachineState.readWord (negStep mem n (k + 1)).memory (32 * (n - 1 - (k + 1))))
          + UInt256.ofNat 0).toNat 32)
      (NEG + 32 * (n - 1 - (k + 1))) = _
  rw [add_ofNat_zero]

/-- `blkNegW`, eight limbs: `32 n ≠ 128` falls into the eight-limb cells. -/
theorem run_negW8 (s : State) (mem : ByteArray) (bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNegW
      (afterCsub0State s mem 8 bsize esize msize) =
      some (negState s mem pcNeg8 8 bsize esize msize 0) := by
  have heq : UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat 256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 200000 })
    [blkNegW, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      afterCsub0State, negState, negStep, frameState, pcAfterCsub0, pcNeg8,
      outer, Exp.outer, hcode, hrun, heq, Exp.not_isTrue_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blkNegW`, four limbs: `32 n = 128` jumps to the stub at pc 2336. -/
theorem run_negW4 (s : State) (mem : ByteArray) (bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNegW
      (afterCsub0State s mem 4 bsize esize msize) =
      some (negState s mem pcNeg4 4 bsize esize msize 0) := by
  have heq : UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 200000 })
    [blkNegW, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      afterCsub0State, negState, negStep, frameState, pcAfterCsub0, pcNeg4,
      outer, Exp.outer, hcode, hrun, heq, Exp.isTrue_one, jumpDestNeg4,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negS8`: limb `0` (`0 - m` at 224). -/
theorem run_negS8 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hA : 32 * (n - 1) = 224) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negS8
      (negState s mem 2429 n bsize esize msize 0) =
      some (negState s mem 2438 n bsize esize msize 1) := by
  have haw224 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 224 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1504 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1504 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_one mem n, hA]
  show Challenge.EvmProof.Stepper.runLocatedBlock negS8
      { s with pc := UInt256.ofNat 2429, stack := outer n bsize esize msize, memory := mem } = _
  simp (config := { maxSteps := 400000 })
    [negS8, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw224, haw1504, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negN8a`: a later limb (`NOT m` at 192). -/
theorem run_negN8a (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 192) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negN8a
      (negState s mem 2438 n bsize esize msize j) =
      some (negState s mem 2446 n bsize esize msize (j + 1)) := by
  have haw192 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 192 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1472 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1472 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negN8a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw192, haw1472, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negN8b`: a later limb (`NOT m` at 160). -/
theorem run_negN8b (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 160) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negN8b
      (negState s mem 2446 n bsize esize msize j) =
      some (negState s mem 2454 n bsize esize msize (j + 1)) := by
  have haw160 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 160 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1440 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negN8b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw160, haw1440, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negN8c`: a later limb (`NOT m` at 128). -/
theorem run_negN8c (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 128) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negN8c
      (negState s mem 2454 n bsize esize msize j) =
      some (negState s mem 2462 n bsize esize msize (j + 1)) := by
  have haw128 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 128 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1408 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1408 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negN8c, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw128, haw1408, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negN8d`: a later limb (`NOT m` at 96). -/
theorem run_negN8d (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 96) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negN8d
      (negState s mem 2462 n bsize esize msize j) =
      some (negState s mem 2470 n bsize esize msize (j + 1)) := by
  have haw96 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 96 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1376 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1376 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negN8d, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw96, haw1376, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negNTa`: a later limb (`NOT m` at 64). -/
theorem run_negNTa (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 64) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negNTa
      (negState s mem 2471 n bsize esize msize j) =
      some (negState s mem 2479 n bsize esize msize (j + 1)) := by
  have haw64 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 64 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1344 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1344 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negNTa, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw64, haw1344, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negNTb`: a later limb (`NOT m` at 32). -/
theorem run_negNTb (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 32) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negNTb
      (negState s mem 2479 n bsize esize msize j) =
      some (negState s mem 2487 n bsize esize msize (j + 1)) := by
  have haw32 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1312 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1312 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negNTb, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw32, haw1312, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negNTc`: a later limb (`NOT m` at 0). -/
theorem run_negNTc (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA : 32 * (n - 1 - j) = 0) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negNTc
      (negState s mem 2487 n bsize esize msize j) =
      some (negState s mem 2494 n bsize esize msize (j + 1)) := by
  have haw0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1280 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1280 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_succ_not mem n j hj, hA]
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 400000 })
    [negNTc, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw0, haw1280, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negS4`: limb `0` (`0 - m` at 96). -/
theorem run_negS4 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hA : 32 * (n - 1) = 96) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negS4
      (negState s mem 2337 n bsize esize msize 0) =
      some (negState s mem 2346 n bsize esize msize 1) := by
  have haw96 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 96 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1376 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1376 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  unfold negState
  rw [negStep_one mem n, hA]
  show Challenge.EvmProof.Stepper.runLocatedBlock negS4
      { s with pc := UInt256.ofNat 2337, stack := outer n bsize esize msize, memory := mem } = _
  simp (config := { maxSteps := 400000 })
    [negS4, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      NEG, outer, Exp.outer, hcode, hrun, haw96, haw1376, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negJ4`: stub `JUMPDEST`. -/
theorem run_negJ4 (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negJ4
      (negState s mem 2336 n bsize esize msize j) =
      some (negState s mem 2337 n bsize esize msize j) := by
  unfold negState
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 200000 })
    [negJ4, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      outer, Exp.outer, hcode, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negJT`: `NEG_TAIL` `JUMPDEST`. -/
theorem run_negJT (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negJT
      (negState s mem 2470 n bsize esize msize j) =
      some (negState s mem 2471 n bsize esize msize j) := by
  unfold negState
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 200000 })
    [negJT, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      outer, Exp.outer, hcode, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `negJ4b`: the stub's jump to `NEG_TAIL`. -/
theorem run_negJ4b (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock negJ4b
      (negState s mem 2346 n bsize esize msize j) =
      some (negState s mem 2470 n bsize esize msize j) := by
  unfold negState
  generalize (negStep mem n j).memory = M
  simp (config := { maxSteps := 200000 })
    [negJ4b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      outer, Exp.outer, hcode, hrun, jumpDestNegT,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- The eight-limb cells: limbs `0..4` of `NEG`. -/
theorem run_neg8 (s : State) (mem : ByteArray) (bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNeg8
      (negState s mem pcNeg8 8 bsize esize msize 0) =
      some (negState s mem pcNegT 8 bsize esize msize 5) := by
  unfold blkNeg8
  simp only [List.append_assoc]
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negS8 s mem 8 bsize esize msize (by decide) hact hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negN8a s mem 8 bsize esize msize 1 (by decide) (by decide) hact hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negN8b s mem 8 bsize esize msize 2 (by decide) (by decide) hact hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negN8c s mem 8 bsize esize msize 3 (by decide) (by decide) hact hcode hrun) hrun ?_
  exact run_negN8d s mem 8 bsize esize msize 4 (by decide) (by decide) hact hcode hrun

/-- The four-limb stub: limb `0` of `NEG`, then `NEG_TAIL`. -/
theorem run_neg4 (s : State) (mem : ByteArray) (bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNeg4
      (negState s mem pcNeg4 4 bsize esize msize 0) =
      some (negState s mem pcNegT 4 bsize esize msize 1) := by
  unfold blkNeg4
  simp only [List.append_assoc]
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negJ4 s mem 4 bsize esize msize 0 hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negS4 s mem 4 bsize esize msize (by decide) hact hcode hrun) hrun ?_
  exact run_negJ4b s mem 4 bsize esize msize 1 hcode hrun

/-- `NEG_TAIL`: the last three limbs (`j`, `j + 1`, `j + 2` at 64, 32, 0). -/
theorem run_negT (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hj : 1 ≤ j) (hA0 : 32 * (n - 1 - j) = 64) (hA1 : 32 * (n - 1 - (j + 1)) = 32)
    (hA2 : 32 * (n - 1 - (j + 1 + 1)) = 0) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNegT
      (negState s mem pcNegT n bsize esize msize j) =
      some (negState s mem pcNegDone n bsize esize msize (j + 1 + 1 + 1)) := by
  unfold blkNegT
  simp only [List.append_assoc]
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negJT s mem n bsize esize msize j hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negNTa s mem n bsize esize msize j hj hA0 hact hcode hrun) hrun ?_
  refine Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_negNTb s mem n bsize esize msize (j + 1) (by omega) hA1 hact hcode hrun) hrun ?_
  exact run_negNTc s mem n bsize esize msize (j + 1 + 1) (by omega) hA2 hact hcode hrun

/-- `blk2919a`: leave `[L, L, d]` at the `CLZ`. -/
theorem run_negDoneA (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2919a
      (negDoneState s mem n bsize esize msize) =
      some (preClzState s (negStep mem n n).memory n bsize esize msize) := by
  have haw0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk2919a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      negDoneState, negState, preClzState, pcNegDone,
      preL,
      outer, Exp.outer, hcode, hrun, haw0, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk2919b` (after the `CLZ`): store `PRE_X := 0 - ~clz L`, `PRE_L := 255 - clz L`,
`dodd`, `Bmod`. -/
theorem run_negDoneB (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2919b
      (postClzState s mem n bsize esize msize) =
      some (preNewtonState s mem n bsize esize msize) := by
  have haw1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1536 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1568 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw3 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw4 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1632 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk2919b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      postClzState, preNewtonState, pcPreNewton,
      preDodd, preK, preS, preBmod, PRE_L, PRE_DODD, PRE_X, PRE_BMOD, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, haw1, haw2, haw3, haw4, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blkNbHead`: load `n0 = mem[mem[V_ML]]` and form `dodd * n0` for the inline Newton chain. -/
theorem run_nbHead (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord M 2752 = UInt256.ofNat (32 * n - 32))
    (hn0 : MachineState.readWord M (32 * n - 32) = n0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNbHead
      (nbHeadState s M d n bsize esize msize) =
      some (nbSubState s M d n0 n bsize esize msize) := by
  have haw2752 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2752 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hawn0 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat (32 * n - 32) 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmodn : (32 * n - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n - 32 := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 600000 })
    [blkNbHead, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      nbHeadState, nbSubState, pcPreNewton, outer, Exp.outer, hcode, hrun,
      hml, hn0, hmodn, haw2752, hawn0,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blkNbSub`: the inline chain (seed and six Newton steps) leaves `newton8W p`. -/
theorem run_nbSub (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNbSub
      (nbSubState s M d n0 n bsize esize msize) =
      some (nbTailState s M d n0 n bsize esize msize) := by
  have hmulone (x : UInt256) : x * UInt256.ofNat 1 = x := by
    change UInt256.mk (x.val * (1 : Fin UInt256.size)) = x
    simp
  simp (config := { maxSteps := 1500000 })
    [blkNbSub, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      nbSubState, nbTailState, newton8W, newton4W, newtonW, hmulone,
      outer, Exp.outer, hcode, hrun, List.exchange,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blkNbTail`: store `dinv` and `V_MINV`, drop four words, and park the riding slots. -/
theorem run_nbTail (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkNbTail
      (nbTailState s M d n0 n bsize esize msize) =
      some (cacheSetupState s (nbOutMem M d n0) n bsize esize msize) := by
  have haw1312 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1312 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1344 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1344 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1376 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1376 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1408 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1408 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1440 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1472 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1472 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1504 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1504 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1536 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1536 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1568 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1568 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1600 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1632 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1632 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1664 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1664 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2720 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2720 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 2500000 })
    [blkNbTail, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      nbTailState, cacheSetupState, slotState, rideSlots, nbOutMem, Exp.storeWord, PRE_DINV,
      outer, Exp.outer, hcode, hrun, haw1312, haw1344, haw1376, haw1408, haw1440, haw1472, haw1504, haw1536, haw1568, haw1600, haw1632, haw1664, haw2720, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals (first | rfl | simp [UInt256.ofNat, Fin.ofNat] | decide)

end Challenge.Modexp.Submission.Proofs.Fast.Shift
