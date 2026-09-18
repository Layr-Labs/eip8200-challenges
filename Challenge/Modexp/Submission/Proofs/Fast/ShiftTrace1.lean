import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheTrace
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

@[simp] private theorem followupPC2635 : Artifact.submissionArtifact.instructionPC 2109 = 2600 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2641 : Artifact.submissionArtifact.instructionPC 2115 = 2607 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2647 : Artifact.submissionArtifact.instructionPC 2121 = 2614 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2653 : Artifact.submissionArtifact.instructionPC 2127 = 2621 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2659 : Artifact.submissionArtifact.instructionPC 2133 = 2628 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem followupPC2665 : Artifact.submissionArtifact.instructionPC 2139 = 2635 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The `DUP2` that ends `blk2982`; the E5 cache block starts at the next index (1872, pc 2531). -/
@[simp] private theorem followupPC1871 : Artifact.submissionArtifact.instructionPC 2149 = 2648 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

attribute [local simp] notThirtyOneOfNat

/-- `blk2862`: the guard, byte-identical to the full-base guard. -/
theorem run_dispatch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn32 : n ≤ 8) (hb : bsize < 2 ^ 256) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2862
      (dispState s mem n bsize esize msize) =
      some (if FullBase.Matches mem n bsize
        then hitState s mem n bsize esize msize
        else missState s mem n bsize esize msize) := by
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have haw : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords :=
    Monpro.activeWords_fix s 0 32 (by decide) (by omega) hact
  have hgw := FullBase.guardWord_eq mem n bsize hn32 hb
  by_cases hm : FullBase.Matches mem n bsize
  · rw [if_pos hm] at hgw
    have hc : ¬ UInt256.isTrue (FullBase.guardWord mem n bsize) := by
      rw [hgw]; decide
    change ¬(((UInt256.shiftRight (MachineState.readWord mem 0) (UInt256.ofNat 255)).land
      ((UInt256.ofNat bsize).eq (UInt256.ofNat (32 * n)))).isZero.isTrue) at hc
    simp (config := { maxSteps := 300000 })
      [blk2862, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        dispState, hitState, frameState, pcDispatch, pcHit, outer, Exp.outer,
        hcode, hrun, hzeroNat, haw, jumpDest1826, hm, FullBase.guardWord, hc,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]
  · rw [if_neg hm] at hgw
    have hc : UInt256.isTrue (FullBase.guardWord mem n bsize) := by
      rw [hgw]; decide
    change (((UInt256.shiftRight (MachineState.readWord mem 0) (UInt256.ofNat 255)).land
      ((UInt256.ofNat bsize).eq (UInt256.ofNat (32 * n)))).isZero.isTrue) at hc
    simp (config := { maxSteps := 300000 })
      [blk2862, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        dispState, missState, frameState, pcDispatch, pcMiss, outer, Exp.outer,
        hcode, hrun, hzeroNat, haw, jumpDest1826, hm, FullBase.guardWord, hc,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]

/-- **S1.** `blk1351`: the diverted recogniser miss.  The dispatcher's `PUSH2`
operand names the six-word bail trampoline, so this class leaves the fast path
here instead of seeding `R1` and running the conversion.  `JUMPDEST; PUSH1 0xee;
JUMP` reads no memory, takes no branch, and consumes nothing beyond the target it
pushes itself, so the outer frame crosses unchanged and only `pc` moves.

The block this replaces (`blk2889`, the `R1` seeding block) is still located where
it always was; what changed is that nothing reaches it.  Its lemma was not merely
stale, it was FALSE -- `missState` is at pc 800 and `blk2889` is not. -/
theorem pcTramp578 : Artifact.submissionArtifact.instructionPC 565 = 800 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp579 : Artifact.submissionArtifact.instructionPC 566 = 801 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp580 : Artifact.submissionArtifact.instructionPC 567 = 803 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem run_bailMiss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1351
      (missState s mem n bsize esize msize) =
      some (bigCState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 400000 })
    [blk1351, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      missState, bigCState, frameState, pcMiss, pcBigC, outer, Exp.outer,
      hcode, hrun, Setup.jumpDestBig, pcTramp578, pcTramp579, pcTramp580,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2874`: copy the raw base to `TS`, clear `TN`, call the retained `CSUB` entry with the return address only. -/
theorem run_hit (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hact : 89 ≤ s.activeWords.toNat)
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

/-- `blk2892`: back from `CSUB`, push the carry `1` and the limb-0 pointer. -/
theorem run_negEntry (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hact : 88 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2892
      (afterCsub0State s mem n bsize esize msize) =
      some (negLoopState s mem n bsize esize msize 0) := by
  have haw : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 2752 32) = s.activeWords :=
    Monpro.activeWords_fix s 2752 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 200000 })
    [blk2892, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      afterCsub0State, negLoopState, frameState, pcAfterCsub0, pcNegLoop, negStep,
      outer, Exp.outer, hcode, hrun, hml, haw,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2896a`: store limb `j` of `NEG := -m`, up to the exit test.  The loop
pointer `p` stays abstract; only its value is needed. -/
theorem run_negBodyA (s : State) (mem : ByteArray) (p : UInt256) (n bsize esize msize j : Nat)
    (hn32 : n ≤ 8) (hj : j < n) (hpv : p.toNat = 32 * (n - 1 - j))
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896a
      { s with pc := UInt256.ofNat pcNegLoop
               stack := p :: (negStep mem n j).flag :: outer n bsize esize msize
               memory := (negStep mem n j).memory } =
      some { s with pc := UInt256.ofNat pcNegMid
                    stack := p :: (negStep mem n (j + 1)).flag :: outer n bsize esize msize
                    memory := (negStep mem n (j + 1)).memory } := by
  have hdst : (1280 + 32 * (n - 1 - j)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      1280 + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have hawL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hawS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (1280 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [UInt256.gt, UInt256.lt, blk2896a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcNegLoop, pcNegMid, negStep, NEG,
      outer, Exp.outer, hcode, hrun, hpv, hdst, hawL, hawS,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk2896b` with a nonzero pointer: step the pointer and jump back to the loop head. -/
theorem run_negTail (s : State) (m : ByteArray) (p c : UInt256) (n bsize esize msize : Nat)
    (hp0 : p.toNat ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896b
      { s with pc := UInt256.ofNat pcNegMid
               stack := p :: c :: outer n bsize esize msize
               memory := m } =
      some { s with pc := UInt256.ofNat pcNegLoop
                    stack := (UInt256.lnot (31 : UInt256) + p) :: c :: outer n bsize esize msize
                    memory := m } := by
  simp (config := { maxSteps := 200000 })
    [blk2896b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcNegMid, pcNegLoop, outer, Exp.outer, hcode, hrun, hp0, jumpDest4664,
      UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk2896b` on the zero pointer: fall through into `NEG_DONE`. -/
theorem run_negExit (s : State) (m : ByteArray) (p c : UInt256) (n bsize esize msize : Nat)
    (hp0 : p.toNat = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896b
      { s with pc := UInt256.ofNat pcNegMid
               stack := p :: c :: outer n bsize esize msize
               memory := m } =
      some { s with pc := UInt256.ofNat pcNegDone
                    stack := (UInt256.lnot (31 : UInt256) + p) :: c :: outer n bsize esize msize
                    memory := m } := by
  simp (config := { maxSteps := 200000 })
    [blk2896b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcNegMid, pcNegDone, outer, Exp.outer, hcode, hrun, hp0,
      UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk2919`: drop the loop words, store `L`, `dodd`, `X`, `Bmod`. -/
theorem run_negDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2919
      (negDoneState s mem n bsize esize msize) =
      some (preNewtonState s (negStep mem n n).memory n bsize esize msize) := by
  have haw0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1536 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1568 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw3 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1600 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw4 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1632 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk2919, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      negDoneState, preNewtonState, pcNegDone, pcPreNewton,
      preL, preDodd, preX, preBmod, PRE_L, PRE_DODD, PRE_X, PRE_BMOD, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, haw0, haw1, haw2, haw3, haw4, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]

/-- `blk2956`: the first four Newton steps. -/
theorem run_preNewton (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2956
      (preNewtonState s mem n bsize esize msize) =
      some (newtonBState s mem n bsize esize msize) := by
  have hmulone (x : UInt256) : x * UInt256.ofNat 1 = x := by
    change UInt256.mk (x.val * (1 : Fin UInt256.size)) = x
    simp
  simp (config := { maxSteps := 600000 })
    [blk2956, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      preNewtonState, newtonBState, pcPreNewton, pcNewtonB, newton4W, newtonW,
      hmulone,
      outer, Exp.outer, hcode, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2982`: the last four Newton steps, the `dinv` store, and `k := n`. -/
theorem run_newtonB (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2982
      (newtonBState s mem n bsize esize msize) =
      some (cacheSetupState s (preMem mem) n bsize esize msize) := by
  have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1664 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk2982, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      newtonBState, preNewtonState, cacheSetupState, kState, pcNewtonB,
      preMem, preMemOf, preDinv, newton8W, newtonW, PRE_DINV, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, haw,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
