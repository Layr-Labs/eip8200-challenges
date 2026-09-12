import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseGuardCore

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

/-- The shift traces normalize PUSH1 literals to `ofNat` before NOT. -/
theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

attribute [local simp] notThirtyOneOfNat

/-- `blk2862`: the guard, byte-identical to the full-base guard. -/
theorem run_dispatch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn32 : n ≤ 32) (hb : bsize < 2 ^ 256) (hact : 296 ≤ s.activeWords.toNat)
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
        hcode, hrun, hzeroNat, haw, jumpDest4652, hm, FullBase.guardWord, hc,
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
        hcode, hrun, hzeroNat, haw, jumpDest4652, hm, FullBase.guardWord, hc,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2889`: the miss arm seeds `R1 = 0x1000` with the word 1 and calls the
Montgomery-form conversion (pc 2081) with return address 1300, the old `r0` block.

This call does not sit on the shared setup path, which every fast route runs.  It sits
here, so it runs only on the recogniser-miss route -- the only route that reads `R1`; the
recogniser-hit routes set up what they need themselves.  The conversion's own exit copies
its result into `R1` (`ShiftTrace3.run_shiftDone`). -/
theorem run_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2889
      (missState s mem n bsize esize msize) =
      some (Exp.r1Call s (Exp.storeWord mem 4096 (UInt256.ofNat 1)) 4096
        (UInt256.ofNat 1300) n bsize esize msize) := by
  have haw : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 4096 32) = s.activeWords :=
    Monpro.activeWords_fix s 4096 32 (by decide) (by omega) (by omega)
  simp (config := { maxSteps := 400000 })
    [blk2889, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      missState, frameState, pcMiss, Exp.r1Call, Exp.storeWord, outer, Exp.outer,
      hcode, hrun, jumpDest2322, haw, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2874`: copy the raw base to `ACC` and `TS`, clear `TN`, call `CSUB`. -/
theorem run_hit (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2874
      (hitState s mem n bsize esize msize) =
      some (Csub.csEntryState s (hitMem mem input n) (UInt256.ofNat 2048)
        (UInt256.ofNat pcAfterCsub0) (outer n bsize esize msize)) := by
  have hsize : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by decide)
  have haw1 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 1024 (32 * n)) = s.activeWords :=
    Monpro.activeWords_fix s 1024 (32 * n) (by omega) (by omega) (by omega)
  have haw2 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8256 (32 * n)) = s.activeWords :=
    Monpro.activeWords_fix s 8256 (32 * n) (by omega) (by omega) (by omega)
  have haw3 : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    Monpro.activeWords_fix s 8224 32 (by decide) (by omega) (by omega)
  simp (config := { maxSteps := 400000 })
    [blk2874, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hitState, frameState, pcHit, pcAfterCsub0, Csub.csEntryState, hitMem,
      FullBase.copyBaseMem, Exp.storeWord, outer, Exp.outer,
      hcode, hrun, hdata, hsize, haw1, haw2, haw3, jumpDest4976, Exp.push0_word,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2892`: back from `CSUB`, push the carry `1` and the limb-0 pointer. -/
theorem run_negEntry (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2892
      (afterCsub0State s mem n bsize esize msize) =
      some (negLoopState s mem n bsize esize msize 0) := by
  have haw : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) = s.activeWords :=
    Monpro.activeWords_fix s 9408 32 (by decide) (by omega) hact
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
    (hn32 : n ≤ 32) (hj : j < n) (hpv : p.toNat = 32 * (n - 1 - j))
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896a
      { s with pc := UInt256.ofNat pcNegLoop
               stack := p :: (negStep mem n j).flag :: outer n bsize esize msize
               memory := (negStep mem n j).memory } =
      some { s with pc := UInt256.ofNat pcNegMid
                    stack := p :: (negStep mem n (j + 1)).flag :: outer n bsize esize msize
                    memory := (negStep mem n (j + 1)).memory } := by
  have hdst : (5120 + 32 * (n - 1 - j)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      5120 + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have hawL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hawS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (5120 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk2896a, opAt, pushAt, wfOp,
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

/-- `blk2896b`: the exit test with a nonzero pointer falls into the decrement. -/
theorem run_negTail (s : State) (m : ByteArray) (p c : UInt256) (n bsize esize msize : Nat)
    (hp0 : p.toNat ≠ 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896b
      { s with pc := UInt256.ofNat pcNegMid
               stack := p :: c :: outer n bsize esize msize
               memory := m } =
      some { s with pc := UInt256.ofNat pcNegNext
                    stack := p :: c :: outer n bsize esize msize
                    memory := m } := by
  simp (config := { maxSteps := 200000 })
    [blk2896b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcNegMid, pcNegNext, outer, Exp.outer, hcode, hrun, hp0, jumpDest4725,
      UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

/-- `blk2896` on the last limb: store limb `n - 1`, jump to `NEG_DONE`. -/
theorem run_negLast (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2896
      (negLoopState s mem n bsize esize msize (n - 1)) =
      some (negDoneState s mem n bsize esize msize) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp : Monpro.ptrAt (32 * (m + 1) - 32) m %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by
    rw [Monpro.ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hp0 : UInt256.ofNat (Monpro.ptrAt (32 * (m + 1) - 32) m) = UInt256.ofNat 0 := by
    rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat (UInt256.ofNat (Monpro.ptrAt _ _)),
      Monpro.ptrAt_toNat _ _ (by omega) (by omega)]
    congr 1; omega
  have hdst : (5120 + Monpro.ptrAt (32 * (m + 1) - 32) m) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      5120 := by
    rw [Nat.add_mod, Monpro.ptrAt_mod _ _ (by omega) (by omega)]
    rw [Nat.mod_eq_of_lt (a := 5120) (by decide)]
    rw [show 32 * (m + 1) - 32 - 32 * m = 0 by omega]
  have hidx : m + 1 - 1 - m = 0 := by omega
  have hawL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hawS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 5120 32) =
      s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk2896, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      negLoopState, negDoneState, pcNegLoop, pcNegDone, negStep, NEG,
      outer, Exp.outer, hcode, hrun, hp, hp0, hdst, hidx, hawL, hawS, jumpDest4725,
      UInt256.isZero, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt, List.exchange]

/-- `blk2915`: decrement the pointer and jump back to the loop head. -/
theorem run_negNext (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2915
      (negNextState s mem n bsize esize msize j) =
      some (negLoopState s mem n bsize esize msize (j + 1)) := by
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  simp (config := { maxSteps := 200000 })
    [blk2915, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      negLoopState, negNextState, pcNegLoop, pcNegNext,
      outer, Exp.outer, hcode, hrun, hK, jumpDest4664, Monpro.ptrAt_succ,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk2919`: drop the loop words, store `L`, `dodd`, `X`, `Bmod`. -/
theorem run_negDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2919
      (negDoneState s mem n bsize esize msize) =
      some (preNewtonState s (negStep mem n n).memory n bsize esize msize) := by
  have haw0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6144 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6176 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw3 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6208 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have haw4 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6240 32) =
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
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2982
      (newtonBState s mem n bsize esize msize) =
      some (shiftLoopState s (preMem mem) n bsize esize msize n) := by
  have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6272 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk2982, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      newtonBState, preNewtonState, shiftLoopState, kState, pcNewtonB, pcShiftLoop,
      preMem, preMemOf, preDinv, newton8W, newtonW, PRE_DINV, Exp.storeWord,
      outer, Exp.outer, hcode, hrun, haw,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
