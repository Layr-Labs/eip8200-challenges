import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 7 of the unrolled exponent-bit body

The copy handles exponent bit 7 at instruction indices 2537 .. 2553 and bytes
3840 .. 3859.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

private theorem shiftRight_zero (byte : UInt256) :
    UInt256.shiftRight byte (0 : UInt256) = byte := by
  apply Challenge.EvmProof.Word.word_ext
  change (UInt256.shiftRight byte (UInt256.ofNat 0)).toNat = byte.toNat
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num)]
  simp

/-- Copy 7, with every stack slot left symbolic. -/
def gasSteps_bitCopy7_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3853 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3873 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2484 := soundW hs (opAt 2671 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2671 3853 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3853 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2485 := soundW hs (pushAt 2672 1 1)
    (blockOfW _ (pcFactW s 2672 3854 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3854 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2486 := soundW hs (opAt 2673 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2673 3856 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3856 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2487 := soundW hs (pushAt 2674 1 0)
    (blockOfW _ (pcFactW s 2674 3857 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3857 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2488 := (soundW hs (opAt 2675 .POP)
    (blockOfW _ (pcFactW s 2675 3859 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_pop s 3859 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))).cast rfl
        (show stW s 3860 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) =
          stW s 3860 ([UInt256.shiftRight byte (0 : UInt256), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) by
            rw [shiftRight_zero])
  have step2489 := soundW hs (opAt 2676 .AND)
    (blockOfW _ (pcFactW s 2676 3860 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3860 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2490 := soundW hs (opAt 2677 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2677 3861 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3861 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2491 := soundW hs (opAt 2678 .MUL)
    (blockOfW _ (pcFactW s 2678 3862 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3862 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2492 := soundW hs (pushAt 2679 1 1)
    (blockOfW _ (pcFactW s 2679 3863 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3863 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2493 := soundW hs (opAt 2680 .ADD)
    (blockOfW _ (pcFactW s 2680 3865 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3865 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2494 := soundW hs (opAt 2681 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2681 3866 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3866 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2495 := soundW hs (opAt 2682 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2682 3867 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3867 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2496 := soundW hs (opAt 2683 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2683 3868 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3868 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2497 := soundW hs (opAt 2684 .MULMOD)
    (blockOfW _ (pcFactW s 2684 3869 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3869 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2498 := soundW hs (opAt 2685 .MULMOD)
    (blockOfW _ (pcFactW s 2685 3870 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3870 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2499 := soundW hs (opAt 2686 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2686 3871 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3871 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2500 := soundW hs (opAt 2687 .POP)
    (blockOfW _ (pcFactW s 2687 3872 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3872 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2484.trans (step2485.trans (step2486.trans (step2487.trans (step2488.trans (step2489.trans (step2490.trans (step2491.trans (step2492.trans (step2493.trans (step2494.trans (step2495.trans (step2496.trans (step2497.trans (step2498.trans (step2499.trans (step2500))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy7_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy7_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 61 := by
  unfold gasSteps_bitCopy7_sym
  have c2484 := blockCostW [opAt 2671 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2671 3853 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3853 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2485 := blockCostW [pushAt 2672 1 1] 3
    (blockOfW _ (pcFactW s 2672 3854 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3854 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2486 := blockCostW [opAt 2673 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2673 3856 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3856 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2487 := blockCostW [pushAt 2674 1 0] 3
    (blockOfW _ (pcFactW s 2674 3857 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3857 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2488 := blockCostW [opAt 2675 .POP] 2
    (blockOfW _ (pcFactW s 2675 3859 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_pop s 3859 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2489 := blockCostW [opAt 2676 .AND] 3
    (blockOfW _ (pcFactW s 2676 3860 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3860 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2490 := blockCostW [opAt 2677 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2677 3861 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3861 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2491 := blockCostW [opAt 2678 .MUL] 5
    (blockOfW _ (pcFactW s 2678 3862 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3862 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2492 := blockCostW [pushAt 2679 1 1] 3
    (blockOfW _ (pcFactW s 2679 3863 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3863 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2493 := blockCostW [opAt 2680 .ADD] 3
    (blockOfW _ (pcFactW s 2680 3865 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3865 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2494 := blockCostW [opAt 2681 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2681 3866 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3866 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2495 := blockCostW [opAt 2682 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2682 3867 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3867 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2496 := blockCostW [opAt 2683 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2683 3868 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3868 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2497 := blockCostW [opAt 2684 .MULMOD] 8
    (blockOfW _ (pcFactW s 2684 3869 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3869 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2498 := blockCostW [opAt 2685 .MULMOD] 8
    (blockOfW _ (pcFactW s 2685 3870 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3870 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2499 := blockCostW [opAt 2686 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2686 3871 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3871 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2500 := blockCostW [opAt 2687 .POP] 2
    (blockOfW _ (pcFactW s 2687 3872 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3872 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.cast_cost, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
