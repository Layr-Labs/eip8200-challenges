import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 6 of the unrolled exponent-bit body

The copy handles exponent bit 6 at instruction indices 2537 .. 2553 and bytes
3852 .. 3871.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 6, with every stack slot left symbolic. -/
def gasSteps_bitCopy6_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3852 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3872 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2537 := soundW hs (opAt 2537 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2537 3852 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3852 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2538 := soundW hs (pushAt 2538 1 1)
    (blockOfW _ (pcFactW s 2538 3853 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3853 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2539 := soundW hs (opAt 2539 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2539 3855 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3855 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2540 := soundW hs (pushAt 2540 1 1)
    (blockOfW _ (pcFactW s 2540 3856 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3856 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2541 := soundW hs (opAt 2541 .SHR)
    (blockOfW _ (pcFactW s 2541 3858 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_shr s 3858 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2542 := soundW hs (opAt 2542 .AND)
    (blockOfW _ (pcFactW s 2542 3859 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3859 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2543 := soundW hs (opAt 2543 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2543 3860 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3860 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2544 := soundW hs (opAt 2544 .MUL)
    (blockOfW _ (pcFactW s 2544 3861 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3861 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2545 := soundW hs (pushAt 2545 1 1)
    (blockOfW _ (pcFactW s 2545 3862 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3862 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2546 := soundW hs (opAt 2546 .ADD)
    (blockOfW _ (pcFactW s 2546 3864 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3864 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2547 := soundW hs (opAt 2547 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2547 3865 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3865 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2548 := soundW hs (opAt 2548 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2548 3866 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3866 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2549 := soundW hs (opAt 2549 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2549 3867 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3867 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2550 := soundW hs (opAt 2550 .MULMOD)
    (blockOfW _ (pcFactW s 2550 3868 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3868 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2551 := soundW hs (opAt 2551 .MULMOD)
    (blockOfW _ (pcFactW s 2551 3869 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3869 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2552 := soundW hs (opAt 2552 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2552 3870 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3870 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2553 := soundW hs (opAt 2553 .POP)
    (blockOfW _ (pcFactW s 2553 3871 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3871 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2537.trans (step2538.trans (step2539.trans (step2540.trans (step2541.trans (step2542.trans (step2543.trans (step2544.trans (step2545.trans (step2546.trans (step2547.trans (step2548.trans (step2549.trans (step2550.trans (step2551.trans (step2552.trans (step2553))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy6_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy6_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy6_sym
  have c2537 := blockCostW [opAt 2537 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2537 3852 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3852 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2538 := blockCostW [pushAt 2538 1 1] 3
    (blockOfW _ (pcFactW s 2538 3853 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3853 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2539 := blockCostW [opAt 2539 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2539 3855 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3855 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2540 := blockCostW [pushAt 2540 1 1] 3
    (blockOfW _ (pcFactW s 2540 3856 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3856 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2541 := blockCostW [opAt 2541 .SHR] 3
    (blockOfW _ (pcFactW s 2541 3858 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_shr s 3858 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2542 := blockCostW [opAt 2542 .AND] 3
    (blockOfW _ (pcFactW s 2542 3859 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3859 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2543 := blockCostW [opAt 2543 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2543 3860 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3860 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2544 := blockCostW [opAt 2544 .MUL] 5
    (blockOfW _ (pcFactW s 2544 3861 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3861 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2545 := blockCostW [pushAt 2545 1 1] 3
    (blockOfW _ (pcFactW s 2545 3862 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3862 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2546 := blockCostW [opAt 2546 .ADD] 3
    (blockOfW _ (pcFactW s 2546 3864 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3864 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2547 := blockCostW [opAt 2547 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2547 3865 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3865 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2548 := blockCostW [opAt 2548 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2548 3866 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3866 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2549 := blockCostW [opAt 2549 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2549 3867 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3867 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2550 := blockCostW [opAt 2550 .MULMOD] 8
    (blockOfW _ (pcFactW s 2550 3868 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3868 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2551 := blockCostW [opAt 2551 .MULMOD] 8
    (blockOfW _ (pcFactW s 2551 3869 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3869 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2552 := blockCostW [opAt 2552 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2552 3870 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3870 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2553 := blockCostW [opAt 2553 .POP] 2
    (blockOfW _ (pcFactW s 2553 3871 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3871 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
