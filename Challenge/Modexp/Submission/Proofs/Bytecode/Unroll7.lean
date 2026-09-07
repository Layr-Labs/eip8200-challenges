import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 7 of the unrolled exponent-bit body

The copy handles exponent bit 7 at instruction indices 2532 .. 2548 and bytes
3833 .. 3852.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 7, with every stack slot left symbolic. -/
def gasSteps_bitCopy7_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3833 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3853 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2484 := soundW hs (opAt 2532 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2532 3833 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3833 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2485 := soundW hs (pushAt 2533 1 1)
    (blockOfW _ (pcFactW s 2533 3834 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_push s 3834 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2486 := soundW hs (opAt 2534 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2534 3836 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_dup s 3836 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2487 := soundW hs (pushAt 2535 1 0)
    (blockOfW _ (pcFactW s 2535 3837 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_push s 3837 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2488 := soundW hs (opAt 2536 .SHR)
    (blockOfW _ (pcFactW s 2536 3839 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2536)
      (stepW_shr s 3839 ((0 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2489 := soundW hs (opAt 2537 .AND)
    (blockOfW _ (pcFactW s 2537 3840 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_and s 3840 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2490 := soundW hs (opAt 2538 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2538 3841 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_dup s 3841 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2491 := soundW hs (opAt 2539 .MUL)
    (blockOfW _ (pcFactW s 2539 3842 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_mul s 3842 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2492 := soundW hs (pushAt 2540 1 1)
    (blockOfW _ (pcFactW s 2540 3843 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3843 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2493 := soundW hs (opAt 2541 .ADD)
    (blockOfW _ (pcFactW s 2541 3845 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_add s 3845 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2494 := soundW hs (opAt 2542 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2542 3846 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_dup s 3846 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2495 := soundW hs (opAt 2543 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2543 3847 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3847 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2496 := soundW hs (opAt 2544 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2544 3848 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_dup s 3848 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2497 := soundW hs (opAt 2545 .MULMOD)
    (blockOfW _ (pcFactW s 2545 3849 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_mulmod s 3849 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2498 := soundW hs (opAt 2546 .MULMOD)
    (blockOfW _ (pcFactW s 2546 3850 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_mulmod s 3850 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2499 := soundW hs (opAt 2547 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2547 3851 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_swap s 3851 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2500 := soundW hs (opAt 2548 .POP)
    (blockOfW _ (pcFactW s 2548 3852 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2548)
      (stepW_pop s 3852 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2484.trans (step2485.trans (step2486.trans (step2487.trans (step2488.trans (step2489.trans (step2490.trans (step2491.trans (step2492.trans (step2493.trans (step2494.trans (step2495.trans (step2496.trans (step2497.trans (step2498.trans (step2499.trans (step2500))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy7_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy7_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy7_sym
  have c2484 := blockCostW [opAt 2532 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2532 3833 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3833 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2485 := blockCostW [pushAt 2533 1 1] 3
    (blockOfW _ (pcFactW s 2533 3834 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_push s 3834 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2486 := blockCostW [opAt 2534 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2534 3836 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_dup s 3836 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2487 := blockCostW [pushAt 2535 1 0] 3
    (blockOfW _ (pcFactW s 2535 3837 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_push s 3837 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2488 := blockCostW [opAt 2536 .SHR] 3
    (blockOfW _ (pcFactW s 2536 3839 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2536)
      (stepW_shr s 3839 ((0 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2489 := blockCostW [opAt 2537 .AND] 3
    (blockOfW _ (pcFactW s 2537 3840 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_and s 3840 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2490 := blockCostW [opAt 2538 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2538 3841 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_dup s 3841 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2491 := blockCostW [opAt 2539 .MUL] 5
    (blockOfW _ (pcFactW s 2539 3842 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_mul s 3842 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2492 := blockCostW [pushAt 2540 1 1] 3
    (blockOfW _ (pcFactW s 2540 3843 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3843 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2493 := blockCostW [opAt 2541 .ADD] 3
    (blockOfW _ (pcFactW s 2541 3845 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_add s 3845 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2494 := blockCostW [opAt 2542 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2542 3846 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_dup s 3846 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2495 := blockCostW [opAt 2543 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2543 3847 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3847 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2496 := blockCostW [opAt 2544 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2544 3848 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_dup s 3848 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2497 := blockCostW [opAt 2545 .MULMOD] 8
    (blockOfW _ (pcFactW s 2545 3849 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_mulmod s 3849 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2498 := blockCostW [opAt 2546 .MULMOD] 8
    (blockOfW _ (pcFactW s 2546 3850 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_mulmod s 3850 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2499 := blockCostW [opAt 2547 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2547 3851 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_swap s 3851 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2500 := blockCostW [opAt 2548 .POP] 2
    (blockOfW _ (pcFactW s 2548 3852 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2548)
      (stepW_pop s 3852 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
