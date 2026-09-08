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
    GasSteps (stW s 3835 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3855 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2484 := soundW hs (opAt 2370 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2370 3835 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3835 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2485 := soundW hs (pushAt 2371 1 1)
    (blockOfW _ (pcFactW s 2371 3836 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3836 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2486 := soundW hs (opAt 2372 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2372 3838 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3838 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2487 := soundW hs (pushAt 2373 1 0)
    (blockOfW _ (pcFactW s 2373 3839 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3839 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2488 := (soundW hs (opAt 2374 .POP)
    (blockOfW _ (pcFactW s 2374 3841 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_pop s 3841 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))).cast rfl
        (show stW s 3842 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) =
          stW s 3842 ([UInt256.shiftRight byte (0 : UInt256), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) by
            rw [shiftRight_zero])
  have step2489 := soundW hs (opAt 2375 .AND)
    (blockOfW _ (pcFactW s 2375 3842 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3842 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2490 := soundW hs (opAt 2376 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2376 3843 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3843 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2491 := soundW hs (opAt 2377 .MUL)
    (blockOfW _ (pcFactW s 2377 3844 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3844 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2492 := soundW hs (pushAt 2378 1 1)
    (blockOfW _ (pcFactW s 2378 3845 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3845 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2493 := soundW hs (opAt 2379 .ADD)
    (blockOfW _ (pcFactW s 2379 3847 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3847 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2494 := soundW hs (opAt 2380 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2380 3848 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3848 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2495 := soundW hs (opAt 2381 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2381 3849 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3849 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2496 := soundW hs (opAt 2382 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2382 3850 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3850 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2497 := soundW hs (opAt 2383 .MULMOD)
    (blockOfW _ (pcFactW s 2383 3851 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3851 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2498 := soundW hs (opAt 2384 .MULMOD)
    (blockOfW _ (pcFactW s 2384 3852 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3852 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2499 := soundW hs (opAt 2385 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2385 3853 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3853 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2500 := soundW hs (opAt 2386 .POP)
    (blockOfW _ (pcFactW s 2386 3854 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3854 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2484.trans (step2485.trans (step2486.trans (step2487.trans (step2488.trans (step2489.trans (step2490.trans (step2491.trans (step2492.trans (step2493.trans (step2494.trans (step2495.trans (step2496.trans (step2497.trans (step2498.trans (step2499.trans (step2500))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy7_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy7_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 61 := by
  unfold gasSteps_bitCopy7_sym
  have c2484 := blockCostW [opAt 2370 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2370 3835 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2537)
      (stepW_dup s 3835 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2485 := blockCostW [pushAt 2371 1 1] 3
    (blockOfW _ (pcFactW s 2371 3836 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2538)
      (stepW_push s 3836 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2486 := blockCostW [opAt 2372 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2372 3838 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2539)
      (stepW_dup s 3838 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2487 := blockCostW [pushAt 2373 1 0] 3
    (blockOfW _ (pcFactW s 2373 3839 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2540)
      (stepW_push s 3839 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2488 := blockCostW [opAt 2374 .POP] 2
    (blockOfW _ (pcFactW s 2374 3841 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2541)
      (stepW_pop s 3841 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2489 := blockCostW [opAt 2375 .AND] 3
    (blockOfW _ (pcFactW s 2375 3842 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2542)
      (stepW_and s 3842 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2490 := blockCostW [opAt 2376 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2376 3843 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2543)
      (stepW_dup s 3843 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2491 := blockCostW [opAt 2377 .MUL] 5
    (blockOfW _ (pcFactW s 2377 3844 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2544)
      (stepW_mul s 3844 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2492 := blockCostW [pushAt 2378 1 1] 3
    (blockOfW _ (pcFactW s 2378 3845 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2545)
      (stepW_push s 3845 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2493 := blockCostW [opAt 2379 .ADD] 3
    (blockOfW _ (pcFactW s 2379 3847 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2546)
      (stepW_add s 3847 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2494 := blockCostW [opAt 2380 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2380 3848 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2547)
      (stepW_dup s 3848 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2495 := blockCostW [opAt 2381 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2381 3849 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2548)
      (stepW_dup s 3849 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2496 := blockCostW [opAt 2382 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2382 3850 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2549)
      (stepW_dup s 3850 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2497 := blockCostW [opAt 2383 .MULMOD] 8
    (blockOfW _ (pcFactW s 2383 3851 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2550)
      (stepW_mulmod s 3851 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2498 := blockCostW [opAt 2384 .MULMOD] 8
    (blockOfW _ (pcFactW s 2384 3852 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2551)
      (stepW_mulmod s 3852 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2499 := blockCostW [opAt 2385 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2385 3853 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2552)
      (stepW_swap s 3853 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2500 := blockCostW [opAt 2386 .POP] 2
    (blockOfW _ (pcFactW s 2386 3854 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2553)
      (stepW_pop s 3854 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.cast_cost, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
