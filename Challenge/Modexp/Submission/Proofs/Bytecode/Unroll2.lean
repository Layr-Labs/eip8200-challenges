import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 2 of the unrolled exponent-bit body

The copy handles exponent bit 2 at instruction indices 2452 .. 2225 and bytes
3996 .. 3523.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 2, with every stack slot left symbolic. -/
def gasSteps_bitCopy2_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3478 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3498 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2399 := soundW hs (opAt 2537 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2537 3478 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2452)
      (stepW_dup s 3478 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2400 := soundW hs (pushAt 2538 1 1)
    (blockOfW _ (pcFactW s 2538 3479 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2453)
      (stepW_push s 3479 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2401 := soundW hs (opAt 2539 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2539 3481 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2454)
      (stepW_dup s 3481 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2402 := soundW hs (pushAt 2540 1 5)
    (blockOfW _ (pcFactW s 2540 3482 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2455)
      (stepW_push s 3482 1 (5 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2403 := soundW hs (opAt 2541 .SHR)
    (blockOfW _ (pcFactW s 2541 3484 ([(5 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2456)
      (stepW_shr s 3484 ((5 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2404 := soundW hs (opAt 2542 .AND)
    (blockOfW _ (pcFactW s 2542 3485 ([(UInt256.shiftRight byte (5 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2457)
      (stepW_and s 3485 ((UInt256.shiftRight byte (5 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2405 := soundW hs (opAt 2543 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2543 3486 ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2458)
      (stepW_dup s 3486 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2406 := soundW hs (opAt 2544 .MUL)
    (blockOfW _ (pcFactW s 2544 3487 ([Bm1, (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2459)
      (stepW_mul s 3487 (Bm1) ((UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2407 := soundW hs (pushAt 2545 1 1)
    (blockOfW _ (pcFactW s 2545 3488 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2460)
      (stepW_push s 3488 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2408 := soundW hs (opAt 2546 .ADD)
    (blockOfW _ (pcFactW s 2546 3490 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2461)
      (stepW_add s 3490 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2409 := soundW hs (opAt 2547 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2547 3491 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2462)
      (stepW_dup s 3491 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2410 := soundW hs (opAt 2548 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2548 3492 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2463)
      (stepW_dup s 3492 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2411 := soundW hs (opAt 2549 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2549 3493 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2464)
      (stepW_dup s 3493 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2412 := soundW hs (opAt 2550 .MULMOD)
    (blockOfW _ (pcFactW s 2550 3494 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2465)
      (stepW_mulmod s 3494 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2413 := soundW hs (opAt 2551 .MULMOD)
    (blockOfW _ (pcFactW s 2551 3495 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2466)
      (stepW_mulmod s 3495 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2414 := soundW hs (opAt 2552 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2552 3496 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2467)
      (stepW_swap s 3496 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2415 := soundW hs (opAt 2553 .POP)
    (blockOfW _ (pcFactW s 2553 3497 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2468)
      (stepW_pop s 3497 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2399.trans (step2400.trans (step2401.trans (step2402.trans (step2403.trans (step2404.trans (step2405.trans (step2406.trans (step2407.trans (step2408.trans (step2409.trans (step2410.trans (step2411.trans (step2412.trans (step2413.trans (step2414.trans (step2415))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy2_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy2_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy2_sym
  have c2399 := blockCostW [opAt 2537 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2537 3478 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2452)
      (stepW_dup s 3478 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2400 := blockCostW [pushAt 2538 1 1] 3
    (blockOfW _ (pcFactW s 2538 3479 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2453)
      (stepW_push s 3479 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2401 := blockCostW [opAt 2539 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2539 3481 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2454)
      (stepW_dup s 3481 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2402 := blockCostW [pushAt 2540 1 5] 3
    (blockOfW _ (pcFactW s 2540 3482 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2455)
      (stepW_push s 3482 1 (5 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2403 := blockCostW [opAt 2541 .SHR] 3
    (blockOfW _ (pcFactW s 2541 3484 ([(5 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2456)
      (stepW_shr s 3484 ((5 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2404 := blockCostW [opAt 2542 .AND] 3
    (blockOfW _ (pcFactW s 2542 3485 ([(UInt256.shiftRight byte (5 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2457)
      (stepW_and s 3485 ((UInt256.shiftRight byte (5 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2405 := blockCostW [opAt 2543 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2543 3486 ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2458)
      (stepW_dup s 3486 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2406 := blockCostW [opAt 2544 .MUL] 5
    (blockOfW _ (pcFactW s 2544 3487 ([Bm1, (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2459)
      (stepW_mul s 3487 (Bm1) ((UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2407 := blockCostW [pushAt 2545 1 1] 3
    (blockOfW _ (pcFactW s 2545 3488 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2460)
      (stepW_push s 3488 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2408 := blockCostW [opAt 2546 .ADD] 3
    (blockOfW _ (pcFactW s 2546 3490 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2461)
      (stepW_add s 3490 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2409 := blockCostW [opAt 2547 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2547 3491 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2462)
      (stepW_dup s 3491 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2410 := blockCostW [opAt 2548 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2548 3492 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2463)
      (stepW_dup s 3492 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2411 := blockCostW [opAt 2549 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2549 3493 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2464)
      (stepW_dup s 3493 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2412 := blockCostW [opAt 2550 .MULMOD] 8
    (blockOfW _ (pcFactW s 2550 3494 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2465)
      (stepW_mulmod s 3494 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2413 := blockCostW [opAt 2551 .MULMOD] 8
    (blockOfW _ (pcFactW s 2551 3495 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2466)
      (stepW_mulmod s 3495 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2414 := blockCostW [opAt 2552 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2552 3496 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2467)
      (stepW_swap s 3496 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2415 := blockCostW [opAt 2553 .POP] 2
    (blockOfW _ (pcFactW s 2553 3497 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2468)
      (stepW_pop s 3497 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2
