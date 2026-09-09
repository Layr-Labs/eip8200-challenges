import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 6 of the unrolled exponent-bit body

The copy handles exponent bit 6 at instruction indices 2520 .. 2536 and bytes
3820 .. 3603.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3579 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3599 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2467 := soundW hs (opAt 2617 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2617 3579 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_dup s 3579 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2468 := soundW hs (pushAt 2618 1 1)
    (blockOfW _ (pcFactW s 2618 3580 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_push s 3580 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2469 := soundW hs (opAt 2619 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2619 3582 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3582 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2470 := soundW hs (pushAt 2620 1 1)
    (blockOfW _ (pcFactW s 2620 3583 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_push s 3583 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2471 := soundW hs (opAt 2621 .SHR)
    (blockOfW _ (pcFactW s 2621 3585 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_shr s 3585 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2472 := soundW hs (opAt 2622 .AND)
    (blockOfW _ (pcFactW s 2622 3586 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_and s 3586 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2473 := soundW hs (opAt 2623 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2623 3587 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_dup s 3587 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2474 := soundW hs (opAt 2624 .MUL)
    (blockOfW _ (pcFactW s 2624 3588 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2527)
      (stepW_mul s 3588 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2475 := soundW hs (pushAt 2625 1 1)
    (blockOfW _ (pcFactW s 2625 3589 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2528)
      (stepW_push s 3589 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2476 := soundW hs (opAt 2626 .ADD)
    (blockOfW _ (pcFactW s 2626 3591 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2529)
      (stepW_add s 3591 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2477 := soundW hs (opAt 2627 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2627 3592 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2530)
      (stepW_dup s 3592 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2478 := soundW hs (opAt 2628 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2628 3593 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2531)
      (stepW_dup s 3593 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2479 := soundW hs (opAt 2629 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2629 3594 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3594 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2480 := soundW hs (opAt 2630 .MULMOD)
    (blockOfW _ (pcFactW s 2630 3595 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_mulmod s 3595 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2481 := soundW hs (opAt 2631 .MULMOD)
    (blockOfW _ (pcFactW s 2631 3596 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_mulmod s 3596 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2482 := soundW hs (opAt 2632 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2632 3597 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_swap s 3597 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2483 := soundW hs (opAt 2633 .POP)
    (blockOfW _ (pcFactW s 2633 3598 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2536)
      (stepW_pop s 3598 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2467.trans (step2468.trans (step2469.trans (step2470.trans (step2471.trans (step2472.trans (step2473.trans (step2474.trans (step2475.trans (step2476.trans (step2477.trans (step2478.trans (step2479.trans (step2480.trans (step2481.trans (step2482.trans (step2483))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy6_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy6_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy6_sym
  have c2467 := blockCostW [opAt 2617 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2617 3579 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_dup s 3579 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2468 := blockCostW [pushAt 2618 1 1] 3
    (blockOfW _ (pcFactW s 2618 3580 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_push s 3580 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2469 := blockCostW [opAt 2619 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2619 3582 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3582 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2470 := blockCostW [pushAt 2620 1 1] 3
    (blockOfW _ (pcFactW s 2620 3583 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_push s 3583 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2471 := blockCostW [opAt 2621 .SHR] 3
    (blockOfW _ (pcFactW s 2621 3585 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_shr s 3585 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2472 := blockCostW [opAt 2622 .AND] 3
    (blockOfW _ (pcFactW s 2622 3586 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_and s 3586 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2473 := blockCostW [opAt 2623 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2623 3587 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_dup s 3587 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2474 := blockCostW [opAt 2624 .MUL] 5
    (blockOfW _ (pcFactW s 2624 3588 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2527)
      (stepW_mul s 3588 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2475 := blockCostW [pushAt 2625 1 1] 3
    (blockOfW _ (pcFactW s 2625 3589 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2528)
      (stepW_push s 3589 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2476 := blockCostW [opAt 2626 .ADD] 3
    (blockOfW _ (pcFactW s 2626 3591 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2529)
      (stepW_add s 3591 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2477 := blockCostW [opAt 2627 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2627 3592 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2530)
      (stepW_dup s 3592 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2478 := blockCostW [opAt 2628 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2628 3593 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2531)
      (stepW_dup s 3593 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2479 := blockCostW [opAt 2629 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2629 3594 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3594 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2480 := blockCostW [opAt 2630 .MULMOD] 8
    (blockOfW _ (pcFactW s 2630 3595 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_mulmod s 3595 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2481 := blockCostW [opAt 2631 .MULMOD] 8
    (blockOfW _ (pcFactW s 2631 3596 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_mulmod s 3596 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2482 := blockCostW [opAt 2632 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2632 3597 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_swap s 3597 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2483 := blockCostW [opAt 2633 .POP] 2
    (blockOfW _ (pcFactW s 2633 3598 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2536)
      (stepW_pop s 3598 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
