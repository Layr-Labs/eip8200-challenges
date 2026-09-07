import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 6 of the unrolled exponent-bit body

The copy handles exponent bit 6 at instruction indices 2520 .. 2536 and bytes
3820 .. 3839.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3738 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3758 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2467 := soundW hs (opAt 2422 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2422 3738 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_dup s 3738 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2468 := soundW hs (pushAt 2423 1 1)
    (blockOfW _ (pcFactW s 2423 3739 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_push s 3739 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2469 := soundW hs (opAt 2424 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2424 3741 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3741 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2470 := soundW hs (pushAt 2425 1 1)
    (blockOfW _ (pcFactW s 2425 3742 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_push s 3742 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2471 := soundW hs (opAt 2426 .SHR)
    (blockOfW _ (pcFactW s 2426 3744 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_shr s 3744 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2472 := soundW hs (opAt 2427 .AND)
    (blockOfW _ (pcFactW s 2427 3745 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_and s 3745 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2473 := soundW hs (opAt 2428 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2428 3746 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_dup s 3746 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2474 := soundW hs (opAt 2429 .MUL)
    (blockOfW _ (pcFactW s 2429 3747 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2527)
      (stepW_mul s 3747 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2475 := soundW hs (pushAt 2430 1 1)
    (blockOfW _ (pcFactW s 2430 3748 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2528)
      (stepW_push s 3748 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2476 := soundW hs (opAt 2431 .ADD)
    (blockOfW _ (pcFactW s 2431 3750 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2529)
      (stepW_add s 3750 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2477 := soundW hs (opAt 2432 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2432 3751 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2530)
      (stepW_dup s 3751 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2478 := soundW hs (opAt 2433 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2433 3752 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2531)
      (stepW_dup s 3752 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2479 := soundW hs (opAt 2434 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2434 3753 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3753 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2480 := soundW hs (opAt 2435 .MULMOD)
    (blockOfW _ (pcFactW s 2435 3754 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_mulmod s 3754 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2481 := soundW hs (opAt 2436 .MULMOD)
    (blockOfW _ (pcFactW s 2436 3755 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_mulmod s 3755 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2482 := soundW hs (opAt 2437 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2437 3756 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_swap s 3756 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2483 := soundW hs (opAt 2438 .POP)
    (blockOfW _ (pcFactW s 2438 3757 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2536)
      (stepW_pop s 3757 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2467.trans (step2468.trans (step2469.trans (step2470.trans (step2471.trans (step2472.trans (step2473.trans (step2474.trans (step2475.trans (step2476.trans (step2477.trans (step2478.trans (step2479.trans (step2480.trans (step2481.trans (step2482.trans (step2483))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy6_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy6_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy6_sym
  have c2467 := blockCostW [opAt 2422 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2422 3738 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_dup s 3738 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2468 := blockCostW [pushAt 2423 1 1] 3
    (blockOfW _ (pcFactW s 2423 3739 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_push s 3739 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2469 := blockCostW [opAt 2424 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2424 3741 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3741 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2470 := blockCostW [pushAt 2425 1 1] 3
    (blockOfW _ (pcFactW s 2425 3742 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_push s 3742 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2471 := blockCostW [opAt 2426 .SHR] 3
    (blockOfW _ (pcFactW s 2426 3744 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_shr s 3744 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2472 := blockCostW [opAt 2427 .AND] 3
    (blockOfW _ (pcFactW s 2427 3745 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_and s 3745 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2473 := blockCostW [opAt 2428 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2428 3746 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_dup s 3746 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2474 := blockCostW [opAt 2429 .MUL] 5
    (blockOfW _ (pcFactW s 2429 3747 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2527)
      (stepW_mul s 3747 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2475 := blockCostW [pushAt 2430 1 1] 3
    (blockOfW _ (pcFactW s 2430 3748 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2528)
      (stepW_push s 3748 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2476 := blockCostW [opAt 2431 .ADD] 3
    (blockOfW _ (pcFactW s 2431 3750 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2529)
      (stepW_add s 3750 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2477 := blockCostW [opAt 2432 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2432 3751 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2530)
      (stepW_dup s 3751 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2478 := blockCostW [opAt 2433 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2433 3752 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2531)
      (stepW_dup s 3752 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2479 := blockCostW [opAt 2434 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2434 3753 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2532)
      (stepW_dup s 3753 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2480 := blockCostW [opAt 2435 .MULMOD] 8
    (blockOfW _ (pcFactW s 2435 3754 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2533)
      (stepW_mulmod s 3754 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2481 := blockCostW [opAt 2436 .MULMOD] 8
    (blockOfW _ (pcFactW s 2436 3755 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2534)
      (stepW_mulmod s 3755 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2482 := blockCostW [opAt 2437 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2437 3756 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2535)
      (stepW_swap s 3756 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2483 := blockCostW [opAt 2438 .POP] 2
    (blockOfW _ (pcFactW s 2438 3757 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2536)
      (stepW_pop s 3757 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
