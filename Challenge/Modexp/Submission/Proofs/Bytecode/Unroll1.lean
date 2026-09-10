import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 1 of the unrolled exponent-bit body

The copy handles exponent bit 1 at instruction indices 2435 .. 2208 and bytes
3976 .. 3503.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 1, with every stack slot left symbolic. -/
def gasSteps_bitCopy1_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3446 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3466 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2382 := soundW hs (opAt 2493 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2493 3446 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3446 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2383 := soundW hs (pushAt 2494 1 1)
    (blockOfW _ (pcFactW s 2494 3447 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3447 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2384 := soundW hs (opAt 2495 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2495 3449 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_dup s 3449 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2385 := soundW hs (pushAt 2496 1 6)
    (blockOfW _ (pcFactW s 2496 3450 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_push s 3450 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2386 := soundW hs (opAt 2497 .SHR)
    (blockOfW _ (pcFactW s 2497 3452 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_shr s 3452 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2387 := soundW hs (opAt 2498 .AND)
    (blockOfW _ (pcFactW s 2498 3453 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_and s 3453 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2388 := soundW hs (opAt 2499 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2499 3454 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3454 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2389 := soundW hs (opAt 2500 .MUL)
    (blockOfW _ (pcFactW s 2500 3455 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_mul s 3455 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2390 := soundW hs (pushAt 2501 1 1)
    (blockOfW _ (pcFactW s 2501 3456 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_push s 3456 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2391 := soundW hs (opAt 2502 .ADD)
    (blockOfW _ (pcFactW s 2502 3458 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_add s 3458 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2392 := soundW hs (opAt 2503 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2503 3459 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3459 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2393 := soundW hs (opAt 2504 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2504 3460 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_dup s 3460 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2394 := soundW hs (opAt 2505 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2505 3461 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_dup s 3461 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2395 := soundW hs (opAt 2506 .MULMOD)
    (blockOfW _ (pcFactW s 2506 3462 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_mulmod s 3462 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2396 := soundW hs (opAt 2507 .MULMOD)
    (blockOfW _ (pcFactW s 2507 3463 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2449)
      (stepW_mulmod s 3463 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2397 := soundW hs (opAt 2508 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2508 3464 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2450)
      (stepW_swap s 3464 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2398 := soundW hs (opAt 2509 .POP)
    (blockOfW _ (pcFactW s 2509 3465 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2451)
      (stepW_pop s 3465 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2382.trans (step2383.trans (step2384.trans (step2385.trans (step2386.trans (step2387.trans (step2388.trans (step2389.trans (step2390.trans (step2391.trans (step2392.trans (step2393.trans (step2394.trans (step2395.trans (step2396.trans (step2397.trans (step2398))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy1_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy1_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy1_sym
  have c2382 := blockCostW [opAt 2493 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2493 3446 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3446 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2383 := blockCostW [pushAt 2494 1 1] 3
    (blockOfW _ (pcFactW s 2494 3447 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3447 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2384 := blockCostW [opAt 2495 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2495 3449 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_dup s 3449 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2385 := blockCostW [pushAt 2496 1 6] 3
    (blockOfW _ (pcFactW s 2496 3450 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_push s 3450 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2386 := blockCostW [opAt 2497 .SHR] 3
    (blockOfW _ (pcFactW s 2497 3452 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_shr s 3452 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2387 := blockCostW [opAt 2498 .AND] 3
    (blockOfW _ (pcFactW s 2498 3453 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_and s 3453 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2388 := blockCostW [opAt 2499 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2499 3454 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3454 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2389 := blockCostW [opAt 2500 .MUL] 5
    (blockOfW _ (pcFactW s 2500 3455 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_mul s 3455 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2390 := blockCostW [pushAt 2501 1 1] 3
    (blockOfW _ (pcFactW s 2501 3456 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_push s 3456 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2391 := blockCostW [opAt 2502 .ADD] 3
    (blockOfW _ (pcFactW s 2502 3458 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_add s 3458 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2392 := blockCostW [opAt 2503 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2503 3459 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3459 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2393 := blockCostW [opAt 2504 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2504 3460 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_dup s 3460 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2394 := blockCostW [opAt 2505 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2505 3461 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_dup s 3461 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2395 := blockCostW [opAt 2506 .MULMOD] 8
    (blockOfW _ (pcFactW s 2506 3462 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_mulmod s 3462 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2396 := blockCostW [opAt 2507 .MULMOD] 8
    (blockOfW _ (pcFactW s 2507 3463 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2449)
      (stepW_mulmod s 3463 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2397 := blockCostW [opAt 2508 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2508 3464 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2450)
      (stepW_swap s 3464 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2398 := blockCostW [opAt 2509 .POP] 2
    (blockOfW _ (pcFactW s 2509 3465 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2451)
      (stepW_pop s 3465 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
