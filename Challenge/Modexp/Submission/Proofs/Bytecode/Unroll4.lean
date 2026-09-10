import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 4 of the unrolled exponent-bit body

This copy handles exponent bit 4, from PC 3303 to PC 3323. Its 17 retained instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 4, with every stack slot left symbolic. -/
def gasSteps_bitCopy4_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3303 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3323 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2433 := soundW hs (opAt 2517 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2517 3303 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2486)
      (stepW_dup s 3303 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2434 := soundW hs (pushAt 2518 1 1)
    (blockOfW _ (pcFactW s 2518 3304 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2487)
      (stepW_push s 3304 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2435 := soundW hs (opAt 2519 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2519 3306 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2488)
      (stepW_dup s 3306 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2436 := soundW hs (pushAt 2520 1 3)
    (blockOfW _ (pcFactW s 2520 3307 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2489)
      (stepW_push s 3307 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2437 := soundW hs (opAt 2521 .SHR)
    (blockOfW _ (pcFactW s 2521 3309 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2490)
      (stepW_shr s 3309 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2438 := soundW hs (opAt 2522 .AND)
    (blockOfW _ (pcFactW s 2522 3310 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2491)
      (stepW_and s 3310 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2439 := soundW hs (opAt 2523 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2523 3311 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2492)
      (stepW_dup s 3311 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2440 := soundW hs (opAt 2524 .MUL)
    (blockOfW _ (pcFactW s 2524 3312 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2493)
      (stepW_mul s 3312 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2441 := soundW hs (pushAt 2525 1 1)
    (blockOfW _ (pcFactW s 2525 3313 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2494)
      (stepW_push s 3313 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2442 := soundW hs (opAt 2526 .ADD)
    (blockOfW _ (pcFactW s 2526 3315 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2495)
      (stepW_add s 3315 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2443 := soundW hs (opAt 2527 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2527 3316 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2496)
      (stepW_dup s 3316 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2444 := soundW hs (opAt 2528 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2528 3317 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2497)
      (stepW_dup s 3317 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2445 := soundW hs (opAt 2529 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2529 3318 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2498)
      (stepW_dup s 3318 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2446 := soundW hs (opAt 2530 .MULMOD)
    (blockOfW _ (pcFactW s 2530 3319 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2499)
      (stepW_mulmod s 3319 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2447 := soundW hs (opAt 2531 .MULMOD)
    (blockOfW _ (pcFactW s 2531 3320 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2500)
      (stepW_mulmod s 3320 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2448 := soundW hs (opAt 2532 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2532 3321 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2501)
      (stepW_swap s 3321 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2449 := soundW hs (opAt 2533 .POP)
    (blockOfW _ (pcFactW s 2533 3322 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2502)
      (stepW_pop s 3322 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2433.trans (step2434.trans (step2435.trans (step2436.trans (step2437.trans (step2438.trans (step2439.trans (step2440.trans (step2441.trans (step2442.trans (step2443.trans (step2444.trans (step2445.trans (step2446.trans (step2447.trans (step2448.trans (step2449))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy4_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy4_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy4_sym
  have c2433 := blockCostW [opAt 2517 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2517 3303 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2486)
      (stepW_dup s 3303 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2434 := blockCostW [pushAt 2518 1 1] 3
    (blockOfW _ (pcFactW s 2518 3304 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2487)
      (stepW_push s 3304 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2435 := blockCostW [opAt 2519 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2519 3306 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2488)
      (stepW_dup s 3306 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2436 := blockCostW [pushAt 2520 1 3] 3
    (blockOfW _ (pcFactW s 2520 3307 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2489)
      (stepW_push s 3307 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2437 := blockCostW [opAt 2521 .SHR] 3
    (blockOfW _ (pcFactW s 2521 3309 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2490)
      (stepW_shr s 3309 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2438 := blockCostW [opAt 2522 .AND] 3
    (blockOfW _ (pcFactW s 2522 3310 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2491)
      (stepW_and s 3310 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2439 := blockCostW [opAt 2523 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2523 3311 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2492)
      (stepW_dup s 3311 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2440 := blockCostW [opAt 2524 .MUL] 5
    (blockOfW _ (pcFactW s 2524 3312 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2493)
      (stepW_mul s 3312 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2441 := blockCostW [pushAt 2525 1 1] 3
    (blockOfW _ (pcFactW s 2525 3313 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2494)
      (stepW_push s 3313 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2442 := blockCostW [opAt 2526 .ADD] 3
    (blockOfW _ (pcFactW s 2526 3315 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2495)
      (stepW_add s 3315 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2443 := blockCostW [opAt 2527 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2527 3316 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2496)
      (stepW_dup s 3316 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2444 := blockCostW [opAt 2528 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2528 3317 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2497)
      (stepW_dup s 3317 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2445 := blockCostW [opAt 2529 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2529 3318 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2498)
      (stepW_dup s 3318 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2446 := blockCostW [opAt 2530 .MULMOD] 8
    (blockOfW _ (pcFactW s 2530 3319 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2499)
      (stepW_mulmod s 3319 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2447 := blockCostW [opAt 2531 .MULMOD] 8
    (blockOfW _ (pcFactW s 2531 3320 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2500)
      (stepW_mulmod s 3320 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2448 := blockCostW [opAt 2532 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2532 3321 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2501)
      (stepW_swap s 3321 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2449 := blockCostW [opAt 2533 .POP] 2
    (blockOfW _ (pcFactW s 2533 3322 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2502)
      (stepW_pop s 3322 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
