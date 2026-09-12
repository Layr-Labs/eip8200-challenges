import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000
/-!
# Copy 5 of the unrolled exponent-bit body

This copy handles exponent bit 5, from PC 3323 to PC 3343. Its 17 retained instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 5, with every stack slot left symbolic. -/
def gasSteps_bitCopy5_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3049 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3069 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2450 := soundW hs (opAt 2359 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2363 3049 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2503)
      (stepW_dup s 3049 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2451 := soundW hs (pushAt 2360 1 1)
    (blockOfW _ (pcFactW s 2364 3050 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2504)
      (stepW_push s 3050 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2452 := soundW hs (opAt 2361 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2365 3052 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2505)
      (stepW_dup s 3052 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2453 := soundW hs (pushAt 2362 1 2)
    (blockOfW _ (pcFactW s 2366 3053 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2506)
      (stepW_push s 3053 1 (2 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2454 := soundW hs (opAt 2363 .SHR)
    (blockOfW _ (pcFactW s 2367 3055 ([(2 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2507)
      (stepW_shr s 3055 ((2 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2455 := soundW hs (opAt 2364 .AND)
    (blockOfW _ (pcFactW s 2368 3056 ([(UInt256.shiftRight byte (2 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2508)
      (stepW_and s 3056 ((UInt256.shiftRight byte (2 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2456 := soundW hs (opAt 2365 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2369 3057 ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2509)
      (stepW_dup s 3057 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2457 := soundW hs (opAt 2366 .MUL)
    (blockOfW _ (pcFactW s 2370 3058 ([Bm1, (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2510)
      (stepW_mul s 3058 (Bm1) ((UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2458 := soundW hs (pushAt 2367 1 1)
    (blockOfW _ (pcFactW s 2371 3059 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2511)
      (stepW_push s 3059 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2459 := soundW hs (opAt 2368 .ADD)
    (blockOfW _ (pcFactW s 2372 3061 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2512)
      (stepW_add s 3061 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2460 := soundW hs (opAt 2369 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2373 3062 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2513)
      (stepW_dup s 3062 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2461 := soundW hs (opAt 2370 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2374 3063 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2514)
      (stepW_dup s 3063 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2462 := soundW hs (opAt 2371 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2375 3064 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2515)
      (stepW_dup s 3064 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2463 := soundW hs (opAt 2372 .MULMOD)
    (blockOfW _ (pcFactW s 2376 3065 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2516)
      (stepW_mulmod s 3065 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2464 := soundW hs (opAt 2373 .MULMOD)
    (blockOfW _ (pcFactW s 2377 3066 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2517)
      (stepW_mulmod s 3066 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2465 := soundW hs (opAt 2374 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2378 3067 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2518)
      (stepW_swap s 3067 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2466 := soundW hs (opAt 2375 .POP)
    (blockOfW _ (pcFactW s 2379 3068 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2519)
      (stepW_pop s 3068 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2450.trans (step2451.trans (step2452.trans (step2453.trans (step2454.trans (step2455.trans (step2456.trans (step2457.trans (step2458.trans (step2459.trans (step2460.trans (step2461.trans (step2462.trans (step2463.trans (step2464.trans (step2465.trans (step2466))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy5_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy5_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy5_sym
  have c2450 := blockCostW [opAt 2359 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2363 3049 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2503)
      (stepW_dup s 3049 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2451 := blockCostW [pushAt 2360 1 1] 3
    (blockOfW _ (pcFactW s 2364 3050 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2504)
      (stepW_push s 3050 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2452 := blockCostW [opAt 2361 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2365 3052 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2505)
      (stepW_dup s 3052 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2453 := blockCostW [pushAt 2362 1 2] 3
    (blockOfW _ (pcFactW s 2366 3053 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2506)
      (stepW_push s 3053 1 (2 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2454 := blockCostW [opAt 2363 .SHR] 3
    (blockOfW _ (pcFactW s 2367 3055 ([(2 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2507)
      (stepW_shr s 3055 ((2 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2455 := blockCostW [opAt 2364 .AND] 3
    (blockOfW _ (pcFactW s 2368 3056 ([(UInt256.shiftRight byte (2 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2508)
      (stepW_and s 3056 ((UInt256.shiftRight byte (2 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2456 := blockCostW [opAt 2365 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2369 3057 ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2509)
      (stepW_dup s 3057 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2457 := blockCostW [opAt 2366 .MUL] 5
    (blockOfW _ (pcFactW s 2370 3058 ([Bm1, (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2510)
      (stepW_mul s 3058 (Bm1) ((UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2458 := blockCostW [pushAt 2367 1 1] 3
    (blockOfW _ (pcFactW s 2371 3059 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2511)
      (stepW_push s 3059 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2459 := blockCostW [opAt 2368 .ADD] 3
    (blockOfW _ (pcFactW s 2372 3061 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2512)
      (stepW_add s 3061 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2460 := blockCostW [opAt 2369 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2373 3062 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2513)
      (stepW_dup s 3062 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2461 := blockCostW [opAt 2370 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2374 3063 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2514)
      (stepW_dup s 3063 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2462 := blockCostW [opAt 2371 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2375 3064 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2515)
      (stepW_dup s 3064 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2463 := blockCostW [opAt 2372 .MULMOD] 8
    (blockOfW _ (pcFactW s 2376 3065 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2516)
      (stepW_mulmod s 3065 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2464 := blockCostW [opAt 2373 .MULMOD] 8
    (blockOfW _ (pcFactW s 2377 3066 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2517)
      (stepW_mulmod s 3066 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2465 := blockCostW [opAt 2374 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2378 3067 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2518)
      (stepW_swap s 3067 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2466 := blockCostW [opAt 2375 .POP] 2
    (blockOfW _ (pcFactW s 2379 3068 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2519)
      (stepW_pop s 3068 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5
