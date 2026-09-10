import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 0 of the unrolled exponent-bit body

This copy handles exponent bit 0, from PC 3223 to PC 3243. Its 17 retained instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll0

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 0, with every stack slot left symbolic. -/
def gasSteps_bitCopy0_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3223 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3243 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2365 := soundW hs (opAt 2449 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2449 3223 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2418)
      (stepW_dup s 3223 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2366 := soundW hs (pushAt 2450 1 1)
    (blockOfW _ (pcFactW s 2450 3224 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2419)
      (stepW_push s 3224 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2367 := soundW hs (opAt 2451 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2451 3226 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2420)
      (stepW_dup s 3226 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2368 := soundW hs (pushAt 2452 1 7)
    (blockOfW _ (pcFactW s 2452 3227 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2421)
      (stepW_push s 3227 1 (7 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2369 := soundW hs (opAt 2453 .SHR)
    (blockOfW _ (pcFactW s 2453 3229 ([(7 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2422)
      (stepW_shr s 3229 ((7 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2370 := soundW hs (opAt 2454 .AND)
    (blockOfW _ (pcFactW s 2454 3230 ([(UInt256.shiftRight byte (7 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2423)
      (stepW_and s 3230 ((UInt256.shiftRight byte (7 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2371 := soundW hs (opAt 2455 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2455 3231 ([(UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2424)
      (stepW_dup s 3231 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2372 := soundW hs (opAt 2456 .MUL)
    (blockOfW _ (pcFactW s 2456 3232 ([Bm1, (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2425)
      (stepW_mul s 3232 (Bm1) ((UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2373 := soundW hs (pushAt 2457 1 1)
    (blockOfW _ (pcFactW s 2457 3233 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2426)
      (stepW_push s 3233 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2374 := soundW hs (opAt 2458 .ADD)
    (blockOfW _ (pcFactW s 2458 3235 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2427)
      (stepW_add s 3235 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2375 := soundW hs (opAt 2459 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2459 3236 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2428)
      (stepW_dup s 3236 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2376 := soundW hs (opAt 2460 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2460 3237 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2429)
      (stepW_dup s 3237 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2377 := soundW hs (opAt 2461 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2461 3238 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2430)
      (stepW_dup s 3238 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2378 := soundW hs (opAt 2462 .MULMOD)
    (blockOfW _ (pcFactW s 2462 3239 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_mulmod s 3239 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2379 := soundW hs (opAt 2463 .MULMOD)
    (blockOfW _ (pcFactW s 2463 3240 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2432)
      (stepW_mulmod s 3240 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2380 := soundW hs (opAt 2464 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2464 3241 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_swap s 3241 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2381 := soundW hs (opAt 2465 .POP)
    (blockOfW _ (pcFactW s 2465 3242 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2434)
      (stepW_pop s 3242 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2365.trans (step2366.trans (step2367.trans (step2368.trans (step2369.trans (step2370.trans (step2371.trans (step2372.trans (step2373.trans (step2374.trans (step2375.trans (step2376.trans (step2377.trans (step2378.trans (step2379.trans (step2380.trans (step2381))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy0_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy0_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy0_sym
  have c2365 := blockCostW [opAt 2449 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2449 3223 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2418)
      (stepW_dup s 3223 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2366 := blockCostW [pushAt 2450 1 1] 3
    (blockOfW _ (pcFactW s 2450 3224 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2419)
      (stepW_push s 3224 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2367 := blockCostW [opAt 2451 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2451 3226 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2420)
      (stepW_dup s 3226 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2368 := blockCostW [pushAt 2452 1 7] 3
    (blockOfW _ (pcFactW s 2452 3227 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2421)
      (stepW_push s 3227 1 (7 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2369 := blockCostW [opAt 2453 .SHR] 3
    (blockOfW _ (pcFactW s 2453 3229 ([(7 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2422)
      (stepW_shr s 3229 ((7 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2370 := blockCostW [opAt 2454 .AND] 3
    (blockOfW _ (pcFactW s 2454 3230 ([(UInt256.shiftRight byte (7 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2423)
      (stepW_and s 3230 ((UInt256.shiftRight byte (7 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2371 := blockCostW [opAt 2455 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2455 3231 ([(UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2424)
      (stepW_dup s 3231 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2372 := blockCostW [opAt 2456 .MUL] 5
    (blockOfW _ (pcFactW s 2456 3232 ([Bm1, (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2425)
      (stepW_mul s 3232 (Bm1) ((UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2373 := blockCostW [pushAt 2457 1 1] 3
    (blockOfW _ (pcFactW s 2457 3233 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2426)
      (stepW_push s 3233 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2374 := blockCostW [opAt 2458 .ADD] 3
    (blockOfW _ (pcFactW s 2458 3235 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2427)
      (stepW_add s 3235 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2375 := blockCostW [opAt 2459 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2459 3236 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2428)
      (stepW_dup s 3236 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2376 := blockCostW [opAt 2460 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2460 3237 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2429)
      (stepW_dup s 3237 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2377 := blockCostW [opAt 2461 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2461 3238 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2430)
      (stepW_dup s 3238 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2378 := blockCostW [opAt 2462 .MULMOD] 8
    (blockOfW _ (pcFactW s 2462 3239 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_mulmod s 3239 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2379 := blockCostW [opAt 2463 .MULMOD] 8
    (blockOfW _ (pcFactW s 2463 3240 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2432)
      (stepW_mulmod s 3240 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2380 := blockCostW [opAt 2464 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2464 3241 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_swap s 3241 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2381 := blockCostW [opAt 2465 .POP] 2
    (blockOfW _ (pcFactW s 2465 3242 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2434)
      (stepW_pop s 3242 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (7 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll0
