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
    GasSteps (stW s 3215 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3235 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2433 := soundW hs (opAt 2472 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2472 3215 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2486)
      (stepW_dup s 3215 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2434 := soundW hs (pushAt 2473 1 1)
    (blockOfW _ (pcFactW s 2473 3216 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2487)
      (stepW_push s 3216 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2435 := soundW hs (opAt 2474 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2474 3218 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2488)
      (stepW_dup s 3218 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2436 := soundW hs (pushAt 2475 1 3)
    (blockOfW _ (pcFactW s 2475 3219 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2489)
      (stepW_push s 3219 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2437 := soundW hs (opAt 2476 .SHR)
    (blockOfW _ (pcFactW s 2476 3221 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2490)
      (stepW_shr s 3221 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2438 := soundW hs (opAt 2477 .AND)
    (blockOfW _ (pcFactW s 2477 3222 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2491)
      (stepW_and s 3222 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2439 := soundW hs (opAt 2478 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2478 3223 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2492)
      (stepW_dup s 3223 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2440 := soundW hs (opAt 2479 .MUL)
    (blockOfW _ (pcFactW s 2479 3224 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2493)
      (stepW_mul s 3224 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2441 := soundW hs (pushAt 2480 1 1)
    (blockOfW _ (pcFactW s 2480 3225 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2494)
      (stepW_push s 3225 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2442 := soundW hs (opAt 2481 .ADD)
    (blockOfW _ (pcFactW s 2481 3227 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2495)
      (stepW_add s 3227 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2443 := soundW hs (opAt 2482 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2482 3228 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2496)
      (stepW_dup s 3228 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2444 := soundW hs (opAt 2483 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2483 3229 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2497)
      (stepW_dup s 3229 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2445 := soundW hs (opAt 2484 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2484 3230 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2498)
      (stepW_dup s 3230 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2446 := soundW hs (opAt 2485 .MULMOD)
    (blockOfW _ (pcFactW s 2485 3231 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2499)
      (stepW_mulmod s 3231 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2447 := soundW hs (opAt 2486 .MULMOD)
    (blockOfW _ (pcFactW s 2486 3232 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2500)
      (stepW_mulmod s 3232 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2448 := soundW hs (opAt 2487 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2487 3233 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2501)
      (stepW_swap s 3233 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2449 := soundW hs (opAt 2488 .POP)
    (blockOfW _ (pcFactW s 2488 3234 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2502)
      (stepW_pop s 3234 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2433.trans (step2434.trans (step2435.trans (step2436.trans (step2437.trans (step2438.trans (step2439.trans (step2440.trans (step2441.trans (step2442.trans (step2443.trans (step2444.trans (step2445.trans (step2446.trans (step2447.trans (step2448.trans (step2449))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy4_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy4_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy4_sym
  have c2433 := blockCostW [opAt 2472 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2472 3215 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2486)
      (stepW_dup s 3215 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2434 := blockCostW [pushAt 2473 1 1] 3
    (blockOfW _ (pcFactW s 2473 3216 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2487)
      (stepW_push s 3216 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2435 := blockCostW [opAt 2474 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2474 3218 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2488)
      (stepW_dup s 3218 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2436 := blockCostW [pushAt 2475 1 3] 3
    (blockOfW _ (pcFactW s 2475 3219 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2489)
      (stepW_push s 3219 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2437 := blockCostW [opAt 2476 .SHR] 3
    (blockOfW _ (pcFactW s 2476 3221 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2490)
      (stepW_shr s 3221 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2438 := blockCostW [opAt 2477 .AND] 3
    (blockOfW _ (pcFactW s 2477 3222 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2491)
      (stepW_and s 3222 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2439 := blockCostW [opAt 2478 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2478 3223 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2492)
      (stepW_dup s 3223 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2440 := blockCostW [opAt 2479 .MUL] 5
    (blockOfW _ (pcFactW s 2479 3224 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2493)
      (stepW_mul s 3224 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2441 := blockCostW [pushAt 2480 1 1] 3
    (blockOfW _ (pcFactW s 2480 3225 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2494)
      (stepW_push s 3225 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2442 := blockCostW [opAt 2481 .ADD] 3
    (blockOfW _ (pcFactW s 2481 3227 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2495)
      (stepW_add s 3227 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2443 := blockCostW [opAt 2482 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2482 3228 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2496)
      (stepW_dup s 3228 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2444 := blockCostW [opAt 2483 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2483 3229 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2497)
      (stepW_dup s 3229 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2445 := blockCostW [opAt 2484 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2484 3230 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2498)
      (stepW_dup s 3230 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2446 := blockCostW [opAt 2485 .MULMOD] 8
    (blockOfW _ (pcFactW s 2485 3231 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2499)
      (stepW_mulmod s 3231 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2447 := blockCostW [opAt 2486 .MULMOD] 8
    (blockOfW _ (pcFactW s 2486 3232 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2500)
      (stepW_mulmod s 3232 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2448 := blockCostW [opAt 2487 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2487 3233 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2501)
      (stepW_swap s 3233 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2449 := blockCostW [opAt 2488 .POP] 2
    (blockOfW _ (pcFactW s 2488 3234 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2502)
      (stepW_pop s 3234 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
