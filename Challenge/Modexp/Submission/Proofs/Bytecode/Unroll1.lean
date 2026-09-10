import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 1 of the unrolled exponent-bit body

This copy handles exponent bit 1, from PC 3243 to PC 3263. Its 17 retained instructions are taken one at a time.
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
    GasSteps (stW s 3243 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3263 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2382 := soundW hs (opAt 2466 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2466 3243 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3243 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2383 := soundW hs (pushAt 2467 1 1)
    (blockOfW _ (pcFactW s 2467 3244 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3244 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2384 := soundW hs (opAt 2468 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2468 3246 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_dup s 3246 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2385 := soundW hs (pushAt 2469 1 6)
    (blockOfW _ (pcFactW s 2469 3247 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_push s 3247 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2386 := soundW hs (opAt 2470 .SHR)
    (blockOfW _ (pcFactW s 2470 3249 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_shr s 3249 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2387 := soundW hs (opAt 2471 .AND)
    (blockOfW _ (pcFactW s 2471 3250 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_and s 3250 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2388 := soundW hs (opAt 2472 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2472 3251 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3251 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2389 := soundW hs (opAt 2473 .MUL)
    (blockOfW _ (pcFactW s 2473 3252 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_mul s 3252 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2390 := soundW hs (pushAt 2474 1 1)
    (blockOfW _ (pcFactW s 2474 3253 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_push s 3253 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2391 := soundW hs (opAt 2475 .ADD)
    (blockOfW _ (pcFactW s 2475 3255 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_add s 3255 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2392 := soundW hs (opAt 2476 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2476 3256 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3256 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2393 := soundW hs (opAt 2477 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2477 3257 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_dup s 3257 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2394 := soundW hs (opAt 2478 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2478 3258 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_dup s 3258 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2395 := soundW hs (opAt 2479 .MULMOD)
    (blockOfW _ (pcFactW s 2479 3259 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_mulmod s 3259 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2396 := soundW hs (opAt 2480 .MULMOD)
    (blockOfW _ (pcFactW s 2480 3260 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2449)
      (stepW_mulmod s 3260 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2397 := soundW hs (opAt 2481 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2481 3261 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2450)
      (stepW_swap s 3261 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2398 := soundW hs (opAt 2482 .POP)
    (blockOfW _ (pcFactW s 2482 3262 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2451)
      (stepW_pop s 3262 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2382.trans (step2383.trans (step2384.trans (step2385.trans (step2386.trans (step2387.trans (step2388.trans (step2389.trans (step2390.trans (step2391.trans (step2392.trans (step2393.trans (step2394.trans (step2395.trans (step2396.trans (step2397.trans (step2398))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy1_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy1_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy1_sym
  have c2382 := blockCostW [opAt 2466 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2466 3243 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3243 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2383 := blockCostW [pushAt 2467 1 1] 3
    (blockOfW _ (pcFactW s 2467 3244 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3244 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2384 := blockCostW [opAt 2468 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2468 3246 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_dup s 3246 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2385 := blockCostW [pushAt 2469 1 6] 3
    (blockOfW _ (pcFactW s 2469 3247 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_push s 3247 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2386 := blockCostW [opAt 2470 .SHR] 3
    (blockOfW _ (pcFactW s 2470 3249 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_shr s 3249 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2387 := blockCostW [opAt 2471 .AND] 3
    (blockOfW _ (pcFactW s 2471 3250 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_and s 3250 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2388 := blockCostW [opAt 2472 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2472 3251 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3251 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2389 := blockCostW [opAt 2473 .MUL] 5
    (blockOfW _ (pcFactW s 2473 3252 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_mul s 3252 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2390 := blockCostW [pushAt 2474 1 1] 3
    (blockOfW _ (pcFactW s 2474 3253 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_push s 3253 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2391 := blockCostW [opAt 2475 .ADD] 3
    (blockOfW _ (pcFactW s 2475 3255 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_add s 3255 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2392 := blockCostW [opAt 2476 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2476 3256 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3256 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2393 := blockCostW [opAt 2477 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2477 3257 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_dup s 3257 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2394 := blockCostW [opAt 2478 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2478 3258 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_dup s 3258 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2395 := blockCostW [opAt 2479 .MULMOD] 8
    (blockOfW _ (pcFactW s 2479 3259 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_mulmod s 3259 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2396 := blockCostW [opAt 2480 .MULMOD] 8
    (blockOfW _ (pcFactW s 2480 3260 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2449)
      (stepW_mulmod s 3260 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2397 := blockCostW [opAt 2481 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2481 3261 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2450)
      (stepW_swap s 3261 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2398 := blockCostW [opAt 2482 .POP] 2
    (blockOfW _ (pcFactW s 2482 3262 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2451)
      (stepW_pop s 3262 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
