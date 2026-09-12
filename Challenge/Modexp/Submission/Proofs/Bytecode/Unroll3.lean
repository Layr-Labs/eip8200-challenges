import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000
/-!
# Copy 3 of the unrolled exponent-bit body

This copy handles exponent bit 3, from PC 3283 to PC 3303. Its 17 retained instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 3, with every stack slot left symbolic. -/
def gasSteps_bitCopy3_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3009 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3029 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2416 := soundW hs (opAt 2325 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2329 3009 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3009 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2417 := soundW hs (pushAt 2326 1 1)
    (blockOfW _ (pcFactW s 2330 3010 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3010 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2418 := soundW hs (opAt 2327 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2331 3012 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3012 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2419 := soundW hs (pushAt 2328 1 4)
    (blockOfW _ (pcFactW s 2332 3013 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3013 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2420 := soundW hs (opAt 2329 .SHR)
    (blockOfW _ (pcFactW s 2333 3015 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3015 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2421 := soundW hs (opAt 2330 .AND)
    (blockOfW _ (pcFactW s 2334 3016 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3016 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2422 := soundW hs (opAt 2331 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2335 3017 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3017 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2423 := soundW hs (opAt 2332 .MUL)
    (blockOfW _ (pcFactW s 2336 3018 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3018 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2424 := soundW hs (pushAt 2333 1 1)
    (blockOfW _ (pcFactW s 2337 3019 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3019 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2425 := soundW hs (opAt 2334 .ADD)
    (blockOfW _ (pcFactW s 2338 3021 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3021 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2426 := soundW hs (opAt 2335 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2339 3022 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3022 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2427 := soundW hs (opAt 2336 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2340 3023 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3023 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2428 := soundW hs (opAt 2337 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2341 3024 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3024 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2429 := soundW hs (opAt 2338 .MULMOD)
    (blockOfW _ (pcFactW s 2342 3025 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3025 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2430 := soundW hs (opAt 2339 .MULMOD)
    (blockOfW _ (pcFactW s 2343 3026 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3026 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2431 := soundW hs (opAt 2340 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2344 3027 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3027 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2432 := soundW hs (opAt 2341 .POP)
    (blockOfW _ (pcFactW s 2345 3028 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3028 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2416.trans (step2417.trans (step2418.trans (step2419.trans (step2420.trans (step2421.trans (step2422.trans (step2423.trans (step2424.trans (step2425.trans (step2426.trans (step2427.trans (step2428.trans (step2429.trans (step2430.trans (step2431.trans (step2432))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy3_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy3_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy3_sym
  have c2416 := blockCostW [opAt 2325 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2329 3009 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3009 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2417 := blockCostW [pushAt 2326 1 1] 3
    (blockOfW _ (pcFactW s 2330 3010 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3010 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2418 := blockCostW [opAt 2327 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2331 3012 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3012 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2419 := blockCostW [pushAt 2328 1 4] 3
    (blockOfW _ (pcFactW s 2332 3013 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3013 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2420 := blockCostW [opAt 2329 .SHR] 3
    (blockOfW _ (pcFactW s 2333 3015 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3015 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2421 := blockCostW [opAt 2330 .AND] 3
    (blockOfW _ (pcFactW s 2334 3016 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3016 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2422 := blockCostW [opAt 2331 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2335 3017 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3017 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2423 := blockCostW [opAt 2332 .MUL] 5
    (blockOfW _ (pcFactW s 2336 3018 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3018 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2424 := blockCostW [pushAt 2333 1 1] 3
    (blockOfW _ (pcFactW s 2337 3019 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3019 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2425 := blockCostW [opAt 2334 .ADD] 3
    (blockOfW _ (pcFactW s 2338 3021 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3021 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2426 := blockCostW [opAt 2335 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2339 3022 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3022 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2427 := blockCostW [opAt 2336 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2340 3023 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3023 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2428 := blockCostW [opAt 2337 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2341 3024 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3024 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2429 := blockCostW [opAt 2338 .MULMOD] 8
    (blockOfW _ (pcFactW s 2342 3025 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3025 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2430 := blockCostW [opAt 2339 .MULMOD] 8
    (blockOfW _ (pcFactW s 2343 3026 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3026 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2431 := blockCostW [opAt 2340 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2344 3027 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3027 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2432 := blockCostW [opAt 2341 .POP] 2
    (blockOfW _ (pcFactW s 2345 3028 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3028 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
