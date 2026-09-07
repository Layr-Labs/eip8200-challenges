import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 1 of the unrolled exponent-bit body

The copy handles exponent bit 1 at instruction indices 2452 .. 2468 and bytes
3752 .. 3771.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3752 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3772 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2452 := soundW hs (opAt 2452 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2452 3752 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2452)
      (stepW_dup s 3752 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2453 := soundW hs (pushAt 2453 1 1)
    (blockOfW _ (pcFactW s 2453 3753 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2453)
      (stepW_push s 3753 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2454 := soundW hs (opAt 2454 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2454 3755 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2454)
      (stepW_dup s 3755 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2455 := soundW hs (pushAt 2455 1 6)
    (blockOfW _ (pcFactW s 2455 3756 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2455)
      (stepW_push s 3756 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2456 := soundW hs (opAt 2456 .SHR)
    (blockOfW _ (pcFactW s 2456 3758 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2456)
      (stepW_shr s 3758 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2457 := soundW hs (opAt 2457 .AND)
    (blockOfW _ (pcFactW s 2457 3759 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2457)
      (stepW_and s 3759 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2458 := soundW hs (opAt 2458 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2458 3760 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2458)
      (stepW_dup s 3760 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2459 := soundW hs (opAt 2459 .MUL)
    (blockOfW _ (pcFactW s 2459 3761 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2459)
      (stepW_mul s 3761 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2460 := soundW hs (pushAt 2460 1 1)
    (blockOfW _ (pcFactW s 2460 3762 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2460)
      (stepW_push s 3762 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2461 := soundW hs (opAt 2461 .ADD)
    (blockOfW _ (pcFactW s 2461 3764 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2461)
      (stepW_add s 3764 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2462 := soundW hs (opAt 2462 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2462 3765 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2462)
      (stepW_dup s 3765 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2463 := soundW hs (opAt 2463 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2463 3766 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2463)
      (stepW_dup s 3766 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2464 := soundW hs (opAt 2464 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2464 3767 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2464)
      (stepW_dup s 3767 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2465 := soundW hs (opAt 2465 .MULMOD)
    (blockOfW _ (pcFactW s 2465 3768 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2465)
      (stepW_mulmod s 3768 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2466 := soundW hs (opAt 2466 .MULMOD)
    (blockOfW _ (pcFactW s 2466 3769 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2466)
      (stepW_mulmod s 3769 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2467 := soundW hs (opAt 2467 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2467 3770 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2467)
      (stepW_swap s 3770 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2468 := soundW hs (opAt 2468 .POP)
    (blockOfW _ (pcFactW s 2468 3771 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2468)
      (stepW_pop s 3771 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2452.trans (step2453.trans (step2454.trans (step2455.trans (step2456.trans (step2457.trans (step2458.trans (step2459.trans (step2460.trans (step2461.trans (step2462.trans (step2463.trans (step2464.trans (step2465.trans (step2466.trans (step2467.trans (step2468))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy1_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy1_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy1_sym
  have c2452 := blockCostW [opAt 2452 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2452 3752 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2452)
      (stepW_dup s 3752 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2453 := blockCostW [pushAt 2453 1 1] 3
    (blockOfW _ (pcFactW s 2453 3753 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2453)
      (stepW_push s 3753 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2454 := blockCostW [opAt 2454 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2454 3755 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2454)
      (stepW_dup s 3755 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2455 := blockCostW [pushAt 2455 1 6] 3
    (blockOfW _ (pcFactW s 2455 3756 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2455)
      (stepW_push s 3756 1 (6 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2456 := blockCostW [opAt 2456 .SHR] 3
    (blockOfW _ (pcFactW s 2456 3758 ([(6 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2456)
      (stepW_shr s 3758 ((6 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2457 := blockCostW [opAt 2457 .AND] 3
    (blockOfW _ (pcFactW s 2457 3759 ([(UInt256.shiftRight byte (6 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2457)
      (stepW_and s 3759 ((UInt256.shiftRight byte (6 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2458 := blockCostW [opAt 2458 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2458 3760 ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2458)
      (stepW_dup s 3760 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2459 := blockCostW [opAt 2459 .MUL] 5
    (blockOfW _ (pcFactW s 2459 3761 ([Bm1, (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2459)
      (stepW_mul s 3761 (Bm1) ((UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2460 := blockCostW [pushAt 2460 1 1] 3
    (blockOfW _ (pcFactW s 2460 3762 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2460)
      (stepW_push s 3762 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2461 := blockCostW [opAt 2461 .ADD] 3
    (blockOfW _ (pcFactW s 2461 3764 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2461)
      (stepW_add s 3764 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2462 := blockCostW [opAt 2462 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2462 3765 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2462)
      (stepW_dup s 3765 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2463 := blockCostW [opAt 2463 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2463 3766 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2463)
      (stepW_dup s 3766 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2464 := blockCostW [opAt 2464 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2464 3767 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2464)
      (stepW_dup s 3767 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2465 := blockCostW [opAt 2465 .MULMOD] 8
    (blockOfW _ (pcFactW s 2465 3768 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2465)
      (stepW_mulmod s 3768 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2466 := blockCostW [opAt 2466 .MULMOD] 8
    (blockOfW _ (pcFactW s 2466 3769 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2466)
      (stepW_mulmod s 3769 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2467 := blockCostW [opAt 2467 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2467 3770 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2467)
      (stepW_swap s 3770 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2468 := blockCostW [opAt 2468 .POP] 2
    (blockOfW _ (pcFactW s 2468 3771 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2468)
      (stepW_pop s 3771 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (6 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
