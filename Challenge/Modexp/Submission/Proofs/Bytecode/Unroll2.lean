import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 2 of the unrolled exponent-bit body

The copy handles exponent bit 2 at instruction indices 2469 .. 2485 and bytes
3772 .. 3791.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 2, with every stack slot left symbolic. -/
def gasSteps_bitCopy2_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3772 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3792 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2469 := soundW hs (opAt 2469 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2469 3772 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3772 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2470 := soundW hs (pushAt 2470 1 1)
    (blockOfW _ (pcFactW s 2470 3773 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3773 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2471 := soundW hs (opAt 2471 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2471 3775 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3775 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2472 := soundW hs (pushAt 2472 1 5)
    (blockOfW _ (pcFactW s 2472 3776 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3776 1 (5 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2473 := soundW hs (opAt 2473 .SHR)
    (blockOfW _ (pcFactW s 2473 3778 ([(5 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3778 ((5 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2474 := soundW hs (opAt 2474 .AND)
    (blockOfW _ (pcFactW s 2474 3779 ([(UInt256.shiftRight byte (5 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3779 ((UInt256.shiftRight byte (5 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2475 := soundW hs (opAt 2475 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2475 3780 ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3780 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2476 := soundW hs (opAt 2476 .MUL)
    (blockOfW _ (pcFactW s 2476 3781 ([Bm1, (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3781 (Bm1) ((UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2477 := soundW hs (pushAt 2477 1 1)
    (blockOfW _ (pcFactW s 2477 3782 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3782 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2478 := soundW hs (opAt 2478 .ADD)
    (blockOfW _ (pcFactW s 2478 3784 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3784 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2479 := soundW hs (opAt 2479 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2479 3785 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3785 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2480 := soundW hs (opAt 2480 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2480 3786 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3786 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2481 := soundW hs (opAt 2481 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2481 3787 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3787 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2482 := soundW hs (opAt 2482 .MULMOD)
    (blockOfW _ (pcFactW s 2482 3788 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3788 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2483 := soundW hs (opAt 2483 .MULMOD)
    (blockOfW _ (pcFactW s 2483 3789 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3789 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2484 := soundW hs (opAt 2484 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2484 3790 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3790 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2485 := soundW hs (opAt 2485 .POP)
    (blockOfW _ (pcFactW s 2485 3791 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3791 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2469.trans (step2470.trans (step2471.trans (step2472.trans (step2473.trans (step2474.trans (step2475.trans (step2476.trans (step2477.trans (step2478.trans (step2479.trans (step2480.trans (step2481.trans (step2482.trans (step2483.trans (step2484.trans (step2485))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy2_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy2_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy2_sym
  have c2469 := blockCostW [opAt 2469 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2469 3772 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3772 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2470 := blockCostW [pushAt 2470 1 1] 3
    (blockOfW _ (pcFactW s 2470 3773 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3773 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2471 := blockCostW [opAt 2471 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2471 3775 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3775 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2472 := blockCostW [pushAt 2472 1 5] 3
    (blockOfW _ (pcFactW s 2472 3776 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3776 1 (5 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2473 := blockCostW [opAt 2473 .SHR] 3
    (blockOfW _ (pcFactW s 2473 3778 ([(5 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3778 ((5 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2474 := blockCostW [opAt 2474 .AND] 3
    (blockOfW _ (pcFactW s 2474 3779 ([(UInt256.shiftRight byte (5 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3779 ((UInt256.shiftRight byte (5 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2475 := blockCostW [opAt 2475 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2475 3780 ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3780 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2476 := blockCostW [opAt 2476 .MUL] 5
    (blockOfW _ (pcFactW s 2476 3781 ([Bm1, (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3781 (Bm1) ((UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2477 := blockCostW [pushAt 2477 1 1] 3
    (blockOfW _ (pcFactW s 2477 3782 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3782 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2478 := blockCostW [opAt 2478 .ADD] 3
    (blockOfW _ (pcFactW s 2478 3784 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3784 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2479 := blockCostW [opAt 2479 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2479 3785 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3785 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2480 := blockCostW [opAt 2480 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2480 3786 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3786 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2481 := blockCostW [opAt 2481 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2481 3787 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3787 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2482 := blockCostW [opAt 2482 .MULMOD] 8
    (blockOfW _ (pcFactW s 2482 3788 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3788 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2483 := blockCostW [opAt 2483 .MULMOD] 8
    (blockOfW _ (pcFactW s 2483 3789 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3789 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2484 := blockCostW [opAt 2484 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2484 3790 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3790 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2485 := blockCostW [opAt 2485 .POP] 2
    (blockOfW _ (pcFactW s 2485 3791 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3791 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (5 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2
