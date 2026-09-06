import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 3 of the unrolled exponent-bit body

The copy handles exponent bit 3 at instruction indices 2469 .. 2485 and bytes
3760 .. 3779.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3760 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3780 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2416 := soundW hs (opAt 2469 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2469 3760 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3760 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2417 := soundW hs (pushAt 2470 1 1)
    (blockOfW _ (pcFactW s 2470 3761 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3761 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2418 := soundW hs (opAt 2471 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2471 3763 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3763 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2419 := soundW hs (pushAt 2472 1 4)
    (blockOfW _ (pcFactW s 2472 3764 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3764 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2420 := soundW hs (opAt 2473 .SHR)
    (blockOfW _ (pcFactW s 2473 3766 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3766 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2421 := soundW hs (opAt 2474 .AND)
    (blockOfW _ (pcFactW s 2474 3767 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3767 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2422 := soundW hs (opAt 2475 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2475 3768 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3768 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2423 := soundW hs (opAt 2476 .MUL)
    (blockOfW _ (pcFactW s 2476 3769 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3769 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2424 := soundW hs (pushAt 2477 1 1)
    (blockOfW _ (pcFactW s 2477 3770 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3770 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2425 := soundW hs (opAt 2478 .ADD)
    (blockOfW _ (pcFactW s 2478 3772 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3772 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2426 := soundW hs (opAt 2479 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2479 3773 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3773 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2427 := soundW hs (opAt 2480 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2480 3774 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3774 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2428 := soundW hs (opAt 2481 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2481 3775 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3775 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2429 := soundW hs (opAt 2482 .MULMOD)
    (blockOfW _ (pcFactW s 2482 3776 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3776 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2430 := soundW hs (opAt 2483 .MULMOD)
    (blockOfW _ (pcFactW s 2483 3777 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3777 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2431 := soundW hs (opAt 2484 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2484 3778 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3778 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2432 := soundW hs (opAt 2485 .POP)
    (blockOfW _ (pcFactW s 2485 3779 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3779 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2416.trans (step2417.trans (step2418.trans (step2419.trans (step2420.trans (step2421.trans (step2422.trans (step2423.trans (step2424.trans (step2425.trans (step2426.trans (step2427.trans (step2428.trans (step2429.trans (step2430.trans (step2431.trans (step2432))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy3_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy3_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy3_sym
  have c2416 := blockCostW [opAt 2469 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2469 3760 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2469)
      (stepW_dup s 3760 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2417 := blockCostW [pushAt 2470 1 1] 3
    (blockOfW _ (pcFactW s 2470 3761 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2470)
      (stepW_push s 3761 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2418 := blockCostW [opAt 2471 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2471 3763 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2471)
      (stepW_dup s 3763 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2419 := blockCostW [pushAt 2472 1 4] 3
    (blockOfW _ (pcFactW s 2472 3764 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2472)
      (stepW_push s 3764 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2420 := blockCostW [opAt 2473 .SHR] 3
    (blockOfW _ (pcFactW s 2473 3766 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2473)
      (stepW_shr s 3766 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2421 := blockCostW [opAt 2474 .AND] 3
    (blockOfW _ (pcFactW s 2474 3767 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2474)
      (stepW_and s 3767 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2422 := blockCostW [opAt 2475 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2475 3768 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2475)
      (stepW_dup s 3768 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2423 := blockCostW [opAt 2476 .MUL] 5
    (blockOfW _ (pcFactW s 2476 3769 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2476)
      (stepW_mul s 3769 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2424 := blockCostW [pushAt 2477 1 1] 3
    (blockOfW _ (pcFactW s 2477 3770 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2477)
      (stepW_push s 3770 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2425 := blockCostW [opAt 2478 .ADD] 3
    (blockOfW _ (pcFactW s 2478 3772 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_add s 3772 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2426 := blockCostW [opAt 2479 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2479 3773 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_dup s 3773 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2427 := blockCostW [opAt 2480 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2480 3774 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_dup s 3774 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2428 := blockCostW [opAt 2481 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2481 3775 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2481)
      (stepW_dup s 3775 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2429 := blockCostW [opAt 2482 .MULMOD] 8
    (blockOfW _ (pcFactW s 2482 3776 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2482)
      (stepW_mulmod s 3776 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2430 := blockCostW [opAt 2483 .MULMOD] 8
    (blockOfW _ (pcFactW s 2483 3777 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2483)
      (stepW_mulmod s 3777 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2431 := blockCostW [opAt 2484 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2484 3778 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2484)
      (stepW_swap s 3778 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2432 := blockCostW [opAt 2485 .POP] 2
    (blockOfW _ (pcFactW s 2485 3779 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2485)
      (stepW_pop s 3779 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
