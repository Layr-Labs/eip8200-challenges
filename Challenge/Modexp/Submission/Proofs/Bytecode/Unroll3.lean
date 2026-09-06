import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 3 of the unrolled exponent-bit body

The copy handles exponent bit 3 at instruction indices 2416 .. 2432 and bytes
3671 .. 3690.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3671 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3691 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2416 := soundW hs (opAt 2416 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2416 3671 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3671 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2417 := soundW hs (pushAt 2417 1 1)
    (blockOfW _ (pcFactW s 2417 3672 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_push s 3672 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2418 := soundW hs (opAt 2418 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2418 3674 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2418)
      (stepW_dup s 3674 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2419 := soundW hs (pushAt 2419 1 4)
    (blockOfW _ (pcFactW s 2419 3675 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2419)
      (stepW_push s 3675 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2420 := soundW hs (opAt 2420 .SHR)
    (blockOfW _ (pcFactW s 2420 3677 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2420)
      (stepW_shr s 3677 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2421 := soundW hs (opAt 2421 .AND)
    (blockOfW _ (pcFactW s 2421 3678 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2421)
      (stepW_and s 3678 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2422 := soundW hs (opAt 2422 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2422 3679 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2422)
      (stepW_dup s 3679 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2423 := soundW hs (opAt 2423 .MUL)
    (blockOfW _ (pcFactW s 2423 3680 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2423)
      (stepW_mul s 3680 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2424 := soundW hs (pushAt 2424 1 1)
    (blockOfW _ (pcFactW s 2424 3681 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2424)
      (stepW_push s 3681 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2425 := soundW hs (opAt 2425 .ADD)
    (blockOfW _ (pcFactW s 2425 3683 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2425)
      (stepW_add s 3683 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2426 := soundW hs (opAt 2426 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2426 3684 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2426)
      (stepW_dup s 3684 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2427 := soundW hs (opAt 2427 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2427 3685 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2427)
      (stepW_dup s 3685 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2428 := soundW hs (opAt 2428 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2428 3686 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2428)
      (stepW_dup s 3686 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2429 := soundW hs (opAt 2429 .MULMOD)
    (blockOfW _ (pcFactW s 2429 3687 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2429)
      (stepW_mulmod s 3687 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2430 := soundW hs (opAt 2430 .MULMOD)
    (blockOfW _ (pcFactW s 2430 3688 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2430)
      (stepW_mulmod s 3688 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2431 := soundW hs (opAt 2431 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2431 3689 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_swap s 3689 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2432 := soundW hs (opAt 2432 .POP)
    (blockOfW _ (pcFactW s 2432 3690 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2432)
      (stepW_pop s 3690 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2416.trans (step2417.trans (step2418.trans (step2419.trans (step2420.trans (step2421.trans (step2422.trans (step2423.trans (step2424.trans (step2425.trans (step2426.trans (step2427.trans (step2428.trans (step2429.trans (step2430.trans (step2431.trans (step2432))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy3_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy3_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy3_sym
  have c2416 := blockCostW [opAt 2416 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2416 3671 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3671 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2417 := blockCostW [pushAt 2417 1 1] 3
    (blockOfW _ (pcFactW s 2417 3672 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_push s 3672 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2418 := blockCostW [opAt 2418 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2418 3674 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2418)
      (stepW_dup s 3674 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2419 := blockCostW [pushAt 2419 1 4] 3
    (blockOfW _ (pcFactW s 2419 3675 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2419)
      (stepW_push s 3675 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2420 := blockCostW [opAt 2420 .SHR] 3
    (blockOfW _ (pcFactW s 2420 3677 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2420)
      (stepW_shr s 3677 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2421 := blockCostW [opAt 2421 .AND] 3
    (blockOfW _ (pcFactW s 2421 3678 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2421)
      (stepW_and s 3678 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2422 := blockCostW [opAt 2422 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2422 3679 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2422)
      (stepW_dup s 3679 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2423 := blockCostW [opAt 2423 .MUL] 5
    (blockOfW _ (pcFactW s 2423 3680 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2423)
      (stepW_mul s 3680 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2424 := blockCostW [pushAt 2424 1 1] 3
    (blockOfW _ (pcFactW s 2424 3681 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2424)
      (stepW_push s 3681 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2425 := blockCostW [opAt 2425 .ADD] 3
    (blockOfW _ (pcFactW s 2425 3683 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2425)
      (stepW_add s 3683 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2426 := blockCostW [opAt 2426 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2426 3684 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2426)
      (stepW_dup s 3684 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2427 := blockCostW [opAt 2427 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2427 3685 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2427)
      (stepW_dup s 3685 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2428 := blockCostW [opAt 2428 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2428 3686 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2428)
      (stepW_dup s 3686 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2429 := blockCostW [opAt 2429 .MULMOD] 8
    (blockOfW _ (pcFactW s 2429 3687 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2429)
      (stepW_mulmod s 3687 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2430 := blockCostW [opAt 2430 .MULMOD] 8
    (blockOfW _ (pcFactW s 2430 3688 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2430)
      (stepW_mulmod s 3688 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2431 := blockCostW [opAt 2431 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2431 3689 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_swap s 3689 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2432 := blockCostW [opAt 2432 .POP] 2
    (blockOfW _ (pcFactW s 2432 3690 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2432)
      (stepW_pop s 3690 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
