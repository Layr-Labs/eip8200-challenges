import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 3 of the unrolled exponent-bit body

The copy handles exponent bit 3 at instruction indices 2393 .. 2409 and bytes
3636 .. 3655.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3636 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3656 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2393 := soundW hs (opAt 2393 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2393 3636 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2393)
      (stepW_dup s 3636 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2394 := soundW hs (pushAt 2394 1 1)
    (blockOfW _ (pcFactW s 2394 3637 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2394)
      (stepW_push s 3637 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2395 := soundW hs (opAt 2395 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2395 3639 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2395)
      (stepW_dup s 3639 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2396 := soundW hs (pushAt 2396 1 4)
    (blockOfW _ (pcFactW s 2396 3640 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2396)
      (stepW_push s 3640 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2397 := soundW hs (opAt 2397 .SHR)
    (blockOfW _ (pcFactW s 2397 3642 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2397)
      (stepW_shr s 3642 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2398 := soundW hs (opAt 2398 .AND)
    (blockOfW _ (pcFactW s 2398 3643 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2398)
      (stepW_and s 3643 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2399 := soundW hs (opAt 2399 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2399 3644 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2399)
      (stepW_dup s 3644 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2400 := soundW hs (opAt 2400 .MUL)
    (blockOfW _ (pcFactW s 2400 3645 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2400)
      (stepW_mul s 3645 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2401 := soundW hs (pushAt 2401 1 1)
    (blockOfW _ (pcFactW s 2401 3646 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2401)
      (stepW_push s 3646 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2402 := soundW hs (opAt 2402 .ADD)
    (blockOfW _ (pcFactW s 2402 3648 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2402)
      (stepW_add s 3648 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2403 := soundW hs (opAt 2403 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2403 3649 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2403)
      (stepW_dup s 3649 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2404 := soundW hs (opAt 2404 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2404 3650 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2404)
      (stepW_dup s 3650 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2405 := soundW hs (opAt 2405 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2405 3651 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2405)
      (stepW_dup s 3651 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2406 := soundW hs (opAt 2406 .MULMOD)
    (blockOfW _ (pcFactW s 2406 3652 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2406)
      (stepW_mulmod s 3652 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2407 := soundW hs (opAt 2407 .MULMOD)
    (blockOfW _ (pcFactW s 2407 3653 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2407)
      (stepW_mulmod s 3653 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2408 := soundW hs (opAt 2408 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2408 3654 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2408)
      (stepW_swap s 3654 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2409 := soundW hs (opAt 2409 .POP)
    (blockOfW _ (pcFactW s 2409 3655 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2409)
      (stepW_pop s 3655 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2393.trans (step2394.trans (step2395.trans (step2396.trans (step2397.trans (step2398.trans (step2399.trans (step2400.trans (step2401.trans (step2402.trans (step2403.trans (step2404.trans (step2405.trans (step2406.trans (step2407.trans (step2408.trans (step2409))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy3_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy3_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy3_sym
  have c2393 := blockCostW [opAt 2393 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2393 3636 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2393)
      (stepW_dup s 3636 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2394 := blockCostW [pushAt 2394 1 1] 3
    (blockOfW _ (pcFactW s 2394 3637 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2394)
      (stepW_push s 3637 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2395 := blockCostW [opAt 2395 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2395 3639 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2395)
      (stepW_dup s 3639 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2396 := blockCostW [pushAt 2396 1 4] 3
    (blockOfW _ (pcFactW s 2396 3640 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2396)
      (stepW_push s 3640 1 (4 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2397 := blockCostW [opAt 2397 .SHR] 3
    (blockOfW _ (pcFactW s 2397 3642 ([(4 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2397)
      (stepW_shr s 3642 ((4 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2398 := blockCostW [opAt 2398 .AND] 3
    (blockOfW _ (pcFactW s 2398 3643 ([(UInt256.shiftRight byte (4 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2398)
      (stepW_and s 3643 ((UInt256.shiftRight byte (4 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2399 := blockCostW [opAt 2399 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2399 3644 ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2399)
      (stepW_dup s 3644 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2400 := blockCostW [opAt 2400 .MUL] 5
    (blockOfW _ (pcFactW s 2400 3645 ([Bm1, (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2400)
      (stepW_mul s 3645 (Bm1) ((UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2401 := blockCostW [pushAt 2401 1 1] 3
    (blockOfW _ (pcFactW s 2401 3646 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2401)
      (stepW_push s 3646 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2402 := blockCostW [opAt 2402 .ADD] 3
    (blockOfW _ (pcFactW s 2402 3648 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2402)
      (stepW_add s 3648 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2403 := blockCostW [opAt 2403 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2403 3649 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2403)
      (stepW_dup s 3649 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2404 := blockCostW [opAt 2404 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2404 3650 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2404)
      (stepW_dup s 3650 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2405 := blockCostW [opAt 2405 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2405 3651 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2405)
      (stepW_dup s 3651 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2406 := blockCostW [opAt 2406 .MULMOD] 8
    (blockOfW _ (pcFactW s 2406 3652 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2406)
      (stepW_mulmod s 3652 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2407 := blockCostW [opAt 2407 .MULMOD] 8
    (blockOfW _ (pcFactW s 2407 3653 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2407)
      (stepW_mulmod s 3653 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2408 := blockCostW [opAt 2408 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2408 3654 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2408)
      (stepW_swap s 3654 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2409 := blockCostW [opAt 2409 .POP] 2
    (blockOfW _ (pcFactW s 2409 3655 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2409)
      (stepW_pop s 3655 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (4 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
