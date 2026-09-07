import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 4 of the unrolled exponent-bit body

The copy handles exponent bit 4 at instruction indices 2511 .. 2527 and bytes
3809 .. 3828.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3809 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3829 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2433 := soundW hs (opAt 2511 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2511 3809 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2511)
      (stepW_dup s 3809 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2434 := soundW hs (pushAt 2512 1 1)
    (blockOfW _ (pcFactW s 2512 3810 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2512)
      (stepW_push s 3810 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2435 := soundW hs (opAt 2513 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2513 3812 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2513)
      (stepW_dup s 3812 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2436 := soundW hs (pushAt 2514 1 3)
    (blockOfW _ (pcFactW s 2514 3813 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2514)
      (stepW_push s 3813 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2437 := soundW hs (opAt 2515 .SHR)
    (blockOfW _ (pcFactW s 2515 3815 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2515)
      (stepW_shr s 3815 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2438 := soundW hs (opAt 2516 .AND)
    (blockOfW _ (pcFactW s 2516 3816 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2516)
      (stepW_and s 3816 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2439 := soundW hs (opAt 2517 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2517 3817 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2517)
      (stepW_dup s 3817 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2440 := soundW hs (opAt 2518 .MUL)
    (blockOfW _ (pcFactW s 2518 3818 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2518)
      (stepW_mul s 3818 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2441 := soundW hs (pushAt 2519 1 1)
    (blockOfW _ (pcFactW s 2519 3819 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2519)
      (stepW_push s 3819 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2442 := soundW hs (opAt 2520 .ADD)
    (blockOfW _ (pcFactW s 2520 3821 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_add s 3821 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2443 := soundW hs (opAt 2521 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2521 3822 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_dup s 3822 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2444 := soundW hs (opAt 2522 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2522 3823 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3823 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2445 := soundW hs (opAt 2523 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2523 3824 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_dup s 3824 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2446 := soundW hs (opAt 2524 .MULMOD)
    (blockOfW _ (pcFactW s 2524 3825 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_mulmod s 3825 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2447 := soundW hs (opAt 2525 .MULMOD)
    (blockOfW _ (pcFactW s 2525 3826 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_mulmod s 3826 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2448 := soundW hs (opAt 2526 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2526 3827 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_swap s 3827 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2449 := soundW hs (opAt 2527 .POP)
    (blockOfW _ (pcFactW s 2527 3828 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2527)
      (stepW_pop s 3828 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2433.trans (step2434.trans (step2435.trans (step2436.trans (step2437.trans (step2438.trans (step2439.trans (step2440.trans (step2441.trans (step2442.trans (step2443.trans (step2444.trans (step2445.trans (step2446.trans (step2447.trans (step2448.trans (step2449))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy4_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy4_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy4_sym
  have c2433 := blockCostW [opAt 2511 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2511 3809 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2511)
      (stepW_dup s 3809 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2434 := blockCostW [pushAt 2512 1 1] 3
    (blockOfW _ (pcFactW s 2512 3810 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2512)
      (stepW_push s 3810 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2435 := blockCostW [opAt 2513 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2513 3812 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2513)
      (stepW_dup s 3812 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2436 := blockCostW [pushAt 2514 1 3] 3
    (blockOfW _ (pcFactW s 2514 3813 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2514)
      (stepW_push s 3813 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2437 := blockCostW [opAt 2515 .SHR] 3
    (blockOfW _ (pcFactW s 2515 3815 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2515)
      (stepW_shr s 3815 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2438 := blockCostW [opAt 2516 .AND] 3
    (blockOfW _ (pcFactW s 2516 3816 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2516)
      (stepW_and s 3816 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2439 := blockCostW [opAt 2517 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2517 3817 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2517)
      (stepW_dup s 3817 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2440 := blockCostW [opAt 2518 .MUL] 5
    (blockOfW _ (pcFactW s 2518 3818 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2518)
      (stepW_mul s 3818 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2441 := blockCostW [pushAt 2519 1 1] 3
    (blockOfW _ (pcFactW s 2519 3819 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2519)
      (stepW_push s 3819 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2442 := blockCostW [opAt 2520 .ADD] 3
    (blockOfW _ (pcFactW s 2520 3821 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2520)
      (stepW_add s 3821 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2443 := blockCostW [opAt 2521 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2521 3822 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2521)
      (stepW_dup s 3822 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2444 := blockCostW [opAt 2522 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2522 3823 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2522)
      (stepW_dup s 3823 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2445 := blockCostW [opAt 2523 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2523 3824 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2523)
      (stepW_dup s 3824 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2446 := blockCostW [opAt 2524 .MULMOD] 8
    (blockOfW _ (pcFactW s 2524 3825 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2524)
      (stepW_mulmod s 3825 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2447 := blockCostW [opAt 2525 .MULMOD] 8
    (blockOfW _ (pcFactW s 2525 3826 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2525)
      (stepW_mulmod s 3826 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2448 := blockCostW [opAt 2526 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2526 3827 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2526)
      (stepW_swap s 3827 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2449 := blockCostW [opAt 2527 .POP] 2
    (blockOfW _ (pcFactW s 2527 3828 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2527)
      (stepW_pop s 3828 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
