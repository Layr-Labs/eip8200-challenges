import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 4 of the unrolled exponent-bit body

The copy handles exponent bit 4 at instruction indices 2433 .. 2449 and bytes
3691 .. 3710.  Its seventeen instructions are taken one at a time.
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
    GasSteps (stW s 3691 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3711 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step2433 := soundW hs (opAt 2433 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 2433 3691 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_dup s 3691 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2434 := soundW hs (pushAt 2434 1 1)
    (blockOfW _ (pcFactW s 2434 3692 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2434)
      (stepW_push s 3692 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2435 := soundW hs (opAt 2435 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 2435 3694 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3694 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step2436 := soundW hs (pushAt 2436 1 3)
    (blockOfW _ (pcFactW s 2436 3695 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3695 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2437 := soundW hs (opAt 2437 .SHR)
    (blockOfW _ (pcFactW s 2437 3697 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_shr s 3697 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2438 := soundW hs (opAt 2438 .AND)
    (blockOfW _ (pcFactW s 2438 3698 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_and s 3698 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2439 := soundW hs (opAt 2439 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 2439 3699 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_dup s 3699 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step2440 := soundW hs (opAt 2440 .MUL)
    (blockOfW _ (pcFactW s 2440 3700 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_mul s 3700 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2441 := soundW hs (pushAt 2441 1 1)
    (blockOfW _ (pcFactW s 2441 3701 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_push s 3701 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2442 := soundW hs (opAt 2442 .ADD)
    (blockOfW _ (pcFactW s 2442 3703 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_add s 3703 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2443 := soundW hs (opAt 2443 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 2443 3704 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_dup s 3704 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step2444 := soundW hs (opAt 2444 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 2444 3705 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_dup s 3705 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2445 := soundW hs (opAt 2445 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 2445 3706 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3706 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step2446 := soundW hs (opAt 2446 .MULMOD)
    (blockOfW _ (pcFactW s 2446 3707 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_mulmod s 3707 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2447 := soundW hs (opAt 2447 .MULMOD)
    (blockOfW _ (pcFactW s 2447 3708 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_mulmod s 3708 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2448 := soundW hs (opAt 2448 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 2448 3709 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_swap s 3709 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step2449 := soundW hs (opAt 2449 .POP)
    (blockOfW _ (pcFactW s 2449 3710 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2449)
      (stepW_pop s 3710 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2433.trans (step2434.trans (step2435.trans (step2436.trans (step2437.trans (step2438.trans (step2439.trans (step2440.trans (step2441.trans (step2442.trans (step2443.trans (step2444.trans (step2445.trans (step2446.trans (step2447.trans (step2448.trans (step2449))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy4_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy4_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy4_sym
  have c2433 := blockCostW [opAt 2433 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2433 3691 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_dup s 3691 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2434 := blockCostW [pushAt 2434 1 1] 3
    (blockOfW _ (pcFactW s 2434 3692 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2434)
      (stepW_push s 3692 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2435 := blockCostW [opAt 2435 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2435 3694 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2435)
      (stepW_dup s 3694 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2436 := blockCostW [pushAt 2436 1 3] 3
    (blockOfW _ (pcFactW s 2436 3695 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2436)
      (stepW_push s 3695 1 (3 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2437 := blockCostW [opAt 2437 .SHR] 3
    (blockOfW _ (pcFactW s 2437 3697 ([(3 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2437)
      (stepW_shr s 3697 ((3 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2438 := blockCostW [opAt 2438 .AND] 3
    (blockOfW _ (pcFactW s 2438 3698 ([(UInt256.shiftRight byte (3 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2438)
      (stepW_and s 3698 ((UInt256.shiftRight byte (3 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2439 := blockCostW [opAt 2439 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2439 3699 ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_dup s 3699 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2440 := blockCostW [opAt 2440 .MUL] 5
    (blockOfW _ (pcFactW s 2440 3700 ([Bm1, (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_mul s 3700 (Bm1) ((UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2441 := blockCostW [pushAt 2441 1 1] 3
    (blockOfW _ (pcFactW s 2441 3701 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_push s 3701 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2442 := blockCostW [opAt 2442 .ADD] 3
    (blockOfW _ (pcFactW s 2442 3703 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_add s 3703 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2443 := blockCostW [opAt 2443 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2443 3704 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2443)
      (stepW_dup s 3704 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2444 := blockCostW [opAt 2444 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2444 3705 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2444)
      (stepW_dup s 3705 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2445 := blockCostW [opAt 2445 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2445 3706 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2445)
      (stepW_dup s 3706 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2446 := blockCostW [opAt 2446 .MULMOD] 8
    (blockOfW _ (pcFactW s 2446 3707 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2446)
      (stepW_mulmod s 3707 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2447 := blockCostW [opAt 2447 .MULMOD] 8
    (blockOfW _ (pcFactW s 2447 3708 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2447)
      (stepW_mulmod s 3708 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2448 := blockCostW [opAt 2448 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2448 3709 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2448)
      (stepW_swap s 3709 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2449 := blockCostW [opAt 2449 .POP] 2
    (blockOfW _ (pcFactW s 2449 3710 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc2449)
      (stepW_pop s 3710 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (3 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
