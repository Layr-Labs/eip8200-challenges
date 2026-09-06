import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 7 of the unrolled exponent-bit body

The copy handles exponent bit 7 at instruction indices 1969 .. 1985 and bytes
3172 .. 3191.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 7, with every stack slot left symbolic. -/
def gasSteps_bitCopy7_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3172 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3192 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step1969 := soundW hs (opAt 1969 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 1969 3172 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1969)
      (stepW_dup s 3172 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1970 := soundW hs (pushAt 1970 1 1)
    (blockOfW _ (pcFactW s 1970 3173 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1970)
      (stepW_push s 3173 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1971 := soundW hs (opAt 1971 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 1971 3175 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1971)
      (stepW_dup s 3175 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step1972 := soundW hs (pushAt 1972 1 0)
    (blockOfW _ (pcFactW s 1972 3176 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1972)
      (stepW_push s 3176 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1973 := soundW hs (opAt 1973 .SHR)
    (blockOfW _ (pcFactW s 1973 3178 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1973)
      (stepW_shr s 3178 ((0 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1974 := soundW hs (opAt 1974 .AND)
    (blockOfW _ (pcFactW s 1974 3179 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1974)
      (stepW_and s 3179 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1975 := soundW hs (opAt 1975 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 1975 3180 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1975)
      (stepW_dup s 3180 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step1976 := soundW hs (opAt 1976 .MUL)
    (blockOfW _ (pcFactW s 1976 3181 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1976)
      (stepW_mul s 3181 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1977 := soundW hs (pushAt 1977 1 1)
    (blockOfW _ (pcFactW s 1977 3182 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1977)
      (stepW_push s 3182 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1978 := soundW hs (opAt 1978 .ADD)
    (blockOfW _ (pcFactW s 1978 3184 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1978)
      (stepW_add s 3184 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1979 := soundW hs (opAt 1979 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 1979 3185 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1979)
      (stepW_dup s 3185 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1980 := soundW hs (opAt 1980 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 1980 3186 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1980)
      (stepW_dup s 3186 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1981 := soundW hs (opAt 1981 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 1981 3187 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1981)
      (stepW_dup s 3187 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1982 := soundW hs (opAt 1982 .MULMOD)
    (blockOfW _ (pcFactW s 1982 3188 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1982)
      (stepW_mulmod s 3188 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1983 := soundW hs (opAt 1983 .MULMOD)
    (blockOfW _ (pcFactW s 1983 3189 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1983)
      (stepW_mulmod s 3189 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1984 := soundW hs (opAt 1984 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 1984 3190 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1984)
      (stepW_swap s 3190 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step1985 := soundW hs (opAt 1985 .POP)
    (blockOfW _ (pcFactW s 1985 3191 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1985)
      (stepW_pop s 3191 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step1969.trans (step1970.trans (step1971.trans (step1972.trans (step1973.trans (step1974.trans (step1975.trans (step1976.trans (step1977.trans (step1978.trans (step1979.trans (step1980.trans (step1981.trans (step1982.trans (step1983.trans (step1984.trans (step1985))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy7_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy7_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy7_sym
  have c1969 := blockCostW [opAt 1969 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1969 3172 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1969)
      (stepW_dup s 3172 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1970 := blockCostW [pushAt 1970 1 1] 3
    (blockOfW _ (pcFactW s 1970 3173 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1970)
      (stepW_push s 3173 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1971 := blockCostW [opAt 1971 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1971 3175 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1971)
      (stepW_dup s 3175 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1972 := blockCostW [pushAt 1972 1 0] 3
    (blockOfW _ (pcFactW s 1972 3176 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1972)
      (stepW_push s 3176 1 (0 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1973 := blockCostW [opAt 1973 .SHR] 3
    (blockOfW _ (pcFactW s 1973 3178 ([(0 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1973)
      (stepW_shr s 3178 ((0 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1974 := blockCostW [opAt 1974 .AND] 3
    (blockOfW _ (pcFactW s 1974 3179 ([(UInt256.shiftRight byte (0 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1974)
      (stepW_and s 3179 ((UInt256.shiftRight byte (0 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1975 := blockCostW [opAt 1975 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1975 3180 ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1975)
      (stepW_dup s 3180 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1976 := blockCostW [opAt 1976 .MUL] 5
    (blockOfW _ (pcFactW s 1976 3181 ([Bm1, (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1976)
      (stepW_mul s 3181 (Bm1) ((UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1977 := blockCostW [pushAt 1977 1 1] 3
    (blockOfW _ (pcFactW s 1977 3182 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1977)
      (stepW_push s 3182 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1978 := blockCostW [opAt 1978 .ADD] 3
    (blockOfW _ (pcFactW s 1978 3184 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1978)
      (stepW_add s 3184 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1979 := blockCostW [opAt 1979 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1979 3185 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1979)
      (stepW_dup s 3185 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1980 := blockCostW [opAt 1980 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1980 3186 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1980)
      (stepW_dup s 3186 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1981 := blockCostW [opAt 1981 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1981 3187 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1981)
      (stepW_dup s 3187 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1982 := blockCostW [opAt 1982 .MULMOD] 8
    (blockOfW _ (pcFactW s 1982 3188 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1982)
      (stepW_mulmod s 3188 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1983 := blockCostW [opAt 1983 .MULMOD] 8
    (blockOfW _ (pcFactW s 1983 3189 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1983)
      (stepW_mulmod s 3189 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1984 := blockCostW [opAt 1984 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1984 3190 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1984)
      (stepW_swap s 3190 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1985 := blockCostW [opAt 1985 .POP] 2
    (blockOfW _ (pcFactW s 1985 3191 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1985)
      (stepW_pop s 3191 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (0 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
