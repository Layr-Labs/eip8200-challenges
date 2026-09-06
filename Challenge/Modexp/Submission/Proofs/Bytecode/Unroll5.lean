import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 5 of the unrolled exponent-bit body

The copy handles exponent bit 5 at instruction indices 1935 .. 1951 and bytes
3132 .. 3151.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 5, with every stack slot left symbolic. -/
def gasSteps_bitCopy5_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3132 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3152 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step1935 := soundW hs (opAt 1935 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 1935 3132 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1935)
      (stepW_dup s 3132 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1936 := soundW hs (pushAt 1936 1 1)
    (blockOfW _ (pcFactW s 1936 3133 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1936)
      (stepW_push s 3133 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1937 := soundW hs (opAt 1937 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 1937 3135 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1937)
      (stepW_dup s 3135 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step1938 := soundW hs (pushAt 1938 1 2)
    (blockOfW _ (pcFactW s 1938 3136 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1938)
      (stepW_push s 3136 1 (2 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1939 := soundW hs (opAt 1939 .SHR)
    (blockOfW _ (pcFactW s 1939 3138 ([(2 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1939)
      (stepW_shr s 3138 ((2 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1940 := soundW hs (opAt 1940 .AND)
    (blockOfW _ (pcFactW s 1940 3139 ([(UInt256.shiftRight byte (2 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1940)
      (stepW_and s 3139 ((UInt256.shiftRight byte (2 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1941 := soundW hs (opAt 1941 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 1941 3140 ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1941)
      (stepW_dup s 3140 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step1942 := soundW hs (opAt 1942 .MUL)
    (blockOfW _ (pcFactW s 1942 3141 ([Bm1, (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1942)
      (stepW_mul s 3141 (Bm1) ((UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1943 := soundW hs (pushAt 1943 1 1)
    (blockOfW _ (pcFactW s 1943 3142 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1943)
      (stepW_push s 3142 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1944 := soundW hs (opAt 1944 .ADD)
    (blockOfW _ (pcFactW s 1944 3144 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1944)
      (stepW_add s 3144 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1945 := soundW hs (opAt 1945 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 1945 3145 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1945)
      (stepW_dup s 3145 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1946 := soundW hs (opAt 1946 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 1946 3146 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1946)
      (stepW_dup s 3146 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1947 := soundW hs (opAt 1947 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 1947 3147 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1947)
      (stepW_dup s 3147 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1948 := soundW hs (opAt 1948 .MULMOD)
    (blockOfW _ (pcFactW s 1948 3148 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1948)
      (stepW_mulmod s 3148 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1949 := soundW hs (opAt 1949 .MULMOD)
    (blockOfW _ (pcFactW s 1949 3149 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1949)
      (stepW_mulmod s 3149 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1950 := soundW hs (opAt 1950 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 1950 3150 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1950)
      (stepW_swap s 3150 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step1951 := soundW hs (opAt 1951 .POP)
    (blockOfW _ (pcFactW s 1951 3151 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1951)
      (stepW_pop s 3151 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step1935.trans (step1936.trans (step1937.trans (step1938.trans (step1939.trans (step1940.trans (step1941.trans (step1942.trans (step1943.trans (step1944.trans (step1945.trans (step1946.trans (step1947.trans (step1948.trans (step1949.trans (step1950.trans (step1951))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy5_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy5_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy5_sym
  have c1935 := blockCostW [opAt 1935 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1935 3132 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1935)
      (stepW_dup s 3132 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1936 := blockCostW [pushAt 1936 1 1] 3
    (blockOfW _ (pcFactW s 1936 3133 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1936)
      (stepW_push s 3133 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1937 := blockCostW [opAt 1937 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1937 3135 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1937)
      (stepW_dup s 3135 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1938 := blockCostW [pushAt 1938 1 2] 3
    (blockOfW _ (pcFactW s 1938 3136 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1938)
      (stepW_push s 3136 1 (2 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1939 := blockCostW [opAt 1939 .SHR] 3
    (blockOfW _ (pcFactW s 1939 3138 ([(2 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1939)
      (stepW_shr s 3138 ((2 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1940 := blockCostW [opAt 1940 .AND] 3
    (blockOfW _ (pcFactW s 1940 3139 ([(UInt256.shiftRight byte (2 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1940)
      (stepW_and s 3139 ((UInt256.shiftRight byte (2 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1941 := blockCostW [opAt 1941 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1941 3140 ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1941)
      (stepW_dup s 3140 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1942 := blockCostW [opAt 1942 .MUL] 5
    (blockOfW _ (pcFactW s 1942 3141 ([Bm1, (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1942)
      (stepW_mul s 3141 (Bm1) ((UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1943 := blockCostW [pushAt 1943 1 1] 3
    (blockOfW _ (pcFactW s 1943 3142 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1943)
      (stepW_push s 3142 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1944 := blockCostW [opAt 1944 .ADD] 3
    (blockOfW _ (pcFactW s 1944 3144 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1944)
      (stepW_add s 3144 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1945 := blockCostW [opAt 1945 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1945 3145 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1945)
      (stepW_dup s 3145 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1946 := blockCostW [opAt 1946 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1946 3146 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1946)
      (stepW_dup s 3146 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1947 := blockCostW [opAt 1947 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1947 3147 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1947)
      (stepW_dup s 3147 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1948 := blockCostW [opAt 1948 .MULMOD] 8
    (blockOfW _ (pcFactW s 1948 3148 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1948)
      (stepW_mulmod s 3148 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1949 := blockCostW [opAt 1949 .MULMOD] 8
    (blockOfW _ (pcFactW s 1949 3149 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1949)
      (stepW_mulmod s 3149 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1950 := blockCostW [opAt 1950 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1950 3150 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1950)
      (stepW_swap s 3150 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1951 := blockCostW [opAt 1951 .POP] 2
    (blockOfW _ (pcFactW s 1951 3151 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1951)
      (stepW_pop s 3151 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (2 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5
