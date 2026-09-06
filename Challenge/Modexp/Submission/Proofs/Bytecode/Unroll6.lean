import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Copy 6 of the unrolled exponent-bit body

The copy handles exponent bit 6 at instruction indices 1952 .. 1968 and bytes
3152 .. 3171.  Its seventeen instructions are taken one at a time.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- Copy 6, with every stack slot left symbolic. -/
def gasSteps_bitCopy6_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3152 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3172 ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest)) := by
  have step1952 := soundW hs (opAt 1952 (.Dup ⟨7, by decide⟩))
    (blockOfW _ (pcFactW s 1952 3152 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1952)
      (stepW_dup s 3152 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1953 := soundW hs (pushAt 1953 1 1)
    (blockOfW _ (pcFactW s 1953 3153 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1953)
      (stepW_push s 3153 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1954 := soundW hs (opAt 1954 (.Dup ⟨4, by decide⟩))
    (blockOfW _ (pcFactW s 1954 3155 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1954)
      (stepW_dup s 3155 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num)))
  have step1955 := soundW hs (pushAt 1955 1 1)
    (blockOfW _ (pcFactW s 1955 3156 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1955)
      (stepW_push s 3156 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1956 := soundW hs (opAt 1956 .SHR)
    (blockOfW _ (pcFactW s 1956 3158 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1956)
      (stepW_shr s 3158 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1957 := soundW hs (opAt 1957 .AND)
    (blockOfW _ (pcFactW s 1957 3159 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1957)
      (stepW_and s 3159 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1958 := soundW hs (opAt 1958 (.Dup ⟨2, by decide⟩))
    (blockOfW _ (pcFactW s 1958 3160 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1958)
      (stepW_dup s 3160 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num)))
  have step1959 := soundW hs (opAt 1959 .MUL)
    (blockOfW _ (pcFactW s 1959 3161 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1959)
      (stepW_mul s 3161 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1960 := soundW hs (pushAt 1960 1 1)
    (blockOfW _ (pcFactW s 1960 3162 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1960)
      (stepW_push s 3162 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1961 := soundW hs (opAt 1961 .ADD)
    (blockOfW _ (pcFactW s 1961 3164 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1961)
      (stepW_add s 3164 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1962 := soundW hs (opAt 1962 (.Dup ⟨1, by decide⟩))
    (blockOfW _ (pcFactW s 1962 3165 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1962)
      (stepW_dup s 3165 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num)))
  have step1963 := soundW hs (opAt 1963 (.Dup ⟨8, by decide⟩))
    (blockOfW _ (pcFactW s 1963 3166 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1963)
      (stepW_dup s 3166 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1964 := soundW hs (opAt 1964 (.Dup ⟨0, by decide⟩))
    (blockOfW _ (pcFactW s 1964 3167 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1964)
      (stepW_dup s 3167 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num)))
  have step1965 := soundW hs (opAt 1965 .MULMOD)
    (blockOfW _ (pcFactW s 1965 3168 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1965)
      (stepW_mulmod s 3168 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1966 := soundW hs (opAt 1966 .MULMOD)
    (blockOfW _ (pcFactW s 1966 3169 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1966)
      (stepW_mulmod s 3169 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1967 := soundW hs (opAt 1967 (.Swap ⟨5, by decide⟩))
    (blockOfW _ (pcFactW s 1967 3170 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1967)
      (stepW_swap s 3170 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num)))
  have step1968 := soundW hs (opAt 1968 .POP)
    (blockOfW _ (pcFactW s 1968 3171 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1968)
      (stepW_pop s 3171 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step1952.trans (step1953.trans (step1954.trans (step1955.trans (step1956.trans (step1957.trans (step1958.trans (step1959.trans (step1960.trans (step1961.trans (step1962.trans (step1963.trans (step1964.trans (step1965.trans (step1966.trans (step1967.trans (step1968))))))))))))))))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitCopy6_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitCopy6_sym s rest Bm1 zero byte offset outerW acc base m hs hrest).cost = 62 := by
  unfold gasSteps_bitCopy6_sym
  have c1952 := blockCostW [opAt 1952 (.Dup ⟨7, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1952 3152 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1952)
      (stepW_dup s 3152 7 (by decide) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1953 := blockCostW [pushAt 1953 1 1] 3
    (blockOfW _ (pcFactW s 1953 3153 ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1953)
      (stepW_push s 3153 1 (1 : UInt256) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1954 := blockCostW [opAt 1954 (.Dup ⟨4, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1954 3155 ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1954)
      (stepW_dup s 3155 4 (by decide) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (byte) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1955 := blockCostW [pushAt 1955 1 1] 3
    (blockOfW _ (pcFactW s 1955 3156 ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1955)
      (stepW_push s 3156 1 (1 : UInt256) ([byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1956 := blockCostW [opAt 1956 .SHR] 3
    (blockOfW _ (pcFactW s 1956 3158 ([(1 : UInt256), byte, (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1956)
      (stepW_shr s 3158 ((1 : UInt256)) (byte) ([(1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1957 := blockCostW [opAt 1957 .AND] 3
    (blockOfW _ (pcFactW s 1957 3159 ([(UInt256.shiftRight byte (1 : UInt256)), (1 : UInt256), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1957)
      (stepW_and s 3159 ((UInt256.shiftRight byte (1 : UInt256))) ((1 : UInt256)) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1958 := blockCostW [opAt 1958 (.Dup ⟨2, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1958 3160 ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1958)
      (stepW_dup s 3160 2 (by decide) ([(UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (Bm1) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1959 := blockCostW [opAt 1959 .MUL] 5
    (blockOfW _ (pcFactW s 1959 3161 ([Bm1, (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1959)
      (stepW_mul s 3161 (Bm1) ((UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1960 := blockCostW [pushAt 1960 1 1] 3
    (blockOfW _ (pcFactW s 1960 3162 ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1960)
      (stepW_push s 3162 1 (1 : UInt256) ([(Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1961 := blockCostW [opAt 1961 .ADD] 3
    (blockOfW _ (pcFactW s 1961 3164 ([(1 : UInt256), (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1961)
      (stepW_add s 3164 ((1 : UInt256)) ((Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) ([m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1962 := blockCostW [opAt 1962 (.Dup ⟨1, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1962 3165 ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1962)
      (stepW_dup s 3165 1 (by decide) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (m) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1963 := blockCostW [opAt 1963 (.Dup ⟨8, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1963 3166 ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1963)
      (stepW_dup s 3166 8 (by decide) ([m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1964 := blockCostW [opAt 1964 (.Dup ⟨0, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1964 3167 ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1964)
      (stepW_dup s 3167 0 (by decide) ([acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (acc) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1965 := blockCostW [opAt 1965 .MULMOD] 8
    (blockOfW _ (pcFactW s 1965 3168 ([acc, acc, m, ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1965)
      (stepW_mulmod s 3168 (acc) (acc) (m) ([((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1966 := blockCostW [opAt 1966 .MULMOD] 8
    (blockOfW _ (pcFactW s 1966 3169 ([(UInt256.mulMod acc acc m), ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))), m, Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1966)
      (stepW_mulmod s 3169 ((UInt256.mulMod acc acc m)) (((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256))))) (m) ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1967 := blockCostW [opAt 1967 (.Swap ⟨5, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1967 3170 ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1967)
      (stepW_swap s 3170 5 (by decide) ([(UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1968 := blockCostW [opAt 1968 .POP] 2
    (blockOfW _ (pcFactW s 1968 3171 ([acc, Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by norm_num) pc1968)
      (stepW_pop s 3171 (acc) ([Bm1, zero, byte, offset, outerW, (UInt256.mulMod (UInt256.mulMod acc acc m) ((1 : UInt256) + (Bm1 * (UInt256.land (UInt256.shiftRight byte (1 : UInt256)) (1 : UInt256)))) m), base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
