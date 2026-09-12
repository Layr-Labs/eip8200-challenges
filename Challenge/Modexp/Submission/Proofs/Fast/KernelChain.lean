import Challenge.Modexp.Submission.Proofs.Fast.KernelChainBlocks

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# First-loop chain of the sqCP1m kernel (shared by the multiply and square rows)

The seven uniform first-loop blocks `k = 1..7` sit at instruction `3071 + 32(k-1)`,
pc `4068 + 38(k-1)`; block `k` performs limb step `j = k + n - 8` (offset
`32(7-k)`, accumulator word `8256 + 32(7-k)`, for both admitted widths).  The
middle block starts with a `JUMPDEST` at pc 4334 (instruction 3295), the entry of the
empty chain.

* `gasSteps_l1Step k`  : one block, on any MAC state `q`.
* `gasSteps_l1Suffix`  : blocks `k..7` from the chain entry `4068 + 38(k-1)` to the
  middle `JUMPDEST` (`midState`), producing `SquareModel.l1Run q bi pa n j (8-k)`.
  The multiply rows use `k = 1` (`n = 8`) and `k = 5` (`n = 4`) after the `DUP6 JUMP`
  dispatch; the square rows enter at `ent = 4068 + 38(k-1)` directly.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.KernelChain

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand

/-! ## One block -/

private theorem off_eq (k n j : Nat) (hk : k ≤ 7) (hjk : j + 8 = k + n) :
    n - 1 - j = 7 - k := by omega

/-- Block `k` (`1 ≤ k ≤ 7`) performs limb step `j = k + n - 8` on any MAC state. -/
def gasSteps_l1Step (k : Nat) (hk1 : 1 ≤ k) (hk7 : k ≤ 7)
    (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = k + n)
    (hsnapshot : Snapshot q.memory pa n) :
    Challenge.EvmProof.GasSteps
      (l1Q (4060 + 38 * (k - 1)) s q bi pb n i hd ent pdst ret rest)
      (l1Q (4060 + 38 * k) s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho := off_eq k n j hk7 hjk
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - k))
      (ht : t.toNat = 8256 + 32 * (7 - k)) =>
    run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  interval_cases k
  · exact l1Block1.steps (environment (l1Q 4060 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4060 192 8448 (by decide) (by decide))
  · exact l1Block2.steps (environment (l1Q 4098 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4098 160 8416 (by decide) (by decide))
  · exact l1Block3.steps (environment (l1Q 4136 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4136 128 8384 (by decide) (by decide))
  · exact l1Block4.steps (environment (l1Q 4174 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4174 96 8352 (by decide) (by decide))
  · exact l1Block5.steps (environment (l1Q 4212 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4212 64 8320 (by decide) (by decide))
  · exact l1Block6.steps (environment (l1Q 4250 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4250 32 8288 (by decide) (by decide))
  · exact l1Block7.steps (environment (l1Q 4288 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 4288 0 8256 (by decide) (by decide))

/-! ## The chain suffix -/

/-- Peel the first step off a run. -/
theorem l1Run_succ_left (q : MacState) (bi : UInt256) (pa n j : Nat) :
    ∀ m, SquareModel.l1Run q bi pa n j (m + 1) =
      SquareModel.l1Run (SquareModel.l1StepOn q bi pa n j) bi pa n (j + 1) m
  | 0 => rfl
  | m + 1 => by
      rw [SquareModel.l1Run_succ, l1Run_succ_left q bi pa n j m, SquareModel.l1Run_succ]
      congr 1
      omega

/-- Blocks `k..7` (`k + m = 8`) from the chain entry of block `k`. -/
def gasSteps_l1Run : (m k : Nat) → 1 ≤ k → k + m = 8 →
    (s : State) → (q : MacState) → (bi : UInt256) →
    (pa pb n i j : Nat) → (hd ent pdst ret : UInt256) → (rest : List UInt256) →
    rest.length ≤ 1005 → s.halt = .Running →
    s.executionEnv.code = Challenge.Modexp.submissionBytecode →
    s.fork = .Osaka →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false →
    296 ≤ s.activeWords.toNat → n ≤ 8 → pa + 32 * n ≤ 8192 → j + 8 = k + n →
    Snapshot q.memory pa n →
    Challenge.EvmProof.GasSteps
      (l1Q (4060 + 38 * (k - 1)) s q bi pb n i hd ent pdst ret rest)
      (l1Q 4326 s (SquareModel.l1Run q bi pa n j m) bi pb n i hd ent pdst ret rest)
  | 0, k, _, hkm, s, q, bi, _, pb, n, i, _, hd, ent, pdst, ret, rest,
      _, _, _, _, _, _, _, _, _, _ => by
      obtain rfl : k = 8 := by omega
      exact Challenge.EvmProof.GasSteps.refl _
  | m + 1, k, hk1, hkm, s, q, bi, pa, pb, n, i, j, hd, ent, pdst, ret, rest,
      hcap, hrun, hcode, hfork, hnp, hact, hn, hpa, hjk, hsnapshot => by
      have h1 := gasSteps_l1Step k hk1 (by omega) s q bi pa pb n i j hd ent pdst ret rest
        hcap hrun hcode hfork hnp hact hn hjk hsnapshot
      have h2 := gasSteps_l1Run m (k + 1) (by omega) (by omega) s
        (SquareModel.l1StepOn q bi pa n j) bi pa pb n i (j + 1) hd ent pdst ret rest
        hcap hrun hcode hfork hnp hact hn hpa (by omega)
        (Snapshot.l1StepOn_pres hsnapshot bi j hn hpa (by omega))
      rw [show k + 1 - 1 = k by omega, ← l1Run_succ_left] at h2
      exact h1.trans h2

/-- **Chain entry → middle.**  From the entry of block `k` (`1 ≤ k ≤ 8`, pc
`4068 + 38(k-1)`) at limb step `j = k + n - 8` to the middle block's `JUMPDEST`,
running `8 - k` limb steps on any MAC state `q` with the staged snapshot of `a`
(`k = 8`: the empty chain, the identity). -/
def gasSteps_l1Suffix (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hpaFit : pa + 32 * n ≤ 8192)
    (hjk : j + 8 = k + n)
    (hsnapshot : Snapshot q.memory pa n) :
    Challenge.EvmProof.GasSteps
      (l1Q (4060 + 38 * (k - 1)) s q bi pb n i hd ent pdst ret rest)
      (midState s (SquareModel.l1Run q bi pa n j (8 - k)).memory
        (SquareModel.l1Run q bi pa n j (8 - k)).carry bi pb n i hd ent pdst ret rest) :=
  gasSteps_l1Run (8 - k) k hk1 (by omega) s q bi pa pb n i j hd ent pdst ret rest
    hcap hrun hcode hfork hnp hact hn hpaFit hjk hsnapshot

/-- The multiply instance: from step `j` of `l1Step` the chain ends at `l1Step … n`. -/
def gasSteps_l1SuffixMul (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hpaFit : pa + 32 * n ≤ 8192)
    (hjk : j + 8 = k + n)
    (hsnapshot : Snapshot mem pa n) :
    Challenge.EvmProof.GasSteps
      (l1At (4060 + 38 * (k - 1)) s mem bi pa pb n i j hd ent pdst ret rest)
      (midState s (l1Step mem bi pa n n).memory (l1Step mem bi pa n n).carry
        bi pb n i hd ent pdst ret rest) := by
  have h := gasSteps_l1Suffix k hk1 hk8 s (l1Step mem bi pa n j) bi pa pb n i j hd ent pdst ret rest
    hcap hrun hcode hfork hnp hact hn hpaFit hjk (hsnapshot.l1 bi j hn hpaFit)
  rw [l1Run_l1Step, show j + (8 - k) = n by omega] at h
  exact h

end Challenge.Modexp.Submission.Proofs.Fast.KernelChain
