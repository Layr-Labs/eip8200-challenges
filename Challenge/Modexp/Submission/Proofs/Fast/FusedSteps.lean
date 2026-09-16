import Challenge.Modexp.Submission.Proofs.Fast.FusedRuns
import Challenge.Modexp.Submission.Proofs.Fast.FusedRuns2
import Challenge.Modexp.Submission.Proofs.Fast.FusedBlocks
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.KernelChain
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas
import Challenge.Modexp.Submission.Proofs.Fast.R8Rows
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
import Challenge.Modexp.Submission.Proofs.Fast.SquareCaches
import Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Fused-square step compositions. Generated. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedSteps

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel
open CiosCachedMacCore CarryRowModel StagedOperand CarryRowBlocks CiosCachedMidMemory SquareRows SquareResult

theorem shuffleU (a b c d : UInt256) : a - (b - c) - d = a + ((c - b) - d) := by
  apply Challenge.EvmProof.Word.word_ext
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  have hc : c.toNat < 2 ^ 256 := c.val.isLt
  have hd : d.toNat < 2 ^ 256 := d.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_sub]
  omega

theorem mul_commU (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]


opaque gasSteps_l2Dispatch8F0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 5561 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 5562 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j0_0).steps (environment (l2At 5561 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F0 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 5709 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 5710 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j0_5).steps (environment (l2At 5709 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF0 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 5776 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 5809,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j0_8).steps (environment (l2At 5776 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF0 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 6131 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 6132 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j1_0).steps (environment (l2At 6131 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F1 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 6279 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 6280 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j1_5).steps (environment (l2At 6279 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF1 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 6346 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 6379,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j1_8).steps (environment (l2At 6346 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF1 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 6664 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 6665 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j2_0).steps (environment (l2At 6664 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F2 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 6812 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 6813 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j2_5).steps (environment (l2At 6812 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF2 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 6879 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 6912,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j2_8).steps (environment (l2At 6879 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF2 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 7160 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 7161 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j3_0).steps (environment (l2At 7160 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F3 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 7308 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 7309 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j3_5).steps (environment (l2At 7308 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF3 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 7375 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 7408,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j3_8).steps (environment (l2At 7375 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF3 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 7619 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 7620 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j4_0).steps (environment (l2At 7619 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F4 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 7767 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 7768 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j4_5).steps (environment (l2At 7767 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF4 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 7834 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 7867,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j4_8).steps (environment (l2At 7834 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF4 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 8041 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 8042 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j5_0).steps (environment (l2At 8041 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F5 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 8189 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 8190 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j5_5).steps (environment (l2At 8189 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF5 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 8256 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 8289,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j5_8).steps (environment (l2At 8256 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF5 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2Dispatch8F6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 8426 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest)
      (l2At 8427 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j6_0).steps (environment (l2At 8426 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2Join8F6 s mid bi mu c0 pb 8 i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2JoinF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i kk : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (l2At 8574 s mid bi mu c0 pb n i kk hd ent pdst ret rest)
      (l2At 8575 s mid bi mu c0 pb n i kk hd ent pdst ret rest) :=
  (FusedBlocks.b_j6_5).steps (environment (l2At 8574 s mid bi mu c0 pb n i kk hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2JoinF6 s mid bi mu c0 pb n i kk hd ent pdst ret rest hcap)

opaque gasSteps_l2FinalF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    GasSteps (l2At 8641 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      ({ s with
               pc := UInt256.ofNat 8674,
               stack := [(l2Step mid mu c0 n (n-1)).carry, bi, UInt256.ofNat (ptrAt (pb+32*n-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest,
               memory := (l2Step mid mu c0 n (n-1)).memory }) :=
  (FusedBlocks.b_j6_8).steps (environment (l2At 8641 s mid bi mu c0 pb n i (n-2) hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (FusedRuns2.run_l2LastF6 s mid bi mu c0 pb n i hd ent pdst ret rest hcap hact hn32 hn)

opaque gasSteps_l2EightF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 5561 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 5809,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F0 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 5562 10 192 2304 2336 FusedBlocks.b_j0_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 5606 1 160 2272 2304 FusedBlocks.b_j0_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 5641 1 128 2240 2272 FusedBlocks.b_j0_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 5676 96 2208 2240 FusedBlocks.b_j0_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF0 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 5710 64 2176 2208 FusedBlocks.b_j0_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 5743 32 2144 2176 FusedBlocks.b_j0_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF0 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 6131 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 6379,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F1 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 6132 10 192 2304 2336 FusedBlocks.b_j1_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 6176 1 160 2272 2304 FusedBlocks.b_j1_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 6211 1 128 2240 2272 FusedBlocks.b_j1_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 6246 96 2208 2240 FusedBlocks.b_j1_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF1 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 6280 64 2176 2208 FusedBlocks.b_j1_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 6313 32 2144 2176 FusedBlocks.b_j1_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF1 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 6664 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 6912,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F2 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 6665 10 192 2304 2336 FusedBlocks.b_j2_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 6709 1 160 2272 2304 FusedBlocks.b_j2_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 6744 1 128 2240 2272 FusedBlocks.b_j2_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 6779 96 2208 2240 FusedBlocks.b_j2_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF2 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 6813 64 2176 2208 FusedBlocks.b_j2_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 6846 32 2144 2176 FusedBlocks.b_j2_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF2 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 7160 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 7408,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F3 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 7161 10 192 2304 2336 FusedBlocks.b_j3_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 7205 1 160 2272 2304 FusedBlocks.b_j3_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 7240 1 128 2240 2272 FusedBlocks.b_j3_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 7275 96 2208 2240 FusedBlocks.b_j3_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF3 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 7309 64 2176 2208 FusedBlocks.b_j3_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 7342 32 2144 2176 FusedBlocks.b_j3_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF3 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 7619 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 7867,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F4 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 7620 10 192 2304 2336 FusedBlocks.b_j4_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 7664 1 160 2272 2304 FusedBlocks.b_j4_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 7699 1 128 2240 2272 FusedBlocks.b_j4_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 7734 96 2208 2240 FusedBlocks.b_j4_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF4 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 7768 64 2176 2208 FusedBlocks.b_j4_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 7801 32 2144 2176 FusedBlocks.b_j4_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF4 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 8041 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 8289,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F5 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 8042 10 192 2304 2336 FusedBlocks.b_j5_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 8086 1 160 2272 2304 FusedBlocks.b_j5_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 8121 1 128 2240 2272 FusedBlocks.b_j5_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 8156 96 2208 2240 FusedBlocks.b_j5_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF5 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 8190 64 2176 2208 FusedBlocks.b_j5_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 8223 32 2144 2176 FusedBlocks.b_j5_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF5 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2EightF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 8426 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      ({ s with
               pc := UInt256.ofNat 8674,
               stack := [(l2Step mid mu c0 8 7).carry, bi, UInt256.ofNat (ptrAt (pb+32*8-32) i),
                 hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv, m0] ++
                 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest),
               memory := (l2Step mid mu c0 8 7).memory }) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8F6 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_l2Mac 8427 10 192 2304 2336 FusedBlocks.b_j6_1 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 8471 1 160 2272 2304 FusedBlocks.b_j6_2 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_l2Mac 8506 1 128 2240 2272 FusedBlocks.b_j6_3 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (CarryRowGas.gasSteps_extraL2 0 8541 96 2208 2240 FusedBlocks.b_j6_4 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2JoinF6 s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (CarryRowGas.gasSteps_extraL2 1 8575 64 2176 2208 FusedBlocks.b_j6_6 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (CarryRowGas.gasSteps_extraL2 2 8608 32 2144 2176 FusedBlocks.b_j6_7 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2FinalF6 s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

def gasSteps_l1StepF0_0 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 2 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 5880 s q bi pb n i hd ent pdst ret rest)
      (l1Q 5917 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 2 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 2))
      (ht : t.toNat = 2112 + 32 * (7 - 2)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_0).steps (environment (l1Q 5880 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 5880 160 2272 (by decide) (by decide))

def gasSteps_l1StepF0_1 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 3 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 5917 s q bi pb n i hd ent pdst ret rest)
      (l1Q 5954 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 3 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 3))
      (ht : t.toNat = 2112 + 32 * (7 - 3)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_1).steps (environment (l1Q 5917 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 5917 128 2240 (by decide) (by decide))

def gasSteps_l1StepF0_2 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 4 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 5954 s q bi pb n i hd ent pdst ret rest)
      (l1Q 5991 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 4 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 4))
      (ht : t.toNat = 2112 + 32 * (7 - 4)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_2).steps (environment (l1Q 5954 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 5954 96 2208 (by decide) (by decide))

def gasSteps_l1StepF0_3 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 5 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 5991 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6028 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 5 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 5))
      (ht : t.toNat = 2112 + 32 * (7 - 5)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_3).steps (environment (l1Q 5991 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 5991 64 2176 (by decide) (by decide))

def gasSteps_l1StepF0_4 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 6 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6028 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6065 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 6 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 6))
      (ht : t.toNat = 2112 + 32 * (7 - 6)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_4).steps (environment (l1Q 6028 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6028 32 2144 (by decide) (by decide))

def gasSteps_l1StepF0_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6065 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6102 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c0_5).steps (environment (l1Q 6065 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6065 0 2112 (by decide) (by decide))

def gasSteps_l1StepF1_1 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 3 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6450 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6487 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 3 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 3))
      (ht : t.toNat = 2112 + 32 * (7 - 3)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c1_1).steps (environment (l1Q 6450 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6450 128 2240 (by decide) (by decide))

def gasSteps_l1StepF1_2 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 4 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6487 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6524 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 4 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 4))
      (ht : t.toNat = 2112 + 32 * (7 - 4)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c1_2).steps (environment (l1Q 6487 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6487 96 2208 (by decide) (by decide))

def gasSteps_l1StepF1_3 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 5 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6524 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6561 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 5 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 5))
      (ht : t.toNat = 2112 + 32 * (7 - 5)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c1_3).steps (environment (l1Q 6524 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6524 64 2176 (by decide) (by decide))

def gasSteps_l1StepF1_4 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 6 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6561 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6598 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 6 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 6))
      (ht : t.toNat = 2112 + 32 * (7 - 6)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c1_4).steps (environment (l1Q 6561 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6561 32 2144 (by decide) (by decide))

def gasSteps_l1StepF1_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6598 s q bi pb n i hd ent pdst ret rest)
      (l1Q 6635 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c1_5).steps (environment (l1Q 6598 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6598 0 2112 (by decide) (by decide))

def gasSteps_l1StepF2_2 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 4 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 6983 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7020 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 4 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 4))
      (ht : t.toNat = 2112 + 32 * (7 - 4)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c2_2).steps (environment (l1Q 6983 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 6983 96 2208 (by decide) (by decide))

def gasSteps_l1StepF2_3 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 5 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7020 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7057 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 5 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 5))
      (ht : t.toNat = 2112 + 32 * (7 - 5)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c2_3).steps (environment (l1Q 7020 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7020 64 2176 (by decide) (by decide))

def gasSteps_l1StepF2_4 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 6 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7057 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7094 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 6 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 6))
      (ht : t.toNat = 2112 + 32 * (7 - 6)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c2_4).steps (environment (l1Q 7057 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7057 32 2144 (by decide) (by decide))

def gasSteps_l1StepF2_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7094 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7131 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c2_5).steps (environment (l1Q 7094 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7094 0 2112 (by decide) (by decide))

def gasSteps_l1StepF3_3 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 5 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7479 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7516 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 5 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 5))
      (ht : t.toNat = 2112 + 32 * (7 - 5)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c3_3).steps (environment (l1Q 7479 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7479 64 2176 (by decide) (by decide))

def gasSteps_l1StepF3_4 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 6 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7516 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7553 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 6 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 6))
      (ht : t.toNat = 2112 + 32 * (7 - 6)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c3_4).steps (environment (l1Q 7516 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7516 32 2144 (by decide) (by decide))

def gasSteps_l1StepF3_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7553 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7590 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c3_5).steps (environment (l1Q 7553 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7553 0 2112 (by decide) (by decide))

def gasSteps_l1StepF4_4 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 6 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7938 s q bi pb n i hd ent pdst ret rest)
      (l1Q 7975 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 6 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 6))
      (ht : t.toNat = 2112 + 32 * (7 - 6)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c4_4).steps (environment (l1Q 7938 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7938 32 2144 (by decide) (by decide))

def gasSteps_l1StepF4_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 7975 s q bi pb n i hd ent pdst ret rest)
      (l1Q 8012 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c4_5).steps (environment (l1Q 7975 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 7975 0 2112 (by decide) (by decide))

def gasSteps_l1StepF5_5 (s : State) (q : MacState) (bi : UInt256)
    (pa pb n i j : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjk : j + 8 = 7 + n)
    (hsnapshot : Snapshot q.memory pa n) :
    GasSteps (l1Q 8360 s q bi pb n i hd ent pdst ret rest)
      (l1Q 8397 s (SquareModel.l1StepOn q bi pa n j) bi pb n i hd ent pdst ret rest) := by
  have hj : j < n := by omega
  have ho : n - 1 - j = 7 - 7 := by omega
  have hrunQ := fun (pc : Nat) (off t : UInt256) (hoff : off.toNat = 32 * (7 - 7))
      (ht : t.toNat = 2112 + 32 * (7 - 7)) =>
    StagedOperand.run_stepQ pc off t s q bi pa pb n i j hd ent pdst ret rest hcap hact hn hj
      (by rw [ho]; exact hoff) (by rw [ho]; exact ht) hsnapshot
  exact (FusedBlocks.b_c5_5).steps (environment (l1Q 8360 s q bi pb n i hd ent pdst ret rest)
      hcode hfork hrun hnp) rfl (hrunQ 8360 0 2112 (by decide) (by decide))

def gasSteps_midF0 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 6102 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 6131 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c0_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF0 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_midF1 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 6635 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 6664 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c1_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF1 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_midF2 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 7131 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 7160 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c2_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF2 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_midF3 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 7590 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 7619 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c3_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF3 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_midF4 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 8012 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 8041 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c4_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF4 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_midF5 (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    GasSteps (midStateAt 8397 s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 8426 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (FusedBlocks.b_c5_mid).steps (environment _ hcode hfork hrun hnp) rfl
    (FusedRuns2.run_middleWideF5 s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hn32 hc hminv)

def gasSteps_joinF0 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 5561 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 5830)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF0 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF0 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF0 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j0_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th0 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF1 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 6131 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 6400)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF1 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF1 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF1 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j1_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th1 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF2 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 6664 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 6933)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF2 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF2 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF2 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j2_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th2 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF3 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 7160 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 7429)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF3 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF3 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF3 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j3_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th3 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF4 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 7619 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 7888)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF4 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF4 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF4 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j4_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th4 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF5 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 8041 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 8310)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF5 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF5 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF5 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j5_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th5 h2 rfl hcode hfork hrun hnp))

def gasSteps_joinF6 (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    GasSteps (l2At 8426 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (framed {s with memory := tailCarry ((l2Step mid mu c0 8 7).memory) (l2Step mid mu c0 8 7).carry bi} (UInt256.ofNat 8695)
        ([negative32+UInt256.ofNat (ptrAt (pb+32*8-32) i), hd, UInt256.ofNat (pb-32), ent, negative32, allOnes, l2Target 8, inv] ++ (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have gL := gasSteps_l2EightF6 s mid bi mu c0 pb i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hc
  have h1 := FusedRuns.run_tailStoreF6 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h2 := FusedRuns2.run_headPOPF6 {s with memory := (l2Step mid mu c0 8 7).memory}
    (l2Step mid mu c0 8 7).carry bi (UInt256.ofNat (ptrAt (pb+32*8-32) i)) hd (UInt256.ofNat (pb-32))
    ent (l2Target 8) inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  exact gL.trans ((SquareRow.stepsOf FusedBlocks.b_j6_9 h1 rfl hcode hfork hrun hnp).trans
    (SquareRow.stepsOf FusedBlocks.b_th6 h2 rfl hcode hfork hrun hnp))

def gasSteps_glueF0 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 5830) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 5880 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF0 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g0_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed0 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F0 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g0_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF0 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g0_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF0 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g0_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF0 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g0_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF1 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 6400) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 6450 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF1 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g1_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed1 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F1 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g1_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF1 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g1_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF1 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g1_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF1 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g1_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF2 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 6933) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 6983 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF2 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g2_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed2 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F2 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g2_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF2 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g2_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF2 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g2_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF2 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g2_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF3 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 7429) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 7479 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF3 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g3_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed3 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F3 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g3_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF3 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g3_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF3 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g3_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF3 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g3_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF4 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 7888) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 7938 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF4 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g4_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed4 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F4 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g4_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF4 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g4_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF4 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g4_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF4 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g4_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF5 (s : State) (mem : ByteArray) (n i e : Nat)
    (w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (M : ByteArray)
    (hM : M = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i) (hT : ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 8310) ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))::(UInt256.ofNat 4065)::(UInt256.ofNat (2368 - 32))::(UInt256.ofNat e)::negative32::allOnes::(l2Target n)::w8::w9::w10::w11::w12::w13::aprev::rest))
      (l1Q 8360 s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev)) (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i (UInt256.ofNat 4065) (UInt256.ofNat (e + 37)) w8 w9 (w10 :: w11 :: w12 :: w13 :: (sqX mem n i) :: rest)) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF5 s' (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes (l2Target n) w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g5_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed5 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F5 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) negative32 allOnes
    ((l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g5_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF5 s' (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g5_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF5 s' ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i))
    ((UInt256.ofNat 4065) :: (UInt256.ofNat (2368 - 32)) :: (UInt256.ofNat e) :: negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g5_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF5 {s' with memory := M} ((UInt256.gt (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) ((((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) + MachineState.readWord s'.memory ((UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)))) - (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat))) (((MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat)) (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)) (UInt256.ofNat 4065) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    (negative32 :: allOnes :: (l2Target n) :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g5_5 hB4 rfl hcode hfork hrun hnp
  rw [hM] at gB4
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, allOnes_value, gt_iff_lt, mul_commU, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt, shuffleU,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl
def gasSteps_glueF6 (s : State) (mem : ByteArray) (n i e : Nat)
    (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hP : P.toNat = aAddr n i) (hT : (P - (256 : UInt256)).toNat = tAddr n i) :
    GasSteps (framed {s with memory := mem} (UInt256.ofNat 8695) (P::hd::w3::ent::w5::M::w7::w8::w9::w10::w11::w12::w13::aprev::rest))
      ({ s with pc := UInt256.ofNat 8745, stack := ((UInt256.gt (((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem P.toNat)) ((((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem P.toNat)) + MachineState.readWord mem (P - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem P.toNat) ((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem P.toNat)) (((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem P.toNat)) - (UInt256.mulMod (MachineState.readWord mem P.toNat) ((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem P.toNat)))) - (((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem P.toNat))) :: (((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem P.toNat)) :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord mem P.toNat) :: rest, memory := MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem P.toNat)) + MachineState.readWord mem (P - (256 : UInt256)).toNat).toNat 32) (P - (256 : UInt256)).toNat }) := by
  let s' : State := {s with memory := mem}
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat P.toNat 32) = s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat (P - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  -- block A
  have hA := FusedRuns.run_AF6 s' P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [SquareRow.push0_eq] at hA
  have gA := SquareRow.stepsOf FusedBlocks.b_g6_0 hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := FusedRuns2.gasSteps_fusedSgt_framed6 s' s'.memory (UInt256.ofNat 0) aprev
    ((MachineState.readWord s'.memory P.toNat) :: P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory P.toNat) :: rest)
    hcode hfork (by simp only [List.length_cons]; omega) hrun hnp
  -- block B1
  have hB1 := FusedRuns.run_B1F6 s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory P.toNat) P hd w3 ent w5 M
    (w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory P.toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB1 := SquareRow.stepsOf FusedBlocks.b_g6_2 hB1 rfl hcode hfork hrun hnp
  -- block B23a
  have hB23a := FusedRuns.run_B23aF6 s' (MachineState.readWord s'.memory P.toNat) ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory P.toNat)) P
    (hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory P.toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB23a := SquareRow.stepsOf FusedBlocks.b_g6_3 hB23a rfl hcode hfork hrun hnp
  -- block B23b
  have hB23b := FusedRuns.run_B23bF6 s' (P - (256 : UInt256)) (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory P.toNat) ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory P.toNat)) (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory P.toNat) ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory P.toNat))) (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory P.toNat)) P
    (hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory P.toNat) :: rest)
    (by simp only [List.length_cons]; omega) hactT
  have gB23b := SquareRow.stepsOf FusedBlocks.b_g6_4 hB23b rfl hcode hfork hrun hnp
  -- block B4POP
  have hB4 := FusedRuns2.run_B4POPF6 {s' with memory := MachineState.writeBytes s'.memory (Data.Bytes.natToBytesPadded ((((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) + MachineState.readWord s'.memory (P - (256 : UInt256)).toNat).toNat 32) (P - (256 : UInt256)).toNat} ((UInt256.gt (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) ((((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) + MachineState.readWord s'.memory (P - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord s'.memory P.toNat) ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory P.toNat)) (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat)) - (UInt256.mulMod (MachineState.readWord s'.memory P.toNat) ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) M - UInt256.lt ((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord s'.memory P.toNat)))) - (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord s'.memory P.toNat))) (((MachineState.readWord s'.memory P.toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord s'.memory P.toNat)) P hd w3 ent
    (w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: (MachineState.readWord s'.memory P.toNat) :: rest)
    (by simp only [List.length_cons]; omega)
  have gB4 := SquareRow.stepsOf FusedBlocks.b_g6_5 hB4 rfl hcode hfork hrun hnp
  have gB := gB1.trans (gB23a.trans (gB23b.trans gB4))
  exact (gA.trans gS).trans gB

def gasSteps_rowF7 (s : State) (mem : ByteArray)
    (inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256)
    (M7 : ByteArray) (hM7 : M7 = MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hminvR7 : inverseInvariant mem 8)
    (hcR7 : CiosReadonly.ReadonlyCache mem 8 (UInt256.ofNat 2336) inv m0)
    (heR7 : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (framed {s with memory := mem} (UInt256.ofNat 8695) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368-32)) :: (UInt256.ofNat (sqEnt 8 7)) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: (UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest))
      (CiosCachedTailDefs.sqExitState s (tailCarry (l2Step (midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).memory (l2Step (midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).carry (overflow (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) (UInt256.ofNat (ptrAt (2368+32*8-32) (7+1))) 2368 8 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 7 + 37)) inv m0 ((UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: pdst :: ret :: rest)) := by
  have hP7 : (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat = aAddr 8 7 :=
    SquareRow.ptr_toNat 8 7 (by omega) (by decide)
  have hT7 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat = tAddr 8 7 :=
    SquareRow.tptr_toNat 8 7 (by omega) (by decide)
  have gB4_7 := gasSteps_glueF6 s mem 8 7 (sqEnt 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)) (UInt256.ofNat 4065) (UInt256.ofNat (2368-32)) (UInt256.ofNat (sqEnt 8 7)) negative32 allOnes (l2Target 8) inv m0 (UInt256.ofNat 2336) m96 m64 m32 aprev pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by decide) hP7 hT7
  have hjump : Decode.isValidJumpDest ({ s with pc := UInt256.ofNat 8745, stack := ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) :: (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) :: (UInt256.ofNat (ptrAt (2368+32*8-32) 7)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368-32)) :: ((UInt256.ofNat (sqEnt 8 7)) + UInt256.ofNat 37) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: (UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: (pdst :: ret :: rest), memory := MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat }).executionEnv.code 3639 = true := by
    have h : ({ s with pc := UInt256.ofNat 8745, stack := ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) :: (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) :: (UInt256.ofNat (ptrAt (2368+32*8-32) 7)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368-32)) :: ((UInt256.ofNat (sqEnt 8 7)) + UInt256.ofNat 37) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: (UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: (pdst :: ret :: rest), memory := MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat }).executionEnv.code = Challenge.Modexp.submissionBytecode := hcode
    rw [h]; exact FusedRuns2.jumpDest3639
  have hRejoin := FusedRuns2.run_rejoin ({ s with pc := UInt256.ofNat 8745, stack := ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) :: (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) :: (UInt256.ofNat (ptrAt (2368+32*8-32) 7)) :: (UInt256.ofNat 4065) :: (UInt256.ofNat (2368-32)) :: ((UInt256.ofNat (sqEnt 8 7)) + UInt256.ofNat 37) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: (UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: (pdst :: ret :: rest), memory := MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat }) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)) (UInt256.ofNat 4065) (UInt256.ofNat (2368-32)) (UInt256.ofNat (sqEnt 8 7)) (negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: (UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: (pdst :: ret :: rest)) (by simp only [List.length_cons]; omega) hjump
  have gRejoin := SquareRow.stepsOf FusedBlocks.b_rejoin hRejoin rfl hcode hfork hrun hnp
  have hW : ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat = 2112 := by have hTT := hT7; unfold tAddr at hTT; omega
  have hsz : (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32).size = 32 := by simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hinv7 : MachineState.readWord ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 2720 = MachineState.readWord mem 2720 :=
    Memory.readWord_writeBytes_disjoint mem ((Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32)) 2720 (((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) (Or.inr (by rw [hsz, hW]; omega))
  have hm07 : MachineState.readWord ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) (32*8-32) = MachineState.readWord mem (32*8-32) :=
    Memory.readWord_writeBytes_disjoint mem ((Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32)) (32*8-32) (((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) (Or.inl (by rw [hW]; omega))
  have hcR7' : CiosReadonly.ReadonlyCache ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 8 (UInt256.ofNat 2336) inv m0 :=
    hcR7.of_preserved hinv7 hm07
  have hminv7 : inverseInvariant ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 8 := by
    unfold inverseInvariant
    rw [hm07, hinv7]
    exact hminvR7
  have h967 : MachineState.readWord ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 96 = MachineState.readWord mem 96 :=
    Memory.readWord_writeBytes_disjoint mem ((Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32)) 96 (((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) (Or.inl (by rw [hW]; omega))
  have h647 : MachineState.readWord ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 64 = MachineState.readWord mem 64 :=
    Memory.readWord_writeBytes_disjoint mem ((Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32)) 64 (((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) (Or.inl (by rw [hW]; omega))
  have h327 : MachineState.readWord ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) 32 = MachineState.readWord mem 32 :=
    Memory.readWord_writeBytes_disjoint mem ((Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32)) 32 (((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) (Or.inl (by rw [hW]; omega))
  have heR7' : CiosReadonlyExtra.ExtraCache ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) m96 m64 m32 :=
    heR7.of_preserved h967 h647 h327
  have heMid : CiosReadonlyExtra.ExtraCache ((midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) m96 m64 m32 :=
    extraCache_midMem1 heR7' (((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))
  have gMid := CarryRowGas.gasSteps_mid s ((MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) (((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) + (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) 2368 8 7 ((UInt256.ofNat 4065)) ((UInt256.ofNat (sqEnt 8 7 + 37))) ((UInt256.ofNat 2336)) inv m0 ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide) (by decide) hminv7 hcR7'
  have gL2 := CarryRowGas.gasSteps_l2Eight s ((midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) ((overflow (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) ((rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8)) ((rowC0 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8)) 2368 7 ((UInt256.ofNat 4065)) ((UInt256.ofNat (sqEnt 8 7 + 37))) ((UInt256.ofNat 2336)) inv m0 ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact heMid
  have gTail := CarryRowGas.gasSteps_tailLastSq s ((l2Step (midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).memory) ((l2Step (midMem1 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).carry) ((rowMu (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8)) ((overflow (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord mem ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) allOnes - UInt256.lt ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) aprev)) * (MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) 2368 8 7 ((UInt256.ofNat (sqEnt 8 7 + 37))) ((UInt256.ofNat 2336)) inv m0 ((MachineState.readWord mem (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) m96 m64 m32 pdst ret rest (by omega) hrun hcode hfork hnp hact (by decide) (by decide) (by decide) jumpDest4710'
  exact (((gB4_7.trans gRejoin).trans gMid).trans gL2).trans gTail

theorem resultF_eq_l2At (s : State) (mem : ByteArray) (tl inv m0 m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hscr : R8RowZeroExact.ScratchZero mem)
    (hminv : inverseInvariant mem 8) (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0) :
    ({R8ZeroFirstRow.result { s with memory := mem } (UInt256.ofNat 4065) (UInt256.ofNat 3417)
        negative32 (l2Target 8) inv m0 m96 m64 m32 (pdst :: ret :: rest) with pc := advancePC 2 (advancePC 12 (advancePC 232 (UInt256.ofNat 5315)))}) =
      l2At 5561 s
        (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry)
        (overflow (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry)
        (rowMu (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 8)
        (rowC0 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 8)
        2368 8 0 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37)) inv m0
        (tl :: m96 :: m64 :: m32 :: sqX (mpZeroed s mem 8) 8 0 :: pdst :: ret :: rest) := by
  have hF := R8RowZeroExact.firstMemory_eq s mem hscr
  have hQ224 : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 224 =
      MachineState.readWord mem 224 := by
    rw [readWord_sqL1 _ 8 0 224 _ (by decide) (Or.inl (by decide)),
      StagedMonpro.readWord_mpZeroed s mem 8 224 (by decide) (Or.inl (by decide))]
  have hQ2720 : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 2720 =
      MachineState.readWord mem 2720 := by
    rw [readWord_sqL1 _ 8 0 2720 _ (by decide) (Or.inr (by decide)),
      StagedMonpro.readWord_mpZeroed s mem 8 2720 (by decide) (Or.inr (by decide))]
  have hmu := R8Rows.mu_eq (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
    (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry inv (by rw [hQ2720]; exact hc.inverse)
  have hc0 := R8Rows.c0_eq (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
    (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry m0 (by rw [hQ224]; exact hc.modulusLow)
    (by rw [hQ224, hQ2720]; exact hminv) (by rw [hQ2720, ← hc.inverse]; exact hc.inverseGuard)
  have hx : sqX (mpZeroed s mem 8) 8 0 = MachineState.readWord mem 2592 := by
    unfold sqX
    rw [StagedMonpro.readWord_mpZeroed s mem 8 (aAddr 8 0) (by decide)
      (Or.inr (by unfold aAddr; omega))]
    rfl
  simp only [R8ZeroFirstRow.result, R8ZeroFirstRow.endFrame, l2At, l2Step,
    ptrAt_zero, List.cons_append, List.nil_append]
  rw [hF, hmu, hc0, R8ZeroFirstRow.zeroed_first_overflow s mem, hx, hc.lowAddress]
  rfl

theorem run_rowZeroF (s : State) (mem : ByteArray) (e : Nat)
    (inv m0 m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (FusedPrograms.prologuePOPProgram (UInt256.ofNat 3417))
      {outState s mem 2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat e) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest) with pc := UInt256.ofNat 5315} =
    some ({R8ZeroFirstRow.result {s with memory := mem} (UInt256.ofNat 4065) (UInt256.ofNat 3417) negative32 (l2Target 8) inv m0 m96 m64 m32 rest with pc := advancePC 2 (advancePC 12 (advancePC 232 (UInt256.ofNat 5315)))}) := by
  rw [R8RowZero.entry_eq]
  exact FusedRuns2.run_prologuePOP {s with memory := mem} (UInt256.ofNat 5315) (UInt256.ofNat 4065) (UInt256.ofNat e) (UInt256.ofNat 3417) negative32 (l2Target 8) inv m0 m96 m64 m32 aprev rest hcap hact

def gasSteps_prologueF (s : State) (mem : ByteArray) (e : Nat)
    (inv m0 m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {outState s mem 2368 8 0 (UInt256.ofNat 4065) (UInt256.ofNat e) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest) with pc := UInt256.ofNat 5315}
      ({R8ZeroFirstRow.result {s with memory := mem} (UInt256.ofNat 4065) (UInt256.ofNat 3417) negative32 (l2Target 8) inv m0 m96 m64 m32 rest with pc := advancePC 2 (advancePC 12 (advancePC 232 (UInt256.ofNat 5315)))}) :=
  SquareRow.stepsOf FusedBlocks.b_pro (run_rowZeroF s mem e inv m0 m96 m64 m32 aprev rest hcap hact) rfl hcode hfork hrun hnp


def gasSteps_fusedRows07 (s : State) (a0 : UInt256) (M0 : ByteArray)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 8)
    (hc : CiosReadonly.ReadonlyCache M0 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 8) :
    GasSteps {s with pc := UInt256.ofNat 5314, stack := [UInt256.ofNat (ptrAt (2368+32*8-32) 0), UInt256.ofNat 4065, UInt256.ofNat (2368-32), UInt256.ofNat (sqEnt 8 0), negative32, allOnes, (l2Target 8), inv, m0] ++ (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest), memory := M0}
    (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 7)} (UInt256.ofNat 8695) (UInt256.ofNat (ptrAt (2368+32*8-32) 7) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 7) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) :: (pdst :: ret :: rest))) := by
  have ha0 : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have hcZ : CiosReadonly.ReadonlyCache (mpZeroed s M0 8) 8 tl inv m0 :=
    hc.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)))
  have heZ : CiosReadonlyExtra.ExtraCache (mpZeroed s M0 8) m96 m64 m32 :=
    he.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 96 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 64 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 32 (by decide) (Or.inl (by decide)))
  have hminvZ : inverseInvariant (mpZeroed s M0 8) 8 := by
    unfold inverseInvariant
    rw [StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)),
      StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide))]
    exact hminv
  have hsnapZ : StagedOperand.Snapshot (mpZeroed s M0 8) 2368 8 := fun _ _ => rfl
  have htl : tl = UInt256.ofNat 2336 := by rw [hc.lowAddress]
  -- row 0
  have gEntry := SquareRow.stepsOf FusedBlocks.b_entry
    (FusedRuns2.run_entry {s with memory := M0} ([UInt256.ofNat (ptrAt (2368+32*8-32) 0), UInt256.ofNat 4065, UInt256.ofNat (2368-32), UInt256.ofNat (sqEnt 8 0), negative32, allOnes, (l2Target 8), inv, m0] ++ (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest)) (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)) rfl hcode hfork hrun hnp
  have gPro0 := gasSteps_prologueF s M0 (sqEnt 8 0) inv m0 m96 m64 m32 a0 (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact
  have gBridge0 := resultF_eq_l2At s M0 tl inv m0 m96 m64 m32 pdst ret rest hscr hminv hc
  have heQ0 : CiosReadonlyExtra.ExtraCache
      ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 0) 8 0 (UInt256.ofNat 0))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heZ 8 0 (by decide) _) _ 2368 8 (0 + 1) (8 - 1 - 0) (by omega)
  have gJoin0 := gasSteps_joinF0 s (midMem1 ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).carry) (overflow ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).carry) (rowMu ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory 8) (rowC0 ((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory 8) 2368 0 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 0 + 37)) tl inv m0 (sqX (mpZeroed s M0 8) 8 0) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (SquareRows.extraCache_midMem1 heQ0 _)
  have gR0chain := gEntry.trans (gPro0.trans (gBridge0.symm ▸ gJoin0))
  rw [htl] at gR0chain
  have gLoc0 := gR0chain
  have hTb0 : (UInt256.ofNat 0) = sqTb (sqRowsCarry (mpZeroed s M0 8) 8 0) 8 0 := by
    rw [← SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 0 (by omega) (by decide) ha0]
    show (UInt256.ofNat 0) = UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0)
    exact ha0.symm
  have hPtr0 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 0)) = UInt256.ofNat (ptrAt (2368+32*8-32) 1) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 0
  have hAEnd0 : (sqX (mpZeroed s M0 8) 8 0) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1) := by rfl
  have hMem0 : tailCarry ((l2Step (midMem1 ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).carry))) (rowMu ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) 8) (rowC0 ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).carry))) (rowMu ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) 8) (rowC0 ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) 8) 8 7).carry (overflow ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).memory)) ((((sqL1 (mpZeroed s M0 8) 8 0 (UInt256.ofNat 0))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 0) 8 0 (UInt256.ofNat 0) := rfl
  rw [hMem0, hTb0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 0, hPtr0, hAEnd0] at gLoc0
  have gAF1 : GasSteps {s with pc := UInt256.ofNat 5314, stack := [UInt256.ofNat (ptrAt (2368+32*8-32) 0), UInt256.ofNat 4065, UInt256.ofNat (2368-32), UInt256.ofNat (sqEnt 8 0), negative32, allOnes, (l2Target 8), inv, m0] ++ (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest), memory := M0} (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 1)} (UInt256.ofNat 5830) (UInt256.ofNat (ptrAt (2368+32*8-32) 1) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 1) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1) :: (pdst :: ret :: rest))) := gLoc0
  -- row 1 (cycle 0)
  have hcR1 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 1 (by omega)
  have heR1 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 1) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 1 (by omega)
  have hminvR1 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 1 (by omega)
  have hsnapR1 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 1) 2368 8 :=
    hsnapZ.sqRowsCarry 1 (by omega) (by decide)
  have hP1 : (UInt256.ofNat (ptrAt (2368+32*8-32) 1)).toNat = aAddr 8 1 := SquareRow.ptr_toNat 8 1 (by omega) (by decide)
  have hT1 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 1)) - (256 : UInt256)).toNat = tAddr 8 1 := SquareRow.tptr_toNat 8 1 (by omega) (by decide)
  have gG1 := gasSteps_glueF0 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 1)} (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (sqEnt 8 1) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 0) 8 0) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 1) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 1) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 1)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 0) 8 0))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 1) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 1)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 1) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 1)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 1)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP1 hT1
  have gC1_0 := gasSteps_l1StepF0_0 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 2 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR1.sqPro 1 _ (by omega) (by decide))
  have gC1_1 := gasSteps_l1StepF0_1 s (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 2) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 3 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (hsnapR1.sqPro 1 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2 (by decide) (Or.inr rfl) (by omega))
  have gC1_2 := gasSteps_l1StepF0_2 s (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 2) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 4 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR1.sqPro 1 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 3 (by decide) (Or.inr rfl) (by omega))
  have gC1_3 := gasSteps_l1StepF0_3 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 2) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR1.sqPro 1 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 4 (by decide) (Or.inr rfl) (by omega))
  have gC1_4 := gasSteps_l1StepF0_4 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 2) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR1.sqPro 1 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 5 (by decide) (Or.inr rfl) (by omega))
  have gC1_5 := gasSteps_l1StepF0_5 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 2) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 6) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 2368 8 1 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR1.sqPro 1 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 5 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 6 (by decide) (Or.inr rfl) (by omega))
  have hminvQ1 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 2 6 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)) (by decide) (by omega) hminvR1)
  have hcQ1 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR1 (by decide) 1 (by omega) _) (by decide) _ 2368 2 6 (by omega))
  have heQ1 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR1 8 1 (by omega) _) _ 2368 8 2 6 (by omega)
  have gM1 := gasSteps_midF0 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1))) 2368 8 1 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ1 hcQ1
  have hcE1 := SquareRows.extraCache_midMem1 heQ1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry
  have gJ1 := gasSteps_joinF1 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory 8) 2368 1 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 1) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE1
  have gR1chain := ((((((((gG1.trans gC1_0).trans gC1_1).trans gC1_2).trans gC1_3).trans gC1_4).trans gC1_5).trans gM1).trans gJ1)
  have gLoc1 := gR1chain
  have hPtr1 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 1)) = UInt256.ofNat (ptrAt (2368+32*8-32) 2) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 1
  have hAEnd1 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2) := by rfl
  have hMem1 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1)) := rfl
  rw [hMem1, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 1, hPtr1, hAEnd1] at gLoc1
  have gAF2 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 1)} (UInt256.ofNat 5830) (UInt256.ofNat (ptrAt (2368+32*8-32) 1) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 1) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 1) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 2)} (UInt256.ofNat 6400) (UInt256.ofNat (ptrAt (2368+32*8-32) 2) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 2) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2) :: (pdst :: ret :: rest))) := gLoc1
  -- row 2 (cycle 1)
  have hcR2 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 2 (by omega)
  have heR2 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 2) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 2 (by omega)
  have hminvR2 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 2 (by omega)
  have hsnapR2 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 2) 2368 8 :=
    hsnapZ.sqRowsCarry 2 (by omega) (by decide)
  have hP2 : (UInt256.ofNat (ptrAt (2368+32*8-32) 2)).toNat = aAddr 8 2 := SquareRow.ptr_toNat 8 2 (by omega) (by decide)
  have hT2 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 2)) - (256 : UInt256)).toNat = tAddr 8 2 := SquareRow.tptr_toNat 8 2 (by omega) (by decide)
  have gG2 := gasSteps_glueF1 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 2)} (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (sqEnt 8 2) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 2) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 2) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 2)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 1) 8 1))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 2) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 2)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 2) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 2)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 2)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP2 hT2
  have gC2_1 := gasSteps_l1StepF1_1 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 2368 8 2 3 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR2.sqPro 2 _ (by omega) (by decide))
  have gC2_2 := gasSteps_l1StepF1_2 s (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 2368 8 2 4 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (hsnapR2.sqPro 2 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 3 (by decide) (Or.inr rfl) (by omega))
  have gC2_3 := gasSteps_l1StepF1_3 s (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 2368 8 2 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR2.sqPro 2 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 4 (by decide) (Or.inr rfl) (by omega))
  have gC2_4 := gasSteps_l1StepF1_4 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 2368 8 2 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR2.sqPro 2 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 5 (by decide) (Or.inr rfl) (by omega))
  have gC2_5 := gasSteps_l1StepF1_5 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 3) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 6) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 2368 8 2 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR2.sqPro 2 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 3 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 5 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 6 (by decide) (Or.inr rfl) (by omega))
  have hminvQ2 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 3 5 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)) (by decide) (by omega) hminvR2)
  have hcQ2 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR2 (by decide) 2 (by omega) _) (by decide) _ 2368 3 5 (by omega))
  have heQ2 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR2 8 2 (by omega) _) _ 2368 8 3 5 (by omega)
  have gM2 := gasSteps_midF1 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2))) 2368 8 2 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ2 hcQ2
  have hcE2 := SquareRows.extraCache_midMem1 heQ2 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry
  have gJ2 := gasSteps_joinF2 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory 8) 2368 2 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 2) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE2
  have gR2chain := (((((((gG2.trans gC2_1).trans gC2_2).trans gC2_3).trans gC2_4).trans gC2_5).trans gM2).trans gJ2)
  have gLoc2 := gR2chain
  have hPtr2 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 2)) = UInt256.ofNat (ptrAt (2368+32*8-32) 3) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 2
  have hAEnd2 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3) := by rfl
  have hMem2 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2)) := rfl
  rw [hMem2, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 2, hPtr2, hAEnd2] at gLoc2
  have gAF3 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 2)} (UInt256.ofNat 6400) (UInt256.ofNat (ptrAt (2368+32*8-32) 2) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 2) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 2) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 3)} (UInt256.ofNat 6933) (UInt256.ofNat (ptrAt (2368+32*8-32) 3) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 3) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3) :: (pdst :: ret :: rest))) := gLoc2
  -- row 3 (cycle 2)
  have hcR3 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 3 (by omega)
  have heR3 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 3) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 3 (by omega)
  have hminvR3 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 3 (by omega)
  have hsnapR3 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 3) 2368 8 :=
    hsnapZ.sqRowsCarry 3 (by omega) (by decide)
  have hP3 : (UInt256.ofNat (ptrAt (2368+32*8-32) 3)).toNat = aAddr 8 3 := SquareRow.ptr_toNat 8 3 (by omega) (by decide)
  have hT3 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 3)) - (256 : UInt256)).toNat = tAddr 8 3 := SquareRow.tptr_toNat 8 3 (by omega) (by decide)
  have gG3 := gasSteps_glueF2 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 3)} (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (sqEnt 8 3) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 3) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 3) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 3)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 2) 8 2))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 3) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 3)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 3) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 3)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 3)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP3 hT3
  have gC3_2 := gasSteps_l1StepF2_2 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 2368 8 3 4 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR3.sqPro 3 _ (by omega) (by decide))
  have gC3_3 := gasSteps_l1StepF2_3 s (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 2368 8 3 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (hsnapR3.sqPro 3 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 4 (by decide) (Or.inr rfl) (by omega))
  have gC3_4 := gasSteps_l1StepF2_4 s (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 2368 8 3 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR3.sqPro 3 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 5 (by decide) (Or.inr rfl) (by omega))
  have gC3_5 := gasSteps_l1StepF2_5 s (SquareModel.l1StepOn (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 4) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 6) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 2368 8 3 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR3.sqPro 3 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 4 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 5 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 6 (by decide) (Or.inr rfl) (by omega))
  have hminvQ3 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 4 4 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)) (by decide) (by omega) hminvR3)
  have hcQ3 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR3 (by decide) 3 (by omega) _) (by decide) _ 2368 4 4 (by omega))
  have heQ3 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR3 8 3 (by omega) _) _ 2368 8 4 4 (by omega)
  have gM3 := gasSteps_midF2 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3))) 2368 8 3 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ3 hcQ3
  have hcE3 := SquareRows.extraCache_midMem1 heQ3 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry
  have gJ3 := gasSteps_joinF3 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory 8) 2368 3 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 3) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE3
  have gR3chain := ((((((gG3.trans gC3_2).trans gC3_3).trans gC3_4).trans gC3_5).trans gM3).trans gJ3)
  have gLoc3 := gR3chain
  have hPtr3 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 3)) = UInt256.ofNat (ptrAt (2368+32*8-32) 4) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 3
  have hAEnd3 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4) := by rfl
  have hMem3 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3)) := rfl
  rw [hMem3, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 3, hPtr3, hAEnd3] at gLoc3
  have gAF4 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 3)} (UInt256.ofNat 6933) (UInt256.ofNat (ptrAt (2368+32*8-32) 3) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 3) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 3) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 4)} (UInt256.ofNat 7429) (UInt256.ofNat (ptrAt (2368+32*8-32) 4) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 4) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4) :: (pdst :: ret :: rest))) := gLoc3
  -- row 4 (cycle 3)
  have hcR4 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 4 (by omega)
  have heR4 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 4) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 4 (by omega)
  have hminvR4 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 4 (by omega)
  have hsnapR4 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 4) 2368 8 :=
    hsnapZ.sqRowsCarry 4 (by omega) (by decide)
  have hP4 : (UInt256.ofNat (ptrAt (2368+32*8-32) 4)).toNat = aAddr 8 4 := SquareRow.ptr_toNat 8 4 (by omega) (by decide)
  have hT4 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 4)) - (256 : UInt256)).toNat = tAddr 8 4 := SquareRow.tptr_toNat 8 4 (by omega) (by decide)
  have gG4 := gasSteps_glueF3 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 4)} (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (sqEnt 8 4) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 4) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 4) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 4)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 3) 8 3))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 4) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 4)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 4) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 4)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 4)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP4 hT4
  have gC4_3 := gasSteps_l1StepF3_3 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 2368 8 4 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 4) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR4.sqPro 4 _ (by omega) (by decide))
  have gC4_4 := gasSteps_l1StepF3_4 s (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 2368 8 4 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 4) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (hsnapR4.sqPro 4 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 5 (by decide) (Or.inr rfl) (by omega))
  have gC4_5 := gasSteps_l1StepF3_5 s (SquareModel.l1StepOn (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 8 5) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 8 6) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 2368 8 4 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 4) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (Snapshot.l1StepOn_pres_stage (hsnapR4.sqPro 4 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 5 (by decide) (Or.inr rfl) (by omega)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 6 (by decide) (Or.inr rfl) (by omega))
  have hminvQ4 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 5 3 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)) (by decide) (by omega) hminvR4)
  have hcQ4 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR4 (by decide) 4 (by omega) _) (by decide) _ 2368 5 3 (by omega))
  have heQ4 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR4 8 4 (by omega) _) _ 2368 8 5 3 (by omega)
  have gM4 := gasSteps_midF3 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4))) 2368 8 4 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 4) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ4 hcQ4
  have hcE4 := SquareRows.extraCache_midMem1 heQ4 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry
  have gJ4 := gasSteps_joinF4 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory 8) 2368 4 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 4) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE4
  have gR4chain := (((((gG4.trans gC4_3).trans gC4_4).trans gC4_5).trans gM4).trans gJ4)
  have gLoc4 := gR4chain
  have hPtr4 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 4)) = UInt256.ofNat (ptrAt (2368+32*8-32) 5) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 4
  have hAEnd4 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5) := by rfl
  have hMem4 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4)) := rfl
  rw [hMem4, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 4, hPtr4, hAEnd4] at gLoc4
  have gAF5 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 4)} (UInt256.ofNat 7429) (UInt256.ofNat (ptrAt (2368+32*8-32) 4) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 4) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 4) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 5)} (UInt256.ofNat 7888) (UInt256.ofNat (ptrAt (2368+32*8-32) 5) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 5) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5) :: (pdst :: ret :: rest))) := gLoc4
  -- row 5 (cycle 4)
  have hcR5 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 5 (by omega)
  have heR5 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 5) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 5 (by omega)
  have hminvR5 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 5 (by omega)
  have hsnapR5 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 5) 2368 8 :=
    hsnapZ.sqRowsCarry 5 (by omega) (by decide)
  have hP5 : (UInt256.ofNat (ptrAt (2368+32*8-32) 5)).toNat = aAddr 8 5 := SquareRow.ptr_toNat 8 5 (by omega) (by decide)
  have hT5 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 5)) - (256 : UInt256)).toNat = tAddr 8 5 := SquareRow.tptr_toNat 8 5 (by omega) (by decide)
  have gG5 := gasSteps_glueF4 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 5)} (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (sqEnt 8 5) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 5) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 5) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 5)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 4) 8 4))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 5) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 5)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 5) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 5)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 5)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP5 hT5
  have gC5_4 := gasSteps_l1StepF4_4 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) 2368 2368 8 5 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 5) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR5.sqPro 5 _ (by omega) (by decide))
  have gC5_5 := gasSteps_l1StepF4_5 s (SquareModel.l1StepOn (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) 2368 8 6) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) 2368 2368 8 5 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 5) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (Snapshot.l1StepOn_pres_stage (hsnapR5.sqPro 5 _ (by omega) (by decide)) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) 6 (by decide) (Or.inr rfl) (by omega))
  have hminvQ5 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 6 2 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)) (by decide) (by omega) hminvR5)
  have hcQ5 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR5 (by decide) 5 (by omega) _) (by decide) _ 2368 6 2 (by omega))
  have heQ5 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR5 8 5 (by omega) _) _ 2368 8 6 2 (by omega)
  have gM5 := gasSteps_midF4 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5))) 2368 8 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 5) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ5 hcQ5
  have hcE5 := SquareRows.extraCache_midMem1 heQ5 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry
  have gJ5 := gasSteps_joinF5 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory 8) 2368 5 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 5) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE5
  have gR5chain := ((((gG5.trans gC5_4).trans gC5_5).trans gM5).trans gJ5)
  have gLoc5 := gR5chain
  have hPtr5 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 5)) = UInt256.ofNat (ptrAt (2368+32*8-32) 6) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 5
  have hAEnd5 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6) := by rfl
  have hMem5 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5)) := rfl
  rw [hMem5, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 5, hPtr5, hAEnd5] at gLoc5
  have gAF6 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 5)} (UInt256.ofNat 7888) (UInt256.ofNat (ptrAt (2368+32*8-32) 5) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 5) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 5) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 6)} (UInt256.ofNat 8310) (UInt256.ofNat (ptrAt (2368+32*8-32) 6) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 6) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6) :: (pdst :: ret :: rest))) := gLoc5
  -- row 6 (cycle 5)
  have hcR6 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 6 (by omega)
  have heR6 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 6) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 6 (by omega)
  have hminvR6 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 6 (by omega)
  have hsnapR6 : StagedOperand.Snapshot (sqRowsCarry (mpZeroed s M0 8) 8 6) 2368 8 :=
    hsnapZ.sqRowsCarry 6 (by omega) (by decide)
  have hP6 : (UInt256.ofNat (ptrAt (2368+32*8-32) 6)).toNat = aAddr 8 6 := SquareRow.ptr_toNat 8 6 (by omega) (by decide)
  have hT6 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 6)) - (256 : UInt256)).toNat = tAddr 8 6 := SquareRow.tptr_toNat 8 6 (by omega) (by decide)
  have gG6 := gasSteps_glueF5 {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 6)} (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (sqEnt 8 6) inv m0 (UInt256.ofNat 2336) m96 m64 m32 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5) pdst ret (pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 6) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 6) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 6)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqX (sqRowsCarry (mpZeroed s M0 8) 8 5) 8 5))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 6) (UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 6)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 6) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 6)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368 + 32 * 8 - 32) 6)) - (256 : UInt256)).toNat) rfl hcode hfork hnp hact (by omega) (by decide) hP6 hT6
  have gC6_5 := gasSteps_l1StepF5_5 s (sqPro (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6))) (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6))) 2368 2368 8 6 7 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 6) + 37)) inv m0 (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide) (by omega) (hsnapR6.sqPro 6 _ (by omega) (by decide))
  have hminvQ6 : inverseInvariant ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory 8 :=
    SquareCaches.inverse_l1Run _ _ 2368 8 7 1 (by decide) (by omega) (SquareCaches.inverse_sqPro (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)) (by decide) (by omega) hminvR6)
  have hcQ6 : CiosReadonly.ReadonlyCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory 8 (UInt256.ofNat 2336) inv m0 :=
    by rw [← htl]; exact (SquareCaches.readonlyCache_l1Run (SquareCaches.readonlyCache_sqPro hcR6 (by decide) 6 (by omega) _) (by decide) _ 2368 7 1 (by omega))
  have heQ6 : CiosReadonlyExtra.ExtraCache ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory m96 m64 m32 :=
    SquareCaches.extraCache_l1Run (SquareCaches.extraCache_sqPro heR6 8 6 (by omega) _) _ 2368 8 7 1 (by omega)
  have gM6 := gasSteps_midF5 s ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry (sqB2 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6))) 2368 8 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 6) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by omega) (by decide) hminvQ6 hcQ6
  have hcE6 := SquareRows.extraCache_midMem1 heQ6 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry
  have gJ6 := gasSteps_joinF6 s (midMem1 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry) (overflow ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry) (rowMu ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory 8) (rowC0 ((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory 8) 2368 6 (UInt256.ofNat 4065) (UInt256.ofNat ((sqEnt 8 6) + 37)) (UInt256.ofNat 2336) inv m0 (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hcE6
  have gR6chain := (((gG6.trans gC6_5).trans gM6).trans gJ6)
  have gLoc6 := gR6chain
  have hPtr6 : (negative32 + UInt256.ofNat (ptrAt (2368+32*8-32) 6)) = UInt256.ofNat (ptrAt (2368+32*8-32) 7) := by
    simpa using CarryTailRows.pointer_next (2368+32*8-32) 6
  have hAEnd6 : (sqX (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6) = (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) := by rfl
  have hMem6 : tailCarry ((l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) 8) 8 7).memory) (l2Step (midMem1 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry))) (rowMu ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) 8) (rowC0 ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) 8) 8 7).carry (overflow ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).memory)) ((((sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)))).carry))) = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 6) 8 6 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6)) := rfl
  rw [hMem6, SquareRows.sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6 (by omega) (by decide) ha0, ← SquareResult.sqRowsCarry_succ, SquareRows.sqEnt_succ 8 6, hPtr6, hAEnd6] at gLoc6
  have gAF7 : GasSteps (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 6)} (UInt256.ofNat 8310) (UInt256.ofNat (ptrAt (2368+32*8-32) 6) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 6) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 6) :: (pdst :: ret :: rest))) (framed {s with memory := (sqRowsCarry (mpZeroed s M0 8) 8 7)} (UInt256.ofNat 8695) (UInt256.ofNat (ptrAt (2368+32*8-32) 7) :: UInt256.ofNat 4065 :: UInt256.ofNat (2368-32) :: UInt256.ofNat (sqEnt 8 7) :: negative32 :: allOnes :: (l2Target 8) :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) :: (pdst :: ret :: rest))) := gLoc6
  exact gAF1.trans (gAF2.trans (gAF3.trans (gAF4.trans (gAF5.trans (gAF6.trans gAF7)))))

def gasSteps_rowsZeroWidthFused (s : State) (a0 : UInt256) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 8)
    (hscr : R8RowZeroExact.ScratchZero M0)
    (hminv : inverseInvariant M0 n)
    (hc : CiosReadonly.ReadonlyCache M0 n tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache M0 m96 m64 m32)
    (hsnap : StagedOperand.Snapshot M0 2368 n) :
    Challenge.EvmProof.GasSteps
      { rowState s a0 M0 n tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 5314 }
      (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 n) n n) (UInt256.ofNat (ptrAt (2368+32*n-32) n)) 2368 n (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt n n)) inv m0 (tl :: m96 :: m64 :: m32 :: sqLast (mpZeroed s M0 n) n :: pdst :: ret :: rest)) := by
  subst n
  have ha0 : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
  have hcZ : CiosReadonly.ReadonlyCache (mpZeroed s M0 8) 8 tl inv m0 :=
    hc.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)))
  have heZ : CiosReadonlyExtra.ExtraCache (mpZeroed s M0 8) m96 m64 m32 :=
    he.of_preserved (StagedMonpro.readWord_mpZeroed s M0 8 96 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 64 (by decide) (Or.inl (by decide)))
      (StagedMonpro.readWord_mpZeroed s M0 8 32 (by decide) (Or.inl (by decide)))
  have hminvZ : inverseInvariant (mpZeroed s M0 8) 8 := by
    unfold inverseInvariant
    rw [StagedMonpro.readWord_mpZeroed s M0 8 (32 * 8 - 32) (by decide) (Or.inl (by decide)),
      StagedMonpro.readWord_mpZeroed s M0 8 2720 (by decide) (Or.inr (by decide))]
    exact hminv
  have hsnapZ : StagedOperand.Snapshot (mpZeroed s M0 8) 2368 8 := fun _ _ => rfl
  have htl : tl = UInt256.ofNat 2336 := by rw [hc.lowAddress]
  have hP7 : (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat = aAddr 8 7 :=
    SquareRow.ptr_toNat 8 7 (by omega) (by decide)
  have hT7 : ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat = tAddr 8 7 :=
    SquareRow.tptr_toNat 8 7 (by omega) (by decide)
  have h078 : (8 - 1 - 7 : Nat) = 0 := rfl
  have h81 : (8 - 1 : Nat) = 7 := rfl
  have gFused07 := gasSteps_fusedRows07 s a0 M0 tl inv m0 m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact hscr hminv hc he hsnap
  have hstart : ({rowState s a0 M0 8 tl inv m0 m96 m64 m32 pdst ret rest 0 with pc := UInt256.ofNat 5314}) = {s with pc := UInt256.ofNat 5314, stack := [UInt256.ofNat (ptrAt (2368+32*8-32) 0), UInt256.ofNat 4065, UInt256.ofNat (2368-32), UInt256.ofNat (sqEnt 8 0), negative32, allOnes, (l2Target 8), inv, m0] ++ (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: a0 :: pdst :: ret :: rest), memory := M0} := by
    simp only [rowState, outState, sqRowsCarry_zero, sqPrev, htl]
  have gS := hstart.symm ▸ gFused07
  have hminvR7 : inverseInvariant (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 :=
    SquareCaches.inverse_sqRowsCarry (mpZeroed s M0 8) 8 (by decide) hminvZ 7 (by decide)
  have hcR7raw : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 tl inv m0 :=
    SquareCaches.readonlyCache_sqRowsCarry hcZ (by decide) 7 (by decide)
  have hcR7 : CiosReadonly.ReadonlyCache (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 (UInt256.ofNat 2336) inv m0 := by
    rw [htl] at hcR7raw; exact hcR7raw
  have heR7 : CiosReadonlyExtra.ExtraCache (sqRowsCarry (mpZeroed s M0 8) 8 7) m96 m64 m32 :=
    SquareCaches.extraCache_sqRowsCarry heZ 8 (by decide) 7 (by decide)
  have gR7 := gasSteps_rowF7 s (sqRowsCarry (mpZeroed s M0 8) 8 7) inv m0 m96 m64 m32 (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7) pdst ret rest ((MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat)) rfl hcap hrun hcode hfork hnp hact hminvR7 hcR7 heR7
  have gPath := gS.trans gR7
  have hL1 : (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) = (sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))).memory := by
    simp only [sqL1]
    rw [h078]
    simp only [l1Run_zero, sqPro, sqPro_eq, sqSum, sqLo, sqX, mul_commU,
      Challenge.EvmProof.Word.ofNat_add_mod]
    rw [hP7, hT7]
  have hL2 : ((UInt256.gt (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))) = (sqL1 (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7 (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))).carry := by
    simp only [sqL1]
    rw [h078]
    simp only [l1Run_zero, sqPro, sqPro_eq, sqCarry, sqHi, SquareDiag.diagHi, sqSum, sqLo, sqX,
      mul_commU, shuffleU, gt_iff_lt, allOnes_value, EvmSemantics.UInt256.gt, EvmSemantics.UInt256.lt,
      Challenge.EvmProof.Word.ofNat_add_mod]
    rw [hP7, hT7]
    rfl
  have htb : (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7)) = sqTb (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7 :=
    sqTb_eq_prev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7 (by decide) (by decide) ha0
  rw [htb] at hL1 hL2
  have hRD : (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) = sqLast (mpZeroed s M0 8) 8 := by
    unfold sqLast sqX; rw [h81, hP7]
  have hENT : (UInt256.ofNat (sqEnt 8 7 + 37)) = (UInt256.ofNat (sqEnt 8 8)) := by rw [sqEnt_succ 8 7]
  have hPBI : (UInt256.ofNat (ptrAt (2368+32*8-32) (7+1))) = (UInt256.ofNat (ptrAt (2368+32*8-32) 8)) := rfl
  have h88 : sqRowsCarry (mpZeroed s M0 8) 8 8 = sqRowCarry (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7 (sqTb (sqRowsCarry (mpZeroed s M0 8) 8 7) 8 7) :=
    sqRowsCarry_succ (mpZeroed s M0 8) 8 7
  have hExit : (CiosCachedTailDefs.sqExitState s (tailCarry (l2Step (midMem1 (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).memory (l2Step (midMem1 (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) (rowMu (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) (rowC0 (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) 8) 8 7).carry (overflow (MachineState.writeBytes (sqRowsCarry (mpZeroed s M0 8) 8 7) (Data.Bytes.natToBytesPadded ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat).toNat 32) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) ((UInt256.gt (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) ((((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) + MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) ((UInt256.ofNat (ptrAt (2368+32*8-32) 7)) - (256 : UInt256)).toNat) - (UInt256.lt (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)) - (UInt256.mulMod (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) allOnes - UInt256.lt ((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat)))) - (((MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) + (UInt256.sgt (UInt256.ofNat 0) (sqPrev (UInt256.ofNat 0) (mpZeroed s M0 8) 8 7))) * (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat))))) (UInt256.ofNat (ptrAt (2368+32*8-32) (7+1))) 2368 8 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 7 + 37)) inv m0 ((UInt256.ofNat 2336) :: m96 :: m64 :: m32 :: (MachineState.readWord (sqRowsCarry (mpZeroed s M0 8) 8 7) (UInt256.ofNat (ptrAt (2368+32*8-32) 7)).toNat) :: pdst :: ret :: rest)) = (CiosCachedTailDefs.sqExitState s (sqRowsCarry (mpZeroed s M0 8) 8 8) (UInt256.ofNat (ptrAt (2368+32*8-32) 8)) 2368 8 (UInt256.ofNat 4065) (UInt256.ofNat (sqEnt 8 8)) inv m0 (tl :: m96 :: m64 :: m32 :: sqLast (mpZeroed s M0 8) 8 :: pdst :: ret :: rest)) := by
    rw [h88, sqRowCarry, rowFromCarry, rowFromL2Carry, htb, hL1, hL2, hRD, hENT, hPBI, htl]
  exact hExit ▸ gPath




end Challenge.Modexp.Submission.Proofs.Fast.FusedSteps
