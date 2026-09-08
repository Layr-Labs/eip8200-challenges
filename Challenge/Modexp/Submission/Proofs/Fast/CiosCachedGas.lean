import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedOut
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMid
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMac
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedControl

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowNineBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CiosCachedBlocks

opaque gasSteps_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.GasSteps
      (entryState s mem pa pb pdst ret rest)
      (outState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) :=
  CiosCachedBlocks.entry.steps (environment (entryState s mem pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (run_entry s mem pa pb n pdst ret rest hcap hrun hact hn hn32
      hpa hpaFit hpb hpbFit hcds hs32)

opaque gasSteps_out (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb n i pdst ret rest)
      (l1At 4348 s mem (rowBi mem pb n i) pa pb n i 0 pdst ret rest) :=
  CiosCachedBlocks.out.steps (environment (outState s mem pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (run_out s mem pa pb n i pdst ret rest hcap hrun hact hn hn32 hi
      hpa hpaFit hpb hpbFit hs32 htl)

opaque gasSteps_mid (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps
      (midState s mem paj ptj c bi pa pb n i pdst ret rest)
      (l2At 4719 s (midMem mem c) bi (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 pdst ret rest) :=
  CiosCachedBlocks.mid.steps (environment (midState s mem paj ptj c bi pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCachedMid.run_middle s mem paj ptj c bi pa pb n i pdst ret rest hcap hact
      hn hn32 hml htl)

opaque gasSteps_tailNext (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (outState s (tailMem mem c) pa pb n (i + 1) pdst ret rest) :=
  tailLoop.steps (environment (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCachedTailRows.run_next s mem pmj ptj c mu bi pa pb n i pdst ret rest
      hcap hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4339))

opaque gasSteps_tailLast (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest)
      (mpCsubState s (tailMem mem c) pdst ret rest) :=
  (tailLoop.steps (environment (tailState s mem pmj ptj c mu bi pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCachedTailRows.run_last s mem pmj ptj c mu bi pa pb n i pdst ret rest
      hcap hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4339))).trans
  (exitBlock.steps (environment (CiosCachedTailDefs.exitState s (tailMem mem c)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb n pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCachedExit.run_exit { s with memory := tailMem mem c }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pa + 32*n - 32))
      (UInt256.ofNat (pb-32)) (isFour n) pdst ret rest hcap
      (by rw [hcode]; exact jumpDest2642)))

opaque gasSteps_l1Mac (pc : Nat)
    (block : Block Artifact.submissionArtifact .Osaka pc l1Program)
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At pc s mem bi pa pb n i j pdst ret rest)
      (l1At (pc+37) s mem bi pa pb n i (j+1) pdst ret rest) :=
  block.steps (environment (l1At pc s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Mac pc s mem bi pa pb n i j pdst ret rest hcap hact hn32 hj hpa hpaFit)

opaque gasSteps_l1Dispatch4 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4348 s mem bi pa pb 4 i j pdst ret rest)
      (l1At 4502 s mem bi pa pb 4 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At 4348 s mem bi pa pb 4 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch4 s mem bi pa pb i j pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4502))

opaque gasSteps_l1Dispatch8 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4348 s mem bi pa pb 8 i j pdst ret rest)
      (l1At 4354 s mem bi pa pb 8 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At 4348 s mem bi pa pb 8 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch8 s mem bi pa pb i j pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4502))

opaque gasSteps_l1Join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4502 s mem bi pa pb n i j pdst ret rest)
      (l1At 4503 s mem bi pa pb n i j pdst ret rest) :=
  l1Join.steps (environment (l1At 4502 s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Join s mem bi pa pb n i j pdst ret rest hcap)

opaque gasSteps_l2Mac (pc : Nat)
    (block : Block Artifact.submissionArtifact .Osaka pc l2Program)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n) :
    Challenge.EvmProof.GasSteps
      (l2At pc s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At (pc+40) s mem bi mu c0 pa pb n i (k+1) pdst ret rest) :=
  block.steps (environment (l2At pc s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Mac pc s mem bi mu c0 pa pb n i k pdst ret rest hcap hact hn32 hk)

opaque gasSteps_l2Dispatch4 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4719 s mem bi mu c0 pa pb 4 i k pdst ret rest)
      (l2At 4885 s mem bi mu c0 pa pb 4 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4719 s mem bi mu c0 pa pb 4 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch4 s mem bi mu c0 pa pb i k pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4885))

opaque gasSteps_l2Dispatch8 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4719 s mem bi mu c0 pa pb 8 i k pdst ret rest)
      (l2At 4725 s mem bi mu c0 pa pb 8 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4719 s mem bi mu c0 pa pb 8 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch8 s mem bi mu c0 pa pb i k pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4885))

opaque gasSteps_l2Join (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4885 s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At 4886 s mem bi mu c0 pa pb n i k pdst ret rest) :=
  l2Join.steps (environment (l2At 4885 s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join s mem bi mu c0 pa pb n i k pdst ret rest hcap)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedGas
