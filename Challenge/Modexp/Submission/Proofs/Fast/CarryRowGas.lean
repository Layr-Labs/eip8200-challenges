import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntry
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
import Challenge.Modexp.Submission.Proofs.Fast.CiosCommonFirst
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedOut
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTraces
import Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMac
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedControl

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CarryRowBlocks CarryRowModel
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

opaque gasSteps_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    Challenge.EvmProof.GasSteps
      (entryState s mem pa pb pdst ret rest)
      (outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pa pb n 0
        (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 9440 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 :: MachineState.readWord mem 32 :: UInt256.ofNat (pa+32*n-32) :: pdst :: ret :: rest)) :=
  CarryRowBlocks.entry.steps (environment (entryState s mem pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (StagedOperand.run_entry s mem pa pb n pdst ret rest hcap hrun hact hn hn32
      hpa hpaFit hpb hpbFit hcds hs32 hml)

opaque gasSteps_out (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb n i pdst ret rest)
      (firstAt 4253 s mem (rowBi mem pb n i) pa pb n i pdst ret rest) :=
  CarryRowBlocks.out.steps (environment (outState s mem pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (run_out s mem pa pb n i pdst ret rest hcap hrun hact hn hn32 hi
      hpa hpaFit hpb hpbFit)

opaque gasSteps_mid (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (_hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (_htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    Challenge.EvmProof.GasSteps
      (midState s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 4578 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  CarryRowBlocks.mid.steps (environment (midState s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CarryReadonlyRun.run_middle s mem c bi pa pb n i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
      hn hn32 hc hminv)

opaque gasSteps_tailNext (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pa pb n i pdst ret rest)
      (outState s (tailCarry mem c bi) pa pb n (i + 1) pdst ret rest) :=
  tailLoop.steps (environment (tailState s mem c mu bi pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (CarryTailRows.run_next s mem c mu bi pa pb n i pdst ret rest
      hcap hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4595))

opaque gasSteps_tailLast (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (tailCarry mem c bi) pdst ret rest) :=
  (tailLoop.steps (environment (tailState s mem c mu bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CarryTailRows.run_last s mem c mu bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4595))).trans
  (exitBlock.steps (environment (CiosCachedTailDefs.exitState s (tailCarry mem c bi)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb n inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosReadonly.run_exit { s with memory := tailCarry mem c bi }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat pa)
      (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4978)))

opaque gasSteps_l1Mac (pc : Nat) (off t : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (StagedOperand.l1Program off t))
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192) (hsnapshot : StagedOperand.Snapshot mem pa n) :
    Challenge.EvmProof.GasSteps
      (l1At pc s mem bi pa pb n i j pdst ret rest)
      (l1At (pc+38) s mem bi pa pb n i (j+1) pdst ret rest) :=
  block.steps (environment (l1At pc s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (StagedOperand.run_l1Mac pc off t s mem bi pa pb n i j pdst ret rest hcap hact hn32 hj hoff ht hpa hpaFit hsnapshot)

opaque gasSteps_commonFirst (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 9472)
    (htl : tl = UInt256.ofNat (8224+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) :
    Challenge.EvmProof.GasSteps
      (firstAt 4253 s mem bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l1At 4279 s mem bi pa pb n i 1 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  l1Mac0.steps (environment _ hcode hfork hrun hnp) rfl
    (CiosCommonFirst.run_commonFirst s mem bi pa pb n i tl inv m0 aEnd m96 m64 m32 pdst ret rest
      hcap hact hn hpos hpaFit htl hAend)

opaque gasSteps_l1First (pc : Nat) (off t : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (l1FirstProgram off t))
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hpos : 0 < n) (hoff : off.toNat = 32 * (n - 1))
    (ht : t.toNat = 8256 + 32 * (n - 1))
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At pc s mem bi pa pb n i 0 pdst ret rest)
      (l1At (pc+35) s mem bi pa pb n i 1 pdst ret rest) :=
  block.steps (environment (l1At pc s mem bi pa pb n i 0 pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1First pc off t s mem bi pa pb n i pdst ret rest hcap hact hn32 hpos hoff ht hpa hpaFit)

opaque gasSteps_l1Last (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hpos : 0 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4511 s mem bi pa pb n i (n-1) pdst ret rest)
      (midState s (l1Step mem bi pa n n).memory (l1Step mem bi pa n n).carry bi
        pa pb n i pdst ret rest) :=
  l1Mac7.steps (environment (l1At 4511 s mem bi pa pb n i (n-1) pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Last 8256 s mem bi pa pb n i pdst ret rest hcap hact hn32 hpos (by decide) hpa hpaFit)

opaque gasSteps_l1Dispatch4 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4279 s mem bi pa pb 4 i j pdst ret rest)
      (l1At 4434 s mem bi pa pb 4 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At 4279 s mem bi pa pb 4 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch4 s mem bi pa pb i j pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4757))

opaque gasSteps_l1Dispatch8 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4279 s mem bi pa pb 8 i j pdst ret rest)
      (l1At 4282 s mem bi pa pb 8 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At 4279 s mem bi pa pb 8 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch8 s mem bi pa pb i j pdst ret rest hcap
      (by rw [hcode]; exact jumpDestL1Eight)) |>.trans
  (l1Join8.steps (environment (l1At 4281 s mem bi pa pb 8 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Join8 s mem bi pa pb 8 i j pdst ret rest hcap))

opaque gasSteps_l1Join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At 4434 s mem bi pa pb n i j pdst ret rest)
      (l1At 4435 s mem bi pa pb n i j pdst ret rest) :=
  l1Join.steps (environment (l1At 4434 s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Join s mem bi pa pb n i j pdst ret rest hcap)

opaque gasSteps_l2Mac (pc : Nat) (w : Fin 33) (x tl ts : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (l2Program w x tl ts))
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k))
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (l2At pc s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At (pc+(w.val+35)) s mem bi mu c0 pa pb n i (k+1) pdst ret rest) :=
  block.steps (environment (l2At pc s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Mac pc w x tl ts s mem bi mu c0 pa pb n i k pdst ret rest hcap hact hn32 hk hx htl hts hpush)

opaque gasSteps_extraL2 (slot : Fin 3) (pc : Nat) (x loadAddr storeAddr : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc
      (CiosReadonlyExtra.extraProgram slot loadAddr storeAddr))
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32*(n-2-k)) (hselect : x.toNat = CiosReadonlyExtra.cacheAddress slot)
    (hload : loadAddr.toNat = 8256+32*(n-2-k))
    (hstore : storeAddr.toNat = 8256+32*(n-1-k))
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At pc s mem bi mu c0 pa pb n i k inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At (pc+34) s mem bi mu c0 pa pb n i (k+1) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have h := CiosReadonlyExtra.run_extraStep slot s (UInt256.ofNat pc) mem
    bi mu c0 n k x loadAddr storeAddr hx hselect hload hstore
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hk hc
  exact block.steps (environment _ hcode hfork hrun hnp) rfl
    (by simpa only [CiosCachedL2.state,l2At,Challenge.EvmProof.Word.ofNat_add_mod,
      List.cons_append,List.nil_append] using h)

opaque gasSteps_l2Dispatch4 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4578 s mem bi mu c0 pa pb 4 i k pdst ret rest)
      (l2At 4733 s mem bi mu c0 pa pb 4 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4578 s mem bi mu c0 pa pb 4 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch4 s mem bi mu c0 pa pb i k pdst ret rest hcap
      (by rw [hcode]; exact jumpDest5112))

opaque gasSteps_l2Dispatch8 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4578 s mem bi mu c0 pa pb 8 i k pdst ret rest)
      (l2At 4581 s mem bi mu c0 pa pb 8 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4578 s mem bi mu c0 pa pb 8 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch8 s mem bi mu c0 pa pb i k pdst ret rest hcap
      (by rw [hcode]; exact jumpDestL2Eight)) |>.trans
  (l2Join8.steps (environment (l2At 4580 s mem bi mu c0 pa pb 8 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join8 s mem bi mu c0 pa pb 8 i k pdst ret rest hcap))

opaque gasSteps_l2Join (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4733 s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At 4734 s mem bi mu c0 pa pb n i k pdst ret rest) :=
  l2Join.steps (environment (l2At 4733 s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join s mem bi mu c0 pa pb n i k pdst ret rest hcap)

/-- The final second-loop copy lands exactly on the row tail frame. -/
opaque gasSteps_l2Final (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hn : 2 ≤ n) :
    Challenge.EvmProof.GasSteps
      (l2At 4802 s mem bi mu c0 pa pb n i (n-2) pdst ret rest)
      (tailState s (l2Step mem mu c0 n (n-1)).memory
        (l2Step mem mu c0 n (n-1)).carry mu bi pa pb n i pdst ret rest) := by
  have h := gasSteps_l2Mac 4802 0 0 8256 8288 l2Mac6 s mem bi mu c0 pa pb n i (n-2) pdst ret rest
    hcap hrun hcode hfork hnp hact hn32 (by omega)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  rw [hnn] at h
  exact h

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas
