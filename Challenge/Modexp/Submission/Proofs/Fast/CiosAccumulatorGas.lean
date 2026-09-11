import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorBlocks
import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryOut
import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryMac
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryControl
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryOperandModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFirstModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CiosAccumulatorBlocks CarryRowModel CiosAccumulatorMemory
variable {carrySlot : UInt256}
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

opaque gasSteps_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 4 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    Challenge.EvmProof.GasSteps
      (entryState s mem pa pb pdst ret rest)
      (outState (carrySlot := negative32) s (mpZeroed s mem n) pa pb n 0
        (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 9440 :: MachineState.readWord mem (pa+96) :: MachineState.readWord mem (pa+64) :: MachineState.readWord mem (pa+32) :: MachineState.readWord mem (pa+32*(n-1)) :: pdst :: ret :: rest)) :=
  CiosAccumulatorBlocks.entry.steps (environment (entryState s mem pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosAccumulatorEntry.run_entry s mem pa pb n pdst ret rest hcap hrun hact hn hn32
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
      (outState (carrySlot := carrySlot) s mem pa pb n i pdst ret rest)
      (firstAt (carrySlot := carrySlot) 4255 s mem (rowBi mem pb n i) pa pb n i pdst ret rest) :=
  CiosAccumulatorBlocks.out.steps (environment (outState (carrySlot := carrySlot) s mem pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (run_out s mem pa pb n i pdst ret rest hcap hrun hact hn hn32 hi
      hpa hpaFit hpb hpbFit)

opaque gasSteps_mid (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn : 2 ≤ n) (hn32 : n ≤ 32)
    (_hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (_htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    Challenge.EvmProof.GasSteps
      (midState (carrySlot := carrySlot) s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At (carrySlot := MachineState.readWord mem 8224+c) 4565 s mem (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pa pb n i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  CiosAccumulatorBlocks.mid.steps (environment (midState (carrySlot := carrySlot) s mem c bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosAccumulatorModel.run_middle s mem c bi carrySlot pa pb n i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
      hn32 hc hminv)

opaque gasSteps_tailNext (s : State) (mem : ByteArray) (c mu bi t : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState (carrySlot := t) s mem c mu bi pa pb n i pdst ret rest)
      (outState (carrySlot := t) s (tailWithTN mem c bi t) pa pb n (i + 1) pdst ret rest) :=
  tailLoop.steps (environment (tailState (carrySlot := t) s mem c mu bi pa pb n i pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCarryFrames.run_next s mem c mu bi t pa pb n i pdst ret rest
      hcap hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4595))

opaque gasSteps_tailLast (s : State) (mem : ByteArray) (c mu bi t : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (_hn32 : n ≤ 32) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (tailState (carrySlot := t) s mem c mu bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (tailWithTN mem c bi t) pdst ret rest) :=
  (tailLoop.steps (environment (tailState (carrySlot := t) s mem c mu bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosCarryFrames.run_last s mem c mu bi t pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact hpb hpbFit hi (by rw [hcode]; exact jumpDest4595))).trans
  (exitBlock.steps (environment (CiosCarryFrames.exitState s (tailWithTN mem c bi t) t
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb n inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosAccumulatorTrace.run_exit { s with memory := tailWithTN mem c bi t }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat pa)
      (UInt256.ofNat (pb-32)) (l1Target n) t (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
      (by rw [hcode]; exact jumpDestCsubDirect)))

opaque gasSteps_l1Mac (pc : Nat) (off t : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (l1Program off t))
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j pdst ret rest)
      (l1At (carrySlot := carrySlot) (pc+38) s mem bi pa pb n i (j+1) pdst ret rest) :=
  block.steps (environment (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Mac pc off t s mem bi pa pb n i j pdst ret rest hcap hact hn32 hj hoff ht hpa hpaFit)

opaque gasSteps_wideL1 (pc : Nat) (off t : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (CiosOperandCache.wideProgram off t))
    (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j pdst ret rest)
      (l1At (carrySlot := carrySlot) (pc+42) s mem bi pa pb n i (j+1) pdst ret rest) :=
  block.steps (environment (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
    (CiosCarryFrames.run_wide_model pc off t s mem bi pa pb n i j pdst ret rest hcap hact hn32 hj hoff ht hpa hpaFit)


opaque gasSteps_operandL1 (slot : Fin 3) (pc : Nat) (off t : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (CiosOperandCache.extraProgram slot t))
    (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (tl inv m0 aEnd a96 a64 a32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hfour : 4 ≤ n) (hj : j < n)
    (hoff : off.toNat = 32*(n-1-j)) (hselect : off.toNat = CiosOperandCache.cacheAddress slot)
    (ht : t.toNat = 8256+32*(n-1-j)) (hpaFit : pa+32*n ≤ 8192)
    (hc : CiosOperandCache.OperandCache mem pa n a96 a64 a32 aEnd) :
    Challenge.EvmProof.GasSteps
      (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j inv m0 (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest))
      (l1At (carrySlot := carrySlot) (pc+34) s mem bi pa pb n i (j+1) inv m0 (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) :=
  block.steps (environment (l1At (carrySlot := carrySlot) pc s mem bi pa pb n i j inv m0 (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosCarryFrames.run_model slot pc off t s mem bi pa pb n i j tl inv m0 aEnd a96 a64 a32 dst ret rest
      hcap hact hn hfour hj hoff hselect ht hpaFit hc)


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
    (hAend : aEnd = MachineState.readWord mem (pa+32*(n-1))) :
    Challenge.EvmProof.GasSteps
      (firstAt (carrySlot := carrySlot) 4255 s mem bi pa pb n i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l1At (carrySlot := carrySlot) 4278 s mem bi pa pb n i 1 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  l1Mac0.steps (environment _ hcode hfork hrun hnp) rfl
    (CiosCarryFirstModel.run_commonFirst s mem bi pa pb n i tl inv m0 aEnd m96 m64 m32 pdst ret rest
      hcap hact hn hpos hpaFit htl hAend)


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
      (l1At (carrySlot := carrySlot) 4502 s mem bi pa pb n i (n-1) pdst ret rest)
      (midState (carrySlot := carrySlot) s (l1Step mem bi pa n n).memory (l1Step mem bi pa n n).carry bi
        pa pb n i pdst ret rest) :=
  l1Mac7.steps (environment (l1At (carrySlot := carrySlot) 4502 s mem bi pa pb n i (n-1) pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Last 8256 s mem bi pa pb n i pdst ret rest hcap hact hn32 hpos (by decide) hpa hpaFit)

opaque gasSteps_l1Dispatch4 (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At (carrySlot := carrySlot) 4278 s mem bi pa pb 4 i j pdst ret rest)
      (l1At (carrySlot := carrySlot) 4433 s mem bi pa pb 4 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At (carrySlot := carrySlot) 4278 s mem bi pa pb 4 i j pdst ret rest) hcode hfork hrun hnp) rfl
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
      (l1At (carrySlot := carrySlot) 4278 s mem bi pa pb 8 i j pdst ret rest)
      (l1At (carrySlot := carrySlot) 4281 s mem bi pa pb 8 i j pdst ret rest) :=
  l1Dispatch.steps (environment (l1At (carrySlot := carrySlot) 4278 s mem bi pa pb 8 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch8 s mem bi pa pb i j pdst ret rest hcap
      (by rw [hcode]; exact jumpDestL1Eight)) |>.trans
  (l1Join8.steps (environment (l1At (carrySlot := carrySlot) 4280 s mem bi pa pb 8 i j pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Join8 s mem bi pa pb 8 i j pdst ret rest hcap))

opaque gasSteps_l1Join (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1At (carrySlot := carrySlot) 4433 s mem bi pa pb n i j pdst ret rest)
      (l1At (carrySlot := carrySlot) 4434 s mem bi pa pb n i j pdst ret rest) :=
  l1Join.steps (environment (l1At (carrySlot := carrySlot) 4433 s mem bi pa pb n i j pdst ret rest) hcode hfork hrun hnp) rfl
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
      (l2At (carrySlot := carrySlot) pc s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At (carrySlot := carrySlot) (pc+(w.val+35)) s mem bi mu c0 pa pb n i (k+1) pdst ret rest) :=
  block.steps (environment (l2At (carrySlot := carrySlot) pc s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Mac pc w x tl ts s mem bi mu c0 pa pb n i k pdst ret rest hcap hact hn32 hk hx htl hts hpush)


opaque gasSteps_l2Dispatch4 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At (carrySlot := carrySlot) 4565 s mem bi mu c0 pa pb 4 i k pdst ret rest)
      (l2At (carrySlot := carrySlot) 4720 s mem bi mu c0 pa pb 4 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At (carrySlot := carrySlot) 4565 s mem bi mu c0 pa pb 4 i k pdst ret rest) hcode hfork hrun hnp) rfl
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
      (l2At (carrySlot := carrySlot) 4565 s mem bi mu c0 pa pb 8 i k pdst ret rest)
      (l2At (carrySlot := carrySlot) 4568 s mem bi mu c0 pa pb 8 i k pdst ret rest) :=
  l2Dispatch.steps (environment (l2At (carrySlot := carrySlot) 4565 s mem bi mu c0 pa pb 8 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch8 s mem bi mu c0 pa pb i k pdst ret rest hcap
      (by rw [hcode]; exact jumpDestL2Eight)) |>.trans
  (l2Join8.steps (environment (l2At (carrySlot := carrySlot) 4567 s mem bi mu c0 pa pb 8 i k pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join8 s mem bi mu c0 pa pb 8 i k pdst ret rest hcap))

opaque gasSteps_l2Join (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At (carrySlot := carrySlot) 4720 s mem bi mu c0 pa pb n i k pdst ret rest)
      (l2At (carrySlot := carrySlot) 4721 s mem bi mu c0 pa pb n i k pdst ret rest) :=
  l2Join.steps (environment (l2At (carrySlot := carrySlot) 4720 s mem bi mu c0 pa pb n i k pdst ret rest) hcode hfork hrun hnp) rfl
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
      (l2At (carrySlot := carrySlot) 4793 s mem bi mu c0 pa pb n i (n-2) pdst ret rest)
      (tailState (carrySlot := carrySlot) s (l2Step mem mu c0 n (n-1)).memory
        (l2Step mem mu c0 n (n-1)).carry mu bi pa pb n i pdst ret rest) := by
  have h := gasSteps_l2Mac (carrySlot := carrySlot) 4793 0 0 8256 8288 l2Mac6 s mem bi mu c0 pa pb n i (n-2) pdst ret rest
    hcap hrun hcode hfork hnp hact hn32 (by omega)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  rw [hnn] at h
  exact h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
