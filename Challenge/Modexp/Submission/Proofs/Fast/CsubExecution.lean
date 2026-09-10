import Challenge.Modexp.Submission.Proofs.Fast.CsubCore

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def gasSteps_amEntry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (amEntryState s memory pa pb pd ret rest)
      (amLoopState s memory pa pb n 0 pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1600
    (by simpa [amEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [amEntryState, State.fork] using hfork)
    (run_amEntry s memory pa pb n pd ret rest hcap hrun hact hn hpa hpaFit hpb hpbFit
      hs32 htl)
    (by simpa [amEntryState] using hrun)
    (by simpa [amEntryState, State.fork] using hnp)

def gasSteps_amIteration (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n j pd ret rest)
      (amLoopState s memory pa pb n (j + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1627
    (by simpa [amLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [amLoopState, State.fork] using hfork)
    (run_amLoopBody s memory pa pb n j pd ret rest hcap hrun hcode hact hj hn32
      hpa hpaFit hpb hpbFit)
    (by simpa [amLoopState] using hrun)
    (by simpa [amLoopState, State.fork] using hnp)

def gasSteps_amLoop (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n 0 pd ret rest)
      (amLoopState s memory pa pb n (n - 1) pd ret rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (n - 1) fun i hi =>
    gasSteps_amIteration s memory pa pb n i pd ret rest hcap hcode hfork hrun hnp hact
      (by omega) hn32 hpa hpaFit hpb hpbFit

def gasSteps_amExit (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n (n - 1) pd ret rest)
      (amTailState s memory pa pb n (n - 1 + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1627
    (by simpa [amLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [amLoopState, State.fork] using hfork)
    (run_amLoopExit s memory pa pb n (n - 1) pd ret rest hcap hrun hcode hact
      (by omega) hn32 hpa hpaFit hpb hpbFit)
    (by simpa [amLoopState] using hrun)
    (by simpa [amLoopState, State.fork] using hnp)

def gasSteps_amTailStep (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps (amTailState s memory pa pb n j pd ret rest)
      (csEntryState s (MachineState.writeBytes (amStep memory pa pb n j).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n j).flag.toNat 32) 8224)
        pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1662
    (by simpa [amTailState, Artifact.submissionArtifact] using hcode)
    (by simpa [amTailState, State.fork] using hfork)
    (run_amTail s memory pa pb n j pd ret rest hcap hrun hact)
    (by simpa [amTailState] using hrun)
    (by simpa [amTailState, State.fork] using hnp)

/-- Whole-subroutine trace for `ADDMOD`: from the entry `[pa, pb, pd, ret]` to
the fall-through entry of `CSUB`, with the sum limbs in the `t` block and the
carry stored at `TN`. -/
def gasSteps_addmod (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (amEntryState s memory pa pb pd ret rest)
      (csEntryState s (MachineState.writeBytes (amStep memory pa pb n n).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224)
        pd ret rest) := by
  have hnn : n - 1 + 1 = n := by omega
  exact Challenge.EvmProof.GasSteps.cast
    ((((gasSteps_amEntry s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
          hn hpa hpaFit hpb hpbFit hs32 htl).trans
        (gasSteps_amLoop s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
          hn32 hpa hpaFit hpb hpbFit)).trans
      (gasSteps_amExit s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
        hn hn32 hpa hpaFit hpb hpbFit)).trans
      (gasSteps_amTailStep s memory pa pb n (n - 1 + 1) pd ret rest hcap hcode hfork
        hrun hnp hact))
    rfl (by rw [hnn])

def gasSteps_csEntry (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (hn8 : n ≠ 8) (hn4 : n ≠ 4)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord memory 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csLoopState s memory n 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csGenericPath
    (by simpa [csEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [csEntryState, State.fork] using hfork)
    (run_csEntry s memory n pdst ret rest hcap hrun hcode hs32 hn8 hn4 hact hn hn32 hml htl)
    (by simpa [csEntryState] using hrun)
    (by simpa [csEntryState, State.fork] using hnp)

def gasSteps_csIteration (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j + 1 < n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n j pdst ret rest)
      (csLoopState s memory n (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1683
    (by simpa [csLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [csLoopState, State.fork] using hfork)
    (run_csLoopBody s memory n j pdst ret rest hcap hrun hcode hact hj hn32)
    (by simpa [csLoopState] using hrun)
    (by simpa [csLoopState, State.fork] using hnp)

def gasSteps_csLoop (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n 0 pdst ret rest)
      (csLoopState s memory n (n - 1) pdst ret rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (n - 1) fun i hi =>
    gasSteps_csIteration s memory n i pdst ret rest hcap hcode hfork hrun hnp hact
      (by omega) hn32

def gasSteps_csExit (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n (n - 1) pdst ret rest)
      (csTailState s memory n (n - 1 + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1683
    (by simpa [csLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [csLoopState, State.fork] using hfork)
    (run_csLoopExit s memory n (n - 1) pdst ret rest hcap hrun hcode hact
      (by omega) hn32)
    (by simpa [csLoopState] using hrun)
    (by simpa [csLoopState, State.fork] using hnp)

def gasSteps_csTailStep (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory n j).memory 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (hsrcFit : (csSrc memory n j).toNat + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (csTailState s memory n j pdst ret rest)
      (csReturnedState s memory n j pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1724
    (by simpa [csTailState, Artifact.submissionArtifact] using hcode)
    (by simpa [csTailState, State.fork] using hfork)
    (run_csTail s memory n j pdst ret rest hcap hrun hcode hact hn hn32 hjump hs32
      hdstFit hsrcFit)
    (by simpa [csTailState] using hrun)
    (by simpa [csTailState, State.fork] using hnp)

-- Keep earlier limb states opaque while checking each explicit recursive step.
attribute [local irreducible] csStep

end Challenge.Modexp.Submission.Proofs.Fast.Csub
