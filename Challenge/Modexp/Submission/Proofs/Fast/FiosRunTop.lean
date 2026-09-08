import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.FiosPC
import Challenge.Modexp.Submission.Proofs.Fast.FiosBlocks
import Challenge.Modexp.Submission.Proofs.Fast.FiosDefs
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunA
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunB
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunC1_1
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunC1_2
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunC2_1
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunC2_2

/-
FiosRun.lean -- the value model, states, block reductions and loop certificates for
`artifact/fios-k9.hex`.  Supersedes FiosEvm.lean sections 2-5; keep that file as the
design note.

THE MAIN FINDING, and it makes this whole layer small:

  The engine's fused body is LITERALLY TWO OF `Monpro`'s EXISTING MAC STEPS.
  `Monpro.lean` already says "Both CIOS limb loops execute the same instruction
  sequence" and gives

      Monpro.mulHi   x y     = UInt256.mulMod x y maxWord - (x * y + lt (mulMod x y maxWord) (x * y))
      Monpro.macSum  x y t c = c + (t + x * y)
      Monpro.macCarry x y t c = lt (c + (t + x*y)) c + (lt (t + x*y) t + mulHi x y)
      Monpro.macSpec x y t c : (macCarry …).toNat * 2^256 + (macSum …).toNat
                                 = t.toNat + x.toNat * y.toNat + c.toNat

  I checked the TERM ORDER against the emitted opcodes, not just the value:
    * `MUL` pops the memory limb then the multiplier, so it is `x * y` with x the
      loaded limb -- `mulHi`'s own convention.
    * `t + x*y` and then `c + (t + x*y)` are the orders `add3` and `DUP4 ADD` produce.
    * `macCarry`'s two `lt`s are the `DUP3 LT` and `DUP4 LT` in that order.
  So the fused body is
      u  = macSum  b_j a_i t_j C1        C1' = macCarry b_j a_i t_j C1
      v  = macSum  N_j m   u   C2        C2' = macCarry N_j m   u   C2
  and NO new value function is needed anywhere.  `macSpec` applied twice is exactly
  `Fios.two_split` from FIOS_MATH.lean, one level down.

ADDRESSES -- all four verified against a running trace (n=4, pa=pb=5120, j=0,1,2):
      p_t   = 8224 + 32 * (n - j - 1)          reads t[j+1]
      p_b   = pa   + 32 * (n - j - 2)          reads b[j+1]
      p_n   =        32 * (n - j - 2)          reads N[j+1]
      store = 8256 + 32 * (n - j - 1)          writes t[j]

CONFIDENCE MARKERS: every step I am not certain of carries `-- ?N` and is listed at the
bottom.  Compile those first.
-/
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Fios

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero


/-! ## 6.  Wrappers and loop certificates

THE UNIFORM BINDER LIST.  Every `run_*` and every `gasSteps_*` in this file takes

    (s mem n pa pb) (pdst ret) (rest) (i j as needed)
    (hcap : rest.length ≤ 1000) hcode hfork hrun hnp
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)

and passes it on verbatim as `hcap hcode hfork hrun hnp hact hn2 hn32 hpa hpaFit hpb
hpbFit`.  `run_*` drops `hfork` and `hnp` (the soundness wrapper consumes those), and
the block-local `hj`/`hi` are appended.  Generating the other eleven from
`gasSteps_BodyA` below is then purely mechanical.

STYLE NOTE, after the paren bug at line 403: the deep nestings are split into named
intermediate `def`s, none more than two `.trans` deep.  A wrong parenthesis in a
four-level chain is an arity error reported a hundred lines from its cause. -/

/-- **The wrapper template.**  Generate the other eleven by substituting the block name,
the PRE/POST pair, and the `run_*` name; nothing else varies. -/
def gasSteps_BodyA (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosBody s mem n pa pb pdst ret rest i j)
      (fiosBodyA s mem n pa pb pdst ret rest i j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyA hcode hfork
      (run_BodyA s mem n pa pb i j pdst ret rest hcap hcode hrun hact hn2 hn32 hpa
        hpaFit hpb hpbFit hj hi) hrun hnp

def gasSteps_stub1379 (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192) :
    Challenge.EvmProof.GasSteps
      (Monpro.mpEntryState s mem pa pb pdst ret rest)
      (fiosEntry s mem pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosStub hcode hfork
      (run_stub1379 s mem n pa pb pdst ret rest hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit) hrun hnp

def gasSteps_Setup (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hcds : s.executionEnv.calldata.size < 2 ^ 256) :
    Challenge.EvmProof.GasSteps
      (fiosEntry s mem pa pb pdst ret rest)
      (fiosRow s (Monpro.mpZeroed s mem n) n pa pb pdst ret rest 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosSetup hcode hfork
      (run_Setup s mem n pa pb pdst ret rest hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hs32 hml htl hcds) hrun hnp

def gasSteps_Row1 (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosRow s mem n pa pb pdst ret rest i)
      (fiosRowA s mem n pa pb pdst ret rest i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosRow1 hcode hfork
      (run_Row1 s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_Row2 (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosRowA s mem n pa pb pdst ret rest i)
      (fiosRowB s mem n pa pb pdst ret rest i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosRow2 hcode hfork
      (run_Row2 s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_Row3 (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosRowB s mem n pa pb pdst ret rest i)
      (fiosRowC s mem n pa pb pdst ret rest i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosRow3 hcode hfork
      (run_Row3 s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_Row4 (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosRowC s mem n pa pb pdst ret rest i)
      (fiosBody s mem n pa pb pdst ret rest i 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosRow4 hcode hfork
      (run_Row4 s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_BodyB (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosBodyA s mem n pa pb pdst ret rest i j)
      (fiosBodyB s mem n pa pb pdst ret rest i j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyB hcode hfork
      (run_BodyB s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hj hi) hrun hnp

def gasSteps_BodyC (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosBodyB s mem n pa pb pdst ret rest i j)
      (fiosBodyC s mem n pa pb pdst ret rest i j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyC hcode hfork
      (run_BodyC s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hj hi) hrun hnp

def gasSteps_BodyD (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosBodyC s mem n pa pb pdst ret rest i j)
      (fiosBodyD s mem n pa pb pdst ret rest i j) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyD hcode hfork
      (run_BodyD s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hj hi) hrun hnp

def gasSteps_BodyE_taken (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) (hjp : j + 2 < n) :
    Challenge.EvmProof.GasSteps
      (fiosBodyD s mem n pa pb pdst ret rest i j)
      (fiosBody s mem n pa pb pdst ret rest i (j + 1)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyE hcode hfork
      (run_BodyE_taken s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hj hi hjp) hrun hnp

def gasSteps_BodyE_exit (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    Challenge.EvmProof.GasSteps
      (fiosBodyD s mem n pa pb pdst ret rest i (n - 2))
      (fiosTail s mem n pa pb pdst ret rest i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosBodyE hcode hfork
      (run_BodyE_exit s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_Tail_taken (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i + 1 < n) :
    Challenge.EvmProof.GasSteps
      (fiosTail s mem n pa pb pdst ret rest i)
      (fiosRow s mem n pa pb pdst ret rest (i + 1)) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosTail hcode hfork
      (run_Tail_taken s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit hi) hrun hnp

def gasSteps_Tail_exit (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192) :
    Challenge.EvmProof.GasSteps
      (fiosTail s mem n pa pb pdst ret rest (n - 1))
      (fiosDone s mem n pa pb pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosTail hcode hfork
      (run_Tail_exit s mem n pa pb pdst ret rest hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit) hrun hnp

def gasSteps_Exit (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192) :
    Challenge.EvmProof.GasSteps
      (fiosDone s mem n pa pb pdst ret rest)
      (Csub.csEntryState s (rowsMem mem pa pb n n) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blkFiosExit hcode hfork
      (run_Exit s mem n pa pb pdst ret rest hcap hcode hrun hact hn2 hn32 hpa hpaFit hpb hpbFit) hrun hnp

def bodyFamily (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) (j : Nat) : State :=
  fiosBody s mem n pa pb pdst ret rest i j

def rowFamily (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  fiosRow s mem n pa pb pdst ret rest i

section Chain

-- Section-scoped, and deliberately NOT the `... in` form: `set_option X in` binds
-- to the NEXT declaration, and a `variable` command is not one, so the `in` form
-- never reached the block the warnings are attributed to.  A bare `set_option`
-- inside the section holds until `end Chain`, which is the scope that contains the
-- `variable` block, the `include`, and every wrapper that consumes them.
set_option linter.unusedVariables false


variable (s : State) (mem : ByteArray) (p pa pb : Nat) (pdst ret : UInt256)
  (rest : List UInt256)
  (hcap : rest.length ≤ 1000)
  (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
  (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)
  (hact : 296 ≤ s.activeWords.toNat)
  (hn32 : p + 2 ≤ 32)
  (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
  (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)

-- `variable`s that are propositions are only auto-included where syntactically
-- referenced; these are referenced only inside the wrappers this section calls, so they
-- must be included explicitly.  This is the `include` mechanism, not a linter setting --
-- which is why `set_option linter.unusedVariables false` did nothing.
include hcap hcode hfork hrun hnp hact hn32 hpa hpaFit hpb hpbFit

/-- The four memory-pure blocks of one fused iteration. -/
def gasSteps_bodyABCD (i j : Nat) (hj : j + 1 < p + 2) (hi : i < p + 2) :
    Challenge.EvmProof.GasSteps
      (fiosBody s mem (p + 2) pa pb pdst ret rest i j)
      (fiosBodyD s mem (p + 2) pa pb pdst ret rest i j) :=
  ((gasSteps_BodyA s mem (p + 2) pa pb pdst ret rest i j hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hj hi).trans
      (gasSteps_BodyB s mem (p + 2) pa pb pdst ret rest i j hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit hj hi)).trans
    ((gasSteps_BodyC s mem (p + 2) pa pb pdst ret rest i j hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit hj hi).trans
      (gasSteps_BodyD s mem (p + 2) pa pb pdst ret rest i j hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit hj hi))

/-- One fused iteration that branches back. -/
def gasSteps_bodyIteration (i : Nat) (hi : i < p + 2) (j : Nat) (hj : j < p) :
    Challenge.EvmProof.GasSteps
      (bodyFamily s mem (p + 2) pa pb pdst ret rest i j)
      (bodyFamily s mem (p + 2) pa pb pdst ret rest i (j + 1)) :=
  (gasSteps_bodyABCD s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32
      hpa hpaFit hpb hpbFit i j (by omega) hi).trans
    (gasSteps_BodyE_taken s mem (p + 2) pa pb pdst ret rest i j hcap hcode hfork hrun
      hnp hact (by omega) hn32 hpa hpaFit hpb hpbFit (by omega) hi (by omega))

/-- The whole fused loop of one row: `p` back-branching iterations, then the final one,
which falls through to the tail. -/
def gasSteps_bodyLoop (i : Nat) (hi : i < p + 2) :
    Challenge.EvmProof.GasSteps
      (bodyFamily s mem (p + 2) pa pb pdst ret rest i 0)
      (fiosTail s mem (p + 2) pa pb pdst ret rest i) :=
  (Challenge.EvmProof.GasSteps.iterateBounded
      (I := bodyFamily s mem (p + 2) pa pb pdst ret rest i) p
      (fun j hj => gasSteps_bodyIteration s mem p pa pb pdst ret rest hcap hcode hfork
        hrun hnp hact hn32 hpa hpaFit hpb hpbFit i hi j hj)).trans
    ((gasSteps_bodyABCD s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32
        hpa hpaFit hpb hpbFit i p (by omega) hi).trans
      (gasSteps_BodyE_exit s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit hi))

/-- The four blocks of the row peel. -/
def gasSteps_row1234 (i : Nat) (hi : i < p + 2) :
    Challenge.EvmProof.GasSteps
      (fiosRow s mem (p + 2) pa pb pdst ret rest i)
      (fiosBody s mem (p + 2) pa pb pdst ret rest i 0) :=
  ((gasSteps_Row1 s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hi).trans
      (gasSteps_Row2 s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hi)).trans
    ((gasSteps_Row3 s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hi).trans
      (gasSteps_Row4 s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hi))

/-- One row that branches back. -/
def gasSteps_rowIteration (i : Nat) (hi : i < p + 1) :
    Challenge.EvmProof.GasSteps
      (rowFamily s mem (p + 2) pa pb pdst ret rest i)
      (rowFamily s mem (p + 2) pa pb pdst ret rest (i + 1)) :=
  (gasSteps_row1234 s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32 hpa
      hpaFit hpb hpbFit i (by omega)).trans
    ((gasSteps_bodyLoop s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32
        hpa hpaFit hpb hpbFit i (by omega)).trans
      (gasSteps_Tail_taken s mem (p + 2) pa pb pdst ret rest i hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit (by omega)))

/-- The last row, which falls through to the exit block. -/
def gasSteps_rowLast :
    Challenge.EvmProof.GasSteps
      (rowFamily s mem (p + 2) pa pb pdst ret rest (p + 1))
      (fiosDone s mem (p + 2) pa pb pdst ret rest) :=
  (gasSteps_row1234 s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32 hpa
      hpaFit hpb hpbFit (p + 1) (by omega)).trans
    ((gasSteps_bodyLoop s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32
        hpa hpaFit hpb hpbFit (p + 1) (by omega)).trans
      (gasSteps_Tail_exit s mem (p + 2) pa pb pdst ret rest hcap hcode hfork hrun hnp
        hact (by omega) hn32 hpa hpaFit hpb hpbFit))

/-- All `p + 2` rows. -/
def gasSteps_allRows :
    Challenge.EvmProof.GasSteps
      (rowFamily s mem (p + 2) pa pb pdst ret rest 0)
      (fiosDone s mem (p + 2) pa pb pdst ret rest) :=
  (Challenge.EvmProof.GasSteps.iterateBounded
      (I := rowFamily s mem (p + 2) pa pb pdst ret rest) (p + 1)
      (fun i hi => gasSteps_rowIteration s mem p pa pb pdst ret rest hcap hcode hfork
        hrun hnp hact hn32 hpa hpaFit hpb hpbFit i hi)).trans
    (gasSteps_rowLast s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact hn32
      hpa hpaFit hpb hpbFit)

/-- **The whole engine**, pc 1939 to the untouched `Csub` tail at pc 2637.

The stub step is `gasSteps_stub1379`, over `blk1379` from the regenerated
`Paths/P7.lean` — NOT a `blkFiosStub`, which we dropped so there is exactly one record
for those three instructions.  Its pc table is the tree's existing `fastPC10`. -/
def gasSteps_fios
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hcds : s.executionEnv.calldata.size < 2 ^ 256) :
    Challenge.EvmProof.GasSteps
      (Monpro.mpEntryState s mem pa pb pdst ret rest)
      (Csub.csEntryState s
        (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) pdst ret rest) :=
  ((gasSteps_stub1379 s mem (p + 2) pa pb pdst ret rest hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit).trans
      (gasSteps_Setup s mem (p + 2) pa pb pdst ret rest hcap hcode hfork hrun hnp hact
        (by omega) hn32 hpa hpaFit hpb hpbFit hs32 hml htl hcds)).trans
    ((gasSteps_allRows s (Monpro.mpZeroed s mem (p + 2)) p pa pb pdst ret rest hcap
        hcode hfork hrun hnp hact hn32 hpa hpaFit hpb hpbFit).trans
      (gasSteps_Exit s (Monpro.mpZeroed s mem (p + 2)) (p + 2) pa pb pdst ret rest hcap
        hcode hfork hrun hnp hact (by omega) hn32 hpa hpaFit hpb hpbFit))

end Chain

/-! ## 7.  The witness swap

`Subroutines` changes in exactly two fields, and `mpMem` only in one component:

    -- before
    mpMem pa pb pd mem =
      Csub.csResultMemory (Monpro.rowsMem (Monpro.mpZeroed s mem n) pa pb n n) n pd
    -- after
    mpMem pa pb pd mem = Fios.fiosMem s n pa pb pd mem
                       = Csub.csResultMemory (Fios.rowsMem (Monpro.mpZeroed s mem n)
                                                n pa pb n) n pd

  * `monpro` -- same statement, same `tail.length ≤ 1000` binder (which already covers
    the engine's peak of `rest + 20`: 1020 < 1024); witness becomes `gasSteps_fios`.
  * `amMem`, `amFrame`, `addmod`, `mpFrame` -- untouched.
  * `SubSpec.mpValue` -- statement unchanged; proof becomes `Fios.fios_montMul` with
    `Fios.fios_row_eq` supplying `hrow` per row and `Fios.top_limb_le_one` supplying
    `Csub.csub_correct`'s `htn1`.
  * `SubSpec.mpFrame`, `SubSpec.mpMinv` -- unchanged.  The engine's only writes are the
    `CALLDATACOPY` at 0x2000 of size 32n+64 and `MSTORE`s in [0x2020, 0x2020+32n], all
    strictly below 0x2480, and the footprint is a STRICT SUBSET of the old one: CIOS
    wrote `t[n+1]` at 0x2000 on every row, the fused tail folds both carries straight
    into `t[n]` and never touches 0x2000 after the zeroing.

## 8.  The steps I doubt -- compile these first

  ?1  `UInt256.gt a b` as the spelling of the `GT` result.  `Csub.run_amLoopBody` puts
      `UInt256.gt` in its simp set, so the constructor exists, but I have not seen it
      used to BUILD a value.  If it is wrong the fix is `UInt256.lt b a`.
      Occurs in `peelC2` and `rowMem`.
  ?2  `MachineState.readWord W.mem (8224 + 32*n - 32*n)` is my clumsy way of writing
      `readWord W.mem 8224` (= t[n]).  Simplify to the literal 8224 if it type-checks;
      I wrote it long only to make the provenance obvious.
  ?3  the row tail writes t[n-1] at 8256 and t[n] at 8224; I am confident of the
      addresses (they are the fixed slots `T_NM1`/`T_N`) but not of the nesting order of
      the two `writeBytes`.
  ?4  RESOLVED.  Only the `s`-taking `Monpro.mpZeroed s mem n` exists, so `rowsMem`
      now starts from `mem` and the caller applies the zeroing -- exactly what
      `Monpro.rowsMem` does.  `Fios.monproMem` in FiosMem.lean supplies it.
  ?5  `fiosTail := fiosBody … (n-1)` reuses the body state at pc 5653, but the tail
      block starts at pc 5838.  The stack IS identical (the loop fell through with p_t
      on top), so this should be a `pc`-only update; write it out as its own record if
      the definitional unfolding is awkward.
  ?6  RESOLVED by the compiler: `fastPC10` is defined at `Defs.lean:531` covering
      1377..1416, is also cited by `Double.lean:222`, and Monpro compiled clean under
      `warningAsError` after the deletion.  Use `fastPC10` for `blk1379`.
  ?7  RESOLVED, in code, and the first attempt was wrong in a way worth recording:
      `ptrAt_add_const` shifted the BASE by the delta, giving `8224 + 32n + dBN`, which
      is not `< 2 ^ 256` because `dBN` carries the wrap.  The literal-vs-`2 ^ 256`
      mismatch you saw was real but downstream of that.  The working route is the exact
      Nat identity `ptrAt (8224+32n) (j+1) + dBN pa n = ptrAt (pa+32n) (j+2)`
      (`ptrAt_dB`), which lands on the b array's own base.  Same for `dN` at base
      `32*n`.  Then the FIRST compile showed the bridge had to be stated at the
      raw-Nat modular level, not through `UInt256.toNat`: see `bAddr_mod`.  NOTE for
      the generator: `dBN`/`dNN` must stay FOLDED in the simp set -- the goal carries
      `dBN pa n` as an application, and unfolding it stops the bridge matching.
  ?H  `ptrAt_dB`/`ptrAt_dN` close with `omega` after `simp only [Csub.ptrAt, dBN]`.
      That leaves omega a linear goal whose coefficients include the 78-digit `K32`
      literal; it should be linear and fine, but if omega baulks the fallback is to
      `rw [Nat.mul_sub]` on `(j+1) * K32` first, as `Csub.ptrAt_toNat` does internally.
-/

end Challenge.Modexp.Submission.Proofs.Fast.Fios


