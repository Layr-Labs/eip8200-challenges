import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Pack
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteBootstrap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CoreRight1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentBootstrapBridge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# The specialised pad-only compressor, end to end

The specialised prefix in the padding windows at 6154 and 7046 executes the
generic compressor's bootstrap, right-line rounds, pack and paired rounds 0..12,
with each omitted schedule read replaced by the zero it returns on the fast
pad-only table, and then rejoins the generic compressor at round 13.  Every
intermediate state is the corresponding generic state with only its program
counter relocated, so the block ends in the generic suffix state.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Body
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon StaggerCoreModel
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero PadWord0)
open HoistedInherited.StaggerPersistentBootstrapBridge (initial initial_eq input input_eq output_eq)

def rightInitial (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4602, stack := stack s.memory h4 [ .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .e ] q q (UInt256.ofNat 1352829926) rho}

def rightFinal (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4674, stack := stack s.memory h4 [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (right1 s.memory (right0 s.memory q)) q (UInt256.ofNat 1352829926) rho}

def gasSteps_right (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (halias : rho[2]? = some q.b) (haliasC : rho[1]? = some q.c)
    (haliasD : rho[0]? = some q.d) (haliasA : rho[3]? = some q.a) (hh4 : h4 = q.e)
    (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (rightInitial s h4 q rho) (rightFinal s h4 q rho) := by
  have g0 := PadCopy.CoreRight0.gasSteps s h4 q q rho hs halias haliasC haliasD haliasA hh4 hr ha hcode hfork hnp hz
  have g1 := PadCopy.CoreRight1.gasSteps s h4 (right0 s.memory q) q rho hs halias hh4 hr ha hcode hfork hnp hz
  exact g0.trans g1

def entry (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4601, stack := StaggerPersistentFrame.frame h off limit rho}

def gasSteps_bootstrap (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 900) (hr : s.halt = .Running)
    (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (entry s h off limit rho)
      (rightInitial s (Word.ofUInt32 h.h4) (initial h)
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have g := PadCopy.SiteBootstrap.gasSteps s (input h off limit) rho hs hr ha hcode hfork hnp hz
  rw [input_eq, output_eq] at g
  exact g

open HoistedInherited.StaggerPersistentPackBridge (suffix) in
def gasSteps_coreBody (s : State) (h : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) (hw : PadWord0 s.memory) :
    GasSteps (rightInitial s h.e h (suffix h off limit rho))
      (PadCopy.FullPrefix.suffixState s h.e (StaggerCoreModel.paired s.memory h) (suffix h off limit rho)) := by
  have hstack : (suffix h off limit rho).length ≤ 900 := by
    simp only [suffix, JointRightPackModel.suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have gr := gasSteps_right s h.e h (suffix h off limit rho)
    hstack (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hr ha hcode hfork hnp hz
  have gp := PadCopy.Pack.gasSteps s h (StaggerCoreModel.right1 s.memory (StaggerCoreModel.right0 s.memory h))
    off limit rho (by omega) hr ha hcode hfork hnp hz
  have gc := PadCopy.FullPrefix.gasSteps_pairedSuffix s h.e
    (StaggerCoreModel.pair h (StaggerCoreModel.prologue s.memory h)) h (suffix h off limit rho)
    hstack hr ha hcode hfork hnp hz hw
  exact gr.trans (gp.trans gc)

def gasSteps_body (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 894) (hr : s.halt = .Running)
    (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) (hw : PadWord0 s.memory) :
    GasSteps (entry s h off limit rho)
      (PadCopy.FullPrefix.suffixState s (Word.ofUInt32 h.h4)
        (StaggerCoreModel.paired s.memory (initial h))
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have gb := gasSteps_bootstrap s h off limit rho (by omega) hr (by omega) hcode hfork hnp hz
  have gc := gasSteps_coreBody s (initial h) off limit rho hs hr ha hcode hfork hnp hz hw
  have he : (initial h).e = Word.ofUInt32 h.h4 := by rw [initial_eq]
  have hsuf : HoistedInherited.StaggerPersistentPackBridge.suffix (initial h) off limit rho =
      StaggerPersistentFrame.coreRest h off limit rho := by
    rw [initial_eq]
    rfl
  rw [he, hsuf] at gc
  exact gb.trans gc

#print axioms gasSteps_body
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Body
