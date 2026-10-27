import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Hops
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired5
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired6
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired7
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired8
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired9
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired10
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired12
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired13
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired14
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.CorePaired15
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Prefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired144WordRound StaggerCoreCommon StaggerCoreModel
open StaggerModeSeven (physicalKey)
open StaggerModeSeven (step fold)
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
set_option linter.unusedVariables false
def pcs : Array Nat := #[6327, 6392, 6424, 6460, 7047, 7083, 7114, 7150, 7181, 7216, 7261, 7296, 7341, 9743, 9802, 9857, 9905]
def atRound (s : State) (h4 : UInt256) (i : Nat) (q right : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack s.memory h4 HoistedInherited.StaggerCore.shapes[i]! q right (physicalKey (i-1)) rho}

private theorem step_ordinary (i : Nat) (m : UInt256) (q : WordLane)
    (hm : ¬ StaggerModeSeven.enabled i) (ht : ¬ (i = 75 ∨ i = 76)) :
    step i m q = StaggerAlgorithm.step i m q := by
  rw [StaggerModeSeven.step, if_neg hm, StaggerTerminal75.step, if_neg ht]

private def gasSteps_at0 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 0 q right rho)
      (atRound s h4 (0+1) (step 0 (message s.memory 0) q) right rho) := by
  rw [step_ordinary 0 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired0.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at1 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 1 q right rho)
      (atRound s h4 (1+1) (step 1 (message s.memory 1) q) right rho) := by
  rw [step_ordinary 1 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired1.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at2 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 2 q right rho)
      (atRound s h4 (2+1) (step 2 (message s.memory 2) q) right rho) := by
  rw [step_ordinary 2 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired2.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at3 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 3 q right rho)
      (atRound s h4 (3+1) (step 3 (message s.memory 3) q) right rho) := by
  rw [step_ordinary 3 _ _ (by decide) (by decide)]
  exact (PadCopy.CorePaired3.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz).trans
    (PadCopy.Hops.gasSteps_window s _
      (by simp only [StaggerCoreCommon.stack, List.length_append, List.length_map, List.length_cons,
            List.length_nil]; omega) hr hcode hfork hnp)

private def gasSteps_at4 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 4 q right rho)
      (atRound s h4 (4+1) (step 4 (message s.memory 4) q) right rho) := by
  rw [step_ordinary 4 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired4.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at5 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 5 q right rho)
      (atRound s h4 (5+1) (step 5 (message s.memory 5) q) right rho) := by
  rw [step_ordinary 5 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired5.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at6 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 6 q right rho)
      (atRound s h4 (6+1) (step 6 (message s.memory 6) q) right rho) := by
  rw [step_ordinary 6 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired6.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at7 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 7 q right rho)
      (atRound s h4 (7+1) (step 7 (message s.memory 7) q) right rho) := by
  rw [step_ordinary 7 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired7.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at8 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 8 q right rho)
      (atRound s h4 (8+1) (step 8 (message s.memory 8) q) right rho) := by
  rw [step_ordinary 8 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired8.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at9 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 9 q right rho)
      (atRound s h4 (9+1) (step 9 (message s.memory 9) q) right rho) := by
  rw [step_ordinary 9 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired9.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at10 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 10 q right rho)
      (atRound s h4 (10+1) (step 10 (message s.memory 10) q) right rho) := by
  rw [step_ordinary 10 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired10.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at11 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 11 q right rho)
      (atRound s h4 (11+1) (step 11 (message s.memory 11) q) right rho) := by
  rw [step_ordinary 11 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired11.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

private def gasSteps_at12 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 12 q right rho)
      (atRound s h4 (12+1) (step 12 (message s.memory 12) q) right rho) := by
  rw [step_ordinary 12 _ _ (by decide) (by decide)]
  exact (PadCopy.CorePaired12.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz).trans
    (PadCopy.Hops.gasSteps_extension s _
      (by simp only [StaggerCoreCommon.stack, List.length_append, List.length_map,
            List.length_cons, List.length_nil]; omega) hr hcode hfork hnp)

private def gasSteps_at13 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 13 q right rho)
      (atRound s h4 (13+1) (step 13 (message s.memory 13) q) right rho) := by
  rw [step_ordinary 13 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired13.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz
private def gasSteps_at14 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 14 q right rho)
      (atRound s h4 (14+1) (step 14 (message s.memory 14) q) right rho) := by
  rw [step_ordinary 14 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired14.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz
private def gasSteps_at15 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 15 q right rho)
      (atRound s h4 (15+1) (step 15 (message s.memory 15) q) right rho) := by
  rw [step_ordinary 15 _ _ (by decide) (by decide)]
  exact PadCopy.CorePaired15.gasSteps s h4 q right rho hs hr ha hcode hfork hnp hz

def gasSteps_step (s : State) (h4 : UInt256) (i : Fin 16) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 i.val q right rho)
      (atRound s h4 (i.val+1) (step i.val (message s.memory i.val) q) right rho) := by
  match i with
  | ⟨0, _⟩ => exact gasSteps_at0 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨1, _⟩ => exact gasSteps_at1 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨2, _⟩ => exact gasSteps_at2 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨3, _⟩ => exact gasSteps_at3 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨4, _⟩ => exact gasSteps_at4 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨5, _⟩ => exact gasSteps_at5 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨6, _⟩ => exact gasSteps_at6 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨7, _⟩ => exact gasSteps_at7 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨8, _⟩ => exact gasSteps_at8 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨9, _⟩ => exact gasSteps_at9 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨10, _⟩ => exact gasSteps_at10 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨11, _⟩ => exact gasSteps_at11 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨12, _⟩ => exact gasSteps_at12 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨13, _⟩ => exact gasSteps_at13 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨14, _⟩ => exact gasSteps_at14 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨15, _⟩ => exact gasSteps_at15 s h4 q right rho hs hr ha hcode hfork hnp hz
  | ⟨n+16, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (h4 : UInt256) (n : Nat) (hn : n ≤ 16) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 0 q right rho)
      (atRound s h4 n (fold (message s.memory) n q) right rho) := by
  induction n with
  | zero => exact GasSteps.refl _
  | succ n ih =>
    exact (ih (by omega)).trans
      (gasSteps_step s h4 ⟨n, by omega⟩ (fold (message s.memory) n q) right rho hs hr ha hcode hfork hnp hz)

/-- The specialised prefix ends in the appended block; the hop and the generic
marker leave exactly the generic state at round16. -/
def gasSteps_toGeneric (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (atRound s h4 0 q right rho)
      (HoistedInherited.StaggerCore.atRound s h4 16 (fold (message s.memory) 16 q) right rho) :=
  (gasSteps_prefix s h4 16 (by decide) q right rho hs hr ha hcode hfork hnp hz).trans
    (PadCopy.Hops.gasSteps_rejoin s _
      (by have h16 : HoistedInherited.StaggerCore.shapes[16]!.length ≤ 20 := by decide
          simp only [StaggerCoreCommon.stack, List.length_append, List.length_map]; omega) hr hcode hfork hnp)

#print axioms gasSteps_toGeneric
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Prefix
