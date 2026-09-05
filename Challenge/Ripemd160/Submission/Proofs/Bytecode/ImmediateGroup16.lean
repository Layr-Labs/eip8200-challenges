import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup16

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

/-- State at the start of left wrapper `i`. -/
def leftGroupState (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => wrapperEntryAt (leftData 0).site s messageOffset outerReturn rest
  | i + 1 =>
    wrapperEntryAt (leftData (i + 1)).site
      (immediateRoundReturned (leftData i)
        (leftGroupState s messageOffset outerReturn rest i)
        messageOffset outerReturn rest)
      messageOffset outerReturn rest

def leftGroupFinal (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  leftGroupState s messageOffset outerReturn rest 16

theorem leftGroupState_entry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (i : Nat) :
    wrapperEntryAt (leftData i).site
        (leftGroupState s messageOffset outerReturn rest i)
        messageOffset outerReturn rest =
      leftGroupState s messageOffset outerReturn rest i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [leftGroupState, wrapperEntryAt]

theorem leftGroupState_executionEnv (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) (i : Nat) :
    (leftGroupState s messageOffset outerReturn rest i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hround :
          (immediateRoundReturned (leftData i)
            (leftGroupState s messageOffset outerReturn rest i)
            messageOffset outerReturn rest).executionEnv =
          (leftGroupState s messageOffset outerReturn rest i).executionEnv := by
        rfl
      simp [leftGroupState, wrapperEntryAt, hround, ih]

theorem leftGroupState_halt (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) (i : Nat) :
    (leftGroupState s messageOffset outerReturn rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hround :
          (immediateRoundReturned (leftData i)
            (leftGroupState s messageOffset outerReturn rest i)
            messageOffset outerReturn rest).halt =
          (leftGroupState s messageOffset outerReturn rest i).halt := by
        rfl
      simp [leftGroupState, wrapperEntryAt, hround, ih]

theorem leftNextPC16 (i : Fin 16) :
    (leftData i.val).site.ret.succ =
      UInt256.ofNat
        (Artifact.submissionArtifact.instructionPC (leftData (i.val + 1)).site.startIndex) := by
  fin_cases i <;> decide

def leftGroupStep (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftGroupState s messageOffset outerReturn rest i)
      (leftGroupState s messageOffset outerReturn rest (i + 1)) := by
  let fi : Fin 16 := ⟨i, hi⟩
  let data := leftData i
  let prev := leftGroupState s messageOffset outerReturn rest i
  have hcert : ImmediateSiteCertificate data := by
    simpa [data, fi] using leftCertificate16 fi
  have henv : prev.executionEnv = s.executionEnv := by
    simpa [prev] using leftGroupState_executionEnv s messageOffset outerReturn rest i
  have hcode' : prev.executionEnv.code = submissionBytecode := by
    rw [henv]
    exact hcode
  have hfork' : prev.fork = .Osaka := by
    change prev.executionEnv.fork = .Osaka
    rw [henv]
    exact hfork
  have hrun' : prev.halt = .Running := by
    rw [leftGroupState_halt]
    exact hrun
  have hnp' : Precompile.isPrecompileWithConfig prev.executionEnv.precompileConfig
      prev.executionEnv.fork prev.executionEnv.codeAddr = false := by
    rw [henv]
    exact hnp
  have gRound := gasStepsImmediateRound hcert prev messageOffset outerReturn rest
    (by
      have hi0 : i / 16 = 0 := Nat.div_eq_of_lt hi
      have hgroup : (leftSite i).j = UInt256.ofNat (i / 16) := by rfl
      change (leftSite i).j.toNat < 5
      rw [hgroup]
      simp [hi0])
    hstack hcode' hfork' hrun' hnp'
  have hnextpc : data.site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftData (i + 1)).site.startIndex) := by
    simpa [data, fi] using leftNextPC16 fi
  have gReturn := gasStepsReturnToNext hcert
    (leftData (i + 1)).site hnextpc prev messageOffset outerReturn rest
    hstack hcode' hfork' hrun' hnp'
  have hstart : leftGroupState s messageOffset outerReturn rest i =
      wrapperEntryAt data.site prev messageOffset outerReturn rest := by
    symm
    exact leftGroupState_entry s messageOffset outerReturn rest i
  have hend : wrapperEntryAt (leftData (i + 1)).site
      (immediateRoundReturned data prev messageOffset outerReturn rest)
      messageOffset outerReturn rest =
      leftGroupState s messageOffset outerReturn rest (i + 1) := by
    rfl
  exact (gRound.cast hstart.symm rfl).trans (gReturn.cast rfl hend)

def leftGroup16GasSteps (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftGroupState s messageOffset outerReturn rest 0)
      (leftGroupState s messageOffset outerReturn rest 16) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
  intro i hi
  exact leftGroupStep s messageOffset outerReturn rest i hi hstack
    hcode hfork hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup16
