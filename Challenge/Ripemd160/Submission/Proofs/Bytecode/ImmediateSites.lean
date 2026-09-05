import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateIteration

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateIteration

/-- Left and right descriptors re-exported by the site module. -/
def leftSite (i : Nat) : WrapperSite := ImmediateIteration.leftSite i

def rightSite (i : Nat) : WrapperSite := ImmediateIteration.rightSite i

inductive Lane where
  | left
  | right
deriving DecidableEq, Repr

/-- Concrete metadata for one immediate wrapper and its return target. -/
structure ImmediateSiteData where
  lane : Lane
  round : Nat
  site : WrapperSite
  returnIndex : Nat
  returnPC : Nat
  nextIndex : Option Nat
deriving Repr

def leftData (i : Nat) : ImmediateSiteData :=
  { lane := .left
    round := i
    site := leftSite i
    returnIndex := 997 + 9 * i + 8
    returnPC := Artifact.submissionArtifact.instructionPC (997 + 9 * i + 8)
    nextIndex := if i = 79 then none else some (997 + 9 * (i + 1)) }

def rightData (i : Nat) : ImmediateSiteData :=
  let start := if i = 79 then 2429 else 1717 + 9 * i
  let returnIndex := if i = 79 then 563 else start + 8
  { lane := .right
    round := i
    site := rightSite i
    returnIndex := returnIndex
    returnPC := Artifact.submissionArtifact.instructionPC returnIndex
    nextIndex := if i = 79 then none else some (1717 + 9 * (i + 1)) }

def leftNextSite (i : Nat) : WrapperSite :=
  if i = 79 then (rightData 0).site else (leftData (i + 1)).site

/-- All 160 concrete sites, in execution order. -/
def leftSiteData : List ImmediateSiteData :=
  (List.range 80).map leftData

def rightSiteData : List ImmediateSiteData :=
  (List.range 80).map rightData

def allImmediateSites : List ImmediateSiteData :=
  leftSiteData ++ rightSiteData

theorem leftData_site (i : Nat) : (leftData i).site = leftSite i := by rfl

theorem rightData_site (i : Nat) : (rightData i).site = rightSite i := by rfl

theorem leftData_returnIndex (i : Nat) :
    (leftData i).returnIndex = 997 + 9 * i + 8 := by rfl

theorem rightData_returnIndex (i : Nat) :
    (rightData i).returnIndex = if i = 79 then 563 else 1717 + 9 * i + 8 := by
  by_cases hi : i = 79 <;> simp [rightData, hi]

theorem leftData_returnPC (i : Nat) :
    (leftData i).returnPC = Artifact.submissionArtifact.instructionPC
      (997 + 9 * i + 8) := by rfl

theorem rightData_returnPC (i : Nat) :
    (rightData i).returnPC = Artifact.submissionArtifact.instructionPC
      (if i = 79 then 563 else 1717 + 9 * i + 8) := by
  by_cases hi : i = 79 <;> simp [rightData, hi]

theorem leftData_round (i : Nat) : (leftData i).round = i := by rfl

theorem rightData_round (i : Nat) : (rightData i).round = i := by rfl

theorem leftData_k (i : Nat) :
    (leftData i).site.k = UInt256.ofNat (ImmediateIteration.leftConstant (i / 16)) := by
  rfl

theorem rightData_k (i : Nat) :
    (rightData i).site.k = UInt256.ofNat (ImmediateIteration.rightConstant (i / 16)) := by
  rfl

theorem leftData_rotation (i : Nat) :
    (leftData i).site.rotation = UInt256.ofNat
      (EvmSemantics.Crypto.Ripemd160.s[i]!) := by rfl

theorem rightData_rotation (i : Nat) :
    (rightData i).site.rotation = UInt256.ofNat
      (EvmSemantics.Crypto.Ripemd160.sP[i]!) := by rfl

theorem leftData_wordIndex (i : Nat) :
    (leftData i).site.wordIndex = UInt256.ofNat
      (EvmSemantics.Crypto.Ripemd160.r[i]!) := by rfl

theorem rightData_wordIndex (i : Nat) :
    (rightData i).site.wordIndex = UInt256.ofNat
      (EvmSemantics.Crypto.Ripemd160.rP[i]!) := by rfl

theorem leftData_group (i : Nat) : (leftData i).site.j = UInt256.ofNat (i / 16) := by
  rfl

theorem rightData_group (i : Nat) :
    (rightData i).site.j = UInt256.ofNat (4 - i / 16) := by
  rfl

theorem leftData_base (i : Nat) : (leftData i).site.base = UInt256.ofNat 0xc0 := by
  rfl

theorem rightData_base (i : Nat) : (rightData i).site.base = UInt256.ofNat 0x160 := by
  rfl

/-- Exact wrapper and return-target certificate for one concrete site. -/
structure ImmediateSiteCertificate (data : ImmediateSiteData) : Prop where
  wrapper : WrapperSiteCertificate data.site
  returnInstr : Artifact.submissionArtifact.instructions[data.returnIndex]? =
    some (.op .JUMPDEST)
  returnPC : Artifact.submissionArtifact.instructionPC data.returnIndex = data.returnPC
  returnMatches : data.site.ret.toNat = data.returnPC
  returnWellFormed : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op .JUMPDEST)

def returnDestPath {data : ImmediateSiteData} (h : ImmediateSiteCertificate data) :
    List Located :=
  [⟨data.returnIndex, .op .JUMPDEST, h.returnInstr, h.returnWellFormed⟩]

def immediateRoundReturned (data : ImmediateSiteData) (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) : State :=
  RoundTrace.roundReturned s data.site.base data.site.j.toNat data.site.wordIndex
    data.site.rotation data.site.k data.site.ret ([messageOffset, outerReturn] ++ rest)

theorem run_returnDest {data : ImmediateSiteData}
    (h : ImmediateSiteCertificate data) (s : State)
    (hpc : s.pc = data.site.ret) (hstack : s.stack.length < 1024)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (returnDestPath h) s =
      some {s with pc := s.pc.succ} := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC data.returnIndex := by
    calc
      s.pc.toNat = data.site.ret.toNat := by rw [hpc]
      _ = data.returnPC := h.returnMatches
      _ = Artifact.submissionArtifact.instructionPC data.returnIndex := h.returnPC.symm
  simp [returnDestPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hpcNat, hstack, hrun, Challenge.EvmProof.Word.succ_ofNat]

def gasSteps_returnDest {data : ImmediateSiteData}
    (h : ImmediateSiteCertificate data) (s : State)
    (hpc : s.pc = data.site.ret) (hstack : s.stack.length < 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s {s with pc := s.pc.succ} := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (returnDestPath h)
  · simpa [Artifact.submissionArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_returnDest h s hpc hstack hrun
  · exact hrun
  · exact hnp

def gasStepsImmediateRound {data : ImmediateSiteData}
    (h : ImmediateSiteCertificate data) (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (hj : data.site.j.toNat < 5) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wrapperEntryAt data.site s messageOffset outerReturn rest)
      (immediateRoundReturned data s messageOffset outerReturn rest) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hvalid : Decode.isValidJumpDest submissionBytecode data.site.ret.toNat = true := by
    rw [h.returnMatches]
    rw [← h.returnPC]
    exact Artifact.submissionArtifact.isValidJumpDest_index data.returnIndex h.returnInstr
  have gw := gasSteps_wrapper_site data.site h.wrapper s messageOffset outerReturn rest
    hstack hcode hfork hrun hnp
  have gr := RoundTrace.gasSteps_round s data.site.base data.site.j.toNat hj
    data.site.wordIndex data.site.rotation data.site.k data.site.ret
    ([messageOffset, outerReturn] ++ rest) hstackRound hcode hfork hrun hnp hvalid
  have heq : wrapperRoundEntryAt data.site s messageOffset outerReturn rest =
      RoundTrace.roundEntry s data.site.base data.site.j.toNat data.site.wordIndex
        data.site.rotation data.site.k data.site.ret
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gw.trans (Challenge.EvmProof.GasSteps.cast gr heq.symm rfl)

/-- Alias used by the iteration modules. -/
def runImmediateRound := @gasStepsImmediateRound

def gasStepsReturnToNext {data : ImmediateSiteData}
    (h : ImmediateSiteCertificate data) (next : WrapperSite)
    (hnext : data.site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC next.startIndex))
    (s : State) (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (immediateRoundReturned data s messageOffset outerReturn rest)
      (wrapperEntryAt next (immediateRoundReturned data s messageOffset outerReturn rest)
        messageOffset outerReturn rest) := by
  let q := immediateRoundReturned data s messageOffset outerReturn rest
  have hqstack : q.stack.length < 1024 := by
    change ([messageOffset, outerReturn] ++ rest).length < 1024
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hqcode : q.executionEnv.code = submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hqfork : q.fork = .Osaka := by
    change s.fork = .Osaka
    exact hfork
  have hqrun : q.halt = .Running := by
    change s.halt = .Running
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false
    exact hnp
  have g := gasSteps_returnDest h q rfl hqstack hqcode hqfork hqrun hqnp
  have hqpc : q.pc = data.site.ret := by rfl
  have hqstack' : q.stack = [messageOffset, outerReturn] ++ rest := by rfl
  have heq : {q with pc := q.pc.succ} =
      wrapperEntryAt next q messageOffset outerReturn rest := by
    simp [wrapperEntryAt, hqpc, hqstack', hnext]
  exact g.cast rfl heq

def gasStepsImmediateSiteToNext {data : ImmediateSiteData}
    (h : ImmediateSiteCertificate data) (next : WrapperSite)
    (hnext : data.site.ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC next.startIndex))
    (s : State) (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (hj : data.site.j.toNat < 5) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wrapperEntryAt data.site s messageOffset outerReturn rest)
      (wrapperEntryAt next (immediateRoundReturned data s messageOffset outerReturn rest)
        messageOffset outerReturn rest) := by
  have gRound := gasStepsImmediateRound h s messageOffset outerReturn rest hj hstack
    hcode hfork hrun hnp
  have gNext := gasStepsReturnToNext h next hnext s messageOffset outerReturn rest
    hstack hcode hfork hrun hnp
  exact gRound.trans gNext

/-- Certificates for the first sixteen concrete left sites. -/
def leftCertificate16 (i : Fin 16) :
    ImmediateSiteCertificate (leftData i.val) := by
  fin_cases i <;>
    refine ⟨
      ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl,
        by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, ⟨by decide, trivial, rfl⟩⟩,
      by rfl, by rfl, by decide, ⟨by decide, trivial, rfl⟩⟩

def leftCertificate0 : ImmediateSiteCertificate (leftData 0) :=
  leftCertificate16 0

def leftSiteCertificate (i : Fin 16) :
    ImmediateSiteCertificate (leftData i.val) :=
  leftCertificate16 i

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites
