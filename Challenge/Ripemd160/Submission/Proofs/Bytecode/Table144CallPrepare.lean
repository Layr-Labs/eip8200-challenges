import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Prepare
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CallPrepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Table144Prepare

def template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 1632), .op (.Dup ⟨6, by decide⟩), .op .ADD]

theorem run_template (s : State) (pc : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (hstack : rho.length ≤ 1013)
    (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := PersistentFrame.frame h off limit rho} =
      some {s with
        pc := pcAfter pc template
        stack := UInt256.add off (UInt256.ofNat 1632) :: PersistentFrame.frame h off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp [template, PersistentFrame.frame, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]
  all_goals repeat first | apply And.intro | rfl

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 308).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 308 actual_slice
    (by change 308 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 505 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 308) = UInt256.ofNat 505
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def callState (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 505
    stack := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho}

def gasSteps_call (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (callState s input i h rho) (entryState s input i h rho) := by
  apply PadLift.gasSteps_of_raw site (callState s input i h rho) _ hcode hfork hrun hnp site_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · have hraw := run_template s (UInt256.ofNat 505) h (DriverTrace.blockOffsetWord i)
      (Padding.paddedWord input) rho (by omega) hrun
    have hp : UInt256.add (DriverTrace.blockOffsetWord i) (UInt256.ofNat 1632) =
        UInt256.ofNat (messagePointer i) := by
      have hb := messagePointer_bound input hfit i hi
      change UInt256.ofNat (DriverTrace.blockOffset i) + UInt256.ofNat 1632 = _
      rw [Word.ofNat_add_ofNat (by unfold messagePointer at hb; omega)]
      congr 1
      simp only [messagePointer, Nat.add_comm]
    have hend : pcAfter (UInt256.ofNat 505) template = UInt256.ofNat 510 := by decide
    rw [hp, hend] at hraw
    exact hraw

opaque gasSteps_call_prepare (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (callState s input i h rho) (readyState s input i h rho) :=
  (gasSteps_call s input i h rho hstack hfit hi hcode hfork hrun hnp).trans
    (gasSteps_prepare s input i h rho hstack hfit hi ctx hcode hfork hrun hnp)

#print axioms gasSteps_call
#print axioms gasSteps_call_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CallPrepare
