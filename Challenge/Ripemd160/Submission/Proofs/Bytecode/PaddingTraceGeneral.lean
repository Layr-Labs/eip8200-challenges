import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTraceGeneral
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PaddingTrace

/-- Actual stores of the generic padding body, starting from arbitrary memory. -/
def lengthMemory (input memory : ByteArray) : Nat → ByteArray
  | 0 => MachineState.writeBytes memory (ByteArray.mk #[0x80])
      (Padding.messageOffset + input.size)
  | i + 1 => MachineState.writeBytes (lengthMemory input memory i)
      (ByteArray.mk #[UInt8.ofNat ((lengthShift input i).toNat % 256)])
      (lengthAddr input i).toNat

def lengthActive (input : ByteArray) (active : UInt256) : Nat → UInt256
  | 0 => UInt256.ofNat (MachineState.activeWordsAfter active.toNat
      (Padding.messageOffset + input.size) 1)
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (lengthActive input active i).toNat (lengthAddr input i).toNat 1)

def sentinelState (input : ByteArray) (s : State) (frame : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 4735
    stack := frame
    memory := lengthMemory input s.memory 0
    activeWords := lengthActive input s.activeWords 0}

def loopState (input : ByteArray) (s : State) (frame : List UInt256) (i : Nat) : State :=
  {s with
    pc := UInt256.ofNat 4744
    stack := lengthAddr input i :: lengthShift input i :: frame
    memory := lengthMemory input s.memory i
    activeWords := lengthActive input s.activeWords i}

def steppedState (input : ByteArray) (s : State) (frame : List UInt256) (i : Nat) : State :=
  {loopState input s frame (i + 1) with pc := UInt256.ofNat 4756}

def exitState (input : ByteArray) (s : State) (frame : List UInt256) (i : Nat) : State :=
  {loopState input s frame i with pc := UInt256.ofNat 4761}

def resultStateAt (input : ByteArray) (s : State) (frame : List UInt256) (i : Nat) : State :=
  {s with
    pc := UInt256.ofNat 465
    stack := frame
    memory := lengthMemory input s.memory i
    activeWords := lengthActive input s.activeWords i}

def resultState (input : ByteArray) (s : State) (frame : List UInt256) : State :=
  resultStateAt input s frame (lengthStop input)

theorem paddedWord_aligned (input : ByteArray) (hfit : CalldataFits input)
    (haligned : input.size % 64 = 0) :
    Padding.paddedWord input = UInt256.ofNat (input.size + 64) := by
  rw [Padding.paddedWord_eq input hfit]
  congr 1
  unfold Padding.paddedLength
  omega

@[simp] theorem resultState_memory (input : ByteArray) (s : State) (frame : List UInt256) :
    (resultState input s frame).memory = lengthMemory input s.memory (lengthStop input) := rfl

@[simp] theorem resultState_activeWords (input : ByteArray) (s : State) (frame : List UInt256) :
    (resultState input s frame).activeWords = lengthActive input s.activeWords (lengthStop input) := rfl

private theorem valid_loop : Decode.isValidJumpDest submissionBytecode 4744 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3635 = 4744 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 3635 (by rfl)

private theorem word_ne_zero (x : UInt256) (hx : x ≠ ⟨0⟩) : x.toNat ≠ 0 := by
  intro h
  apply hx
  apply Word.word_ext
  exact h

section
variable (input : ByteArray) (s : State) (frame : List UInt256)
variable (hframe : frame.length = 15)
variable (hlimit : frame[12]? = some (Padding.paddedWord input))
variable (hcal : s.executionEnv.calldata = input)
variable (hrun : s.halt = .Running)
variable (hcode : s.executionEnv.code = submissionBytecode)
variable (hfork : s.fork = .Osaka)
variable (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
  s.executionEnv.fork s.executionEnv.codeAddr = false)

include hframe hcal hrun in
private theorem run_sentinel (hfit : CalldataFits input) :
    DataStepper.runLocatedBlock lengthSentinelPath
      {s with pc := UInt256.ofNat 4727, stack := frame} =
      some (sentinelState input s frame) := by
  have hsum : Padding.messageOffset + input.size < 2^256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat =
      Padding.messageOffset + input.size := by
    rw [Word.ofNat_add_ofNat hsum, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  have hadd' : (UInt256.ofNat input.size + UInt256.ofNat 1087).toNat =
      1087 + input.size := by
    rw [Word.word_add_comm]
    exact hadd
  simp [lengthSentinelPath, Artifact.padSentinelPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, sentinelState, lengthMemory,
    lengthActive, State.activeWordsAfterUInt256, hframe, hcal, hrun,
    Padding.messageOffset, hadd, hadd']

include hframe hlimit hcal hrun in
private theorem run_setup :
    DataStepper.runLocatedBlock lengthFooterSetupPath (sentinelState input s frame) =
      some (loopState input s frame 0) := by
  obtain ⟨hidx, hget⟩ := List.getElem_of_getElem? hlimit
  have haddressOrder : UInt256.ofNat 1079 + Padding.paddedWord input =
      Padding.paddedWord input + UInt256.ofNat 1079 := Word.word_add_comm _ _
  simp [lengthFooterSetupPath, Artifact.padFooterSetupPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, sentinelState, loopState,
    lengthAddr, lengthShift, lengthOffsetWord, bitLengthWord, haddressOrder,
    hframe, hlimit, hget, hcal, hrun]

include hframe hrun in
private theorem run_body (i : Nat) :
    DataStepper.runLocatedBlock lengthBodyPath (loopState input s frame i) =
      some (steppedState input s frame i) := by
  simp [lengthBodyPath, lengthIterationPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, steppedState, loopState,
    lengthMemory, lengthActive, lengthAddr, lengthShift, List.exchange,
    State.activeWordsAfterUInt256, hframe, hrun]

include hframe hrun hcode in
private theorem run_back (i : Nat) (hne : lengthShift input (i+1) ≠ ⟨0⟩) :
    DataStepper.runLocatedBlock lengthBranchPath (steppedState input s frame i) =
      some (loopState input s frame (i+1)) := by
  have ht : UInt256.isTrue (lengthShift input (i+1)) = true := by
    simp [UInt256.isTrue, word_ne_zero _ hne]
  simp [lengthBranchPath, lengthIterationPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, steppedState, loopState,
    hframe, hrun, hcode, ht, valid_loop]

include hframe hrun in
private theorem run_branch_exit (i : Nat) (hz : lengthShift input (i+1) = ⟨0⟩) :
    DataStepper.runLocatedBlock lengthBranchPath (steppedState input s frame i) =
      some (exitState input s frame (i+1)) := by
  have ht : UInt256.isTrue (lengthShift input (i+1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, steppedState, loopState,
    exitState, hframe, hrun, ht]

include hframe hrun hcode in
private theorem run_exit (i : Nat) :
    DataStepper.runLocatedBlock lengthExitPath (exitState input s frame i) =
      some (resultStateAt input s frame i) := by
  have hj := StaggerPersistentStart.valid_loop s hcode
  simp [lengthExitPath, Artifact.padExitPath, DataStepper.runLocatedBlock,
    DataStepper.runLocated, DataStepper.runInstr, exitState, loopState,
    resultStateAt, hframe, hrun, hcode, hj]

include hframe hlimit hcal hrun hcode hfork hnp in
def gasSteps_setup (hfit : CalldataFits input) :
    GasSteps {s with pc := UInt256.ofNat 4727, stack := frame}
      (loopState input s frame 0) := by
  have gs := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthSentinelPath (s := {s with pc := UInt256.ofNat 4727, stack := frame}) hcode hfork (run_sentinel input s frame hframe hcal hrun hfit) hrun hnp
  have gt := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthFooterSetupPath (s := sentinelState input s frame) hcode hfork (run_setup input s frame hframe hlimit hcal hrun) hrun hnp
  exact gs.trans gt

include hframe hrun hcode hfork hnp in
def gasSteps_iteration (i : Nat) (hne : lengthShift input (i+1) ≠ ⟨0⟩) :
    GasSteps (loopState input s frame i) (loopState input s frame (i+1)) := by
  have gb := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthBodyPath (s := loopState input s frame i) hcode hfork (run_body input s frame hframe hrun i) hrun hnp
  have gr := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthBranchPath (s := steppedState input s frame i) hcode hfork (run_back input s frame hframe hrun hcode i hne) hrun hnp
  exact gb.trans gr

include hframe hrun hcode hfork hnp in
def gasSteps_iteration_exit (i : Nat) (hz : lengthShift input (i+1) = ⟨0⟩) :
    GasSteps (loopState input s frame i) (resultStateAt input s frame (i+1)) := by
  have gb := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthBodyPath (s := loopState input s frame i) hcode hfork (run_body input s frame hframe hrun i) hrun hnp
  have gr := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthBranchPath (s := steppedState input s frame i) hcode hfork (run_branch_exit input s frame hframe hrun i hz) hrun hnp
  have ge := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    lengthExitPath (s := exitState input s frame (i+1)) hcode hfork (run_exit input s frame hframe hrun hcode (i+1)) hrun hnp
  exact gb.trans (gr.trans ge)

include hframe hrun hcode hfork hnp in
noncomputable def gasSteps_loopFrom (hfit : CalldataFits input) :
    (fuel i : Nat) → i+fuel = 9 →
    (∀ j, 0<j → j≤i → lengthShift input j ≠ ⟨0⟩) →
    lengthShift input i ≠ ⟨0⟩ →
    GasSteps (loopState input s frame i) (resultState input s frame)
  | 0, i, hsum, _hprior, hne => by
      have hi : i = 9 := by omega
      subst hi
      exact False.elim (hne (lengthShift_nine input hfit))
  | fuel+1, i, hsum, hprior, _hne =>
      if hz : lengthShift input (i+1) = ⟨0⟩ then
        have hs := lengthStop_eq_succ_of_nonzero input i (by omega) hprior hz
        GasSteps.cast
          (gasSteps_iteration_exit input s frame hframe hrun hcode hfork hnp i hz) rfl
          (by simp [resultState, hs])
      else
        have hp : ∀ j, 0<j → j≤i+1 → lengthShift input j ≠ ⟨0⟩ := by
          intro j hj hji
          by_cases hle : j≤i
          · exact hprior j hj hle
          · have he : j=i+1 := by omega
            simpa [he] using hz
        (gasSteps_iteration input s frame hframe hrun hcode hfork hnp i hz).trans
          (gasSteps_loopFrom hfit fuel (i+1) (by omega) hp hz)

include hframe hrun hcode hfork hnp in
noncomputable def gasSteps_loop (hfit : CalldataFits input) :
    GasSteps (loopState input s frame 0) (resultState input s frame) :=
  if hz : lengthShift input 1 = ⟨0⟩ then
    have hs := lengthStop_eq_succ_of_nonzero input 0 (by norm_num)
      (fun j hj hle => by omega) hz
    GasSteps.cast
      (gasSteps_iteration_exit input s frame hframe hrun hcode hfork hnp 0 hz) rfl
      (by simp [resultState, hs])
  else
    (gasSteps_iteration input s frame hframe hrun hcode hfork hnp 0 hz).trans
      (gasSteps_loopFrom input s frame hframe hrun hcode hfork hnp hfit 8 1 (by norm_num)
        (fun j hj hle => by
          have he : j=1 := by omega
          simpa [he] using hz) hz)

include hframe hlimit hcal hrun hcode hfork hnp in
/-- Generic padding at the actual artifact entry, preserving an arbitrary initialized frame.
The twelve upper words include the offset, and word12 is the padded limit. -/
noncomputable def gasSteps_padBody (hfit : CalldataFits input) (_hn32 : input.size ≠ 32) :
    GasSteps {s with pc := UInt256.ofNat 4727, stack := frame}
      (resultState input s frame) := by
  exact (gasSteps_setup input s frame hframe hlimit hcal hrun hcode hfork hnp hfit).trans
    (gasSteps_loop input s frame hframe hrun hcode hfork hnp hfit)

end

#print axioms gasSteps_padBody
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTraceGeneral
