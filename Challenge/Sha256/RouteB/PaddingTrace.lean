import Challenge.Sha256.RouteB.Padding
import Challenge.Sha256.RouteB.Trace
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Direct execution of the reference padding function

The first certified block enters `pad` from the initialized main state.  The
subsequent loop proof uses the two-word function frame established here:
zero output slot above the return destination.
-/

namespace Challenge.Sha256.RouteB.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

def pushedReturn (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := (Main.initializedState input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 1367 :: (Main.initializedState input).stack }

def pushedOutput (input : ByteArray) : State :=
  { pushedReturn input with
    pc := (pushedReturn input).pc.succ
    stack := ⟨0⟩ :: (pushedReturn input).stack }

def pushedPad (input : ByteArray) : State :=
  { pushedOutput input with
    pc := (pushedOutput input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 357 :: (pushedOutput input).stack }

def padEntry (input : ByteArray) : State :=
  { pushedPad input with
    pc := UInt256.ofNat 357
    stack := [⟨0⟩, UInt256.ofNat 1367] }

def padBodyStart (input : ByteArray) : State :=
  { padEntry input with pc := (padEntry input).pc.succ }

def padSized (input : ByteArray) : State :=
  { padBodyStart input with
    pc := (padBodyStart input).pc.succ
    stack := UInt256.ofNat input.size :: (padBodyStart input).stack }

theorem gasSteps_enterPad (input : ByteArray) :
    Challenge.RouteB.GasSteps (Main.initializedState input) (padEntry input) := by
  have hinitPC : (Main.initializedState input).pc =
      UInt256.ofNat (Artifact.instructionPC 707) := by rfl
  have hinitStack : (Main.initializedState input).stack = [] := by rfl
  have hreturnPC : (pushedReturn input).pc =
      UInt256.ofNat (Artifact.instructionPC 708) := by
    rw [pushedReturn, hinitPC]
    exact Trace.pushPC (index := 707) (width := 2) (by decide)
  have houtputPC : (pushedOutput input).pc =
      UInt256.ofNat (Artifact.instructionPC 709) := by
    rw [pushedOutput, hreturnPC]
    exact Trace.succPC (index := 708) (by decide)
  have hpadPC : (pushedPad input).pc =
      UInt256.ofNat (Artifact.instructionPC 710) := by
    rw [pushedPad, houtputPC]
    exact Trace.pushPC (index := 709) (width := 2) (by decide)
  have hpushReturn : Challenge.RouteB.GasSteps
      (Main.initializedState input) (pushedReturn input) := by
    have hdecode := Trace.decodedPushAt (Main.initializedState input) 707
      ⟨2, by decide⟩ (UInt256.ofNat 1367) rfl rfl rfl (by decide)
      (by rfl)
    have hstep := Challenge.RouteB.GasStep.pushN
      (s := Main.initializedState input) ⟨2, by decide⟩
      (UInt256.ofNat 1367) 2 (by decide) hdecode (by simp [hinitStack])
      (by rfl) (by rfl)
    simpa [pushedReturn] using hstep
  have hpushOutput : Challenge.RouteB.GasSteps
      (pushedReturn input) (pushedOutput input) := by
    have hdecode := Trace.decodedPushOpAt (pushedReturn input) 708
      ⟨0, by decide⟩ ⟨0⟩ rfl (by
        exact hreturnPC) rfl
        (by decide) (by rfl)
    have hstep := Challenge.RouteB.GasStep.push0 (s := pushedReturn input)
      hdecode (by simp [pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [pushedOutput] using hstep
  have hpushPad : Challenge.RouteB.GasSteps
      (pushedOutput input) (pushedPad input) := by
    have hdecode := Trace.decodedPushAt (pushedOutput input) 709
      ⟨2, by decide⟩ (UInt256.ofNat 357) rfl (by
        exact houtputPC) rfl
        (by decide) (by rfl)
    have hstep := Challenge.RouteB.GasStep.pushN
      (s := pushedOutput input) ⟨2, by decide⟩
      (UInt256.ofNat 357) 2 (by decide) hdecode
      (by simp [pushedOutput, pushedReturn, hinitStack])
      (by rfl) (by rfl)
    simpa [pushedPad] using hstep
  have hjump : Challenge.RouteB.GasSteps (pushedPad input) (padEntry input) := by
    have hdecode := Trace.decodedOpAt (pushedPad input) 710 .JUMP rfl hpadPC rfl
      (by decide) trivial (by rfl)
    have hvalid : Decode.isValidJumpDest
        (pushedPad input).executionEnv.code (UInt256.ofNat 357).toNat = true := by
      change Decode.isValidJumpDest referenceBytecode 357 = true
      have hv := Trace.validJumpDestAt 259 rfl
      change Decode.isValidJumpDest referenceBytecode
        (Artifact.instructionPC 259 % 2 ^ 256) = true at hv
      rw [show Artifact.instructionPC 259 % 2 ^ 256 = 357 by decide] at hv
      exact hv
    have hstep := Challenge.RouteB.GasStep.jump (s := pushedPad input)
      (UInt256.ofNat 357) [⟨0⟩, UInt256.ofNat 1367] hdecode (by rfl) hvalid
      (by simp [pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [padEntry] using hstep
  exact hpushReturn.trans (hpushOutput.trans (hpushPad.trans hjump))

theorem gasSteps_padReadSize (input : ByteArray) :
    Challenge.RouteB.GasSteps (padEntry input) (padSized input) := by
  have hentryPC : (padEntry input).pc =
      UInt256.ofNat (Artifact.instructionPC 259) := by
    rw [padEntry]
    congr 1
  have hbodyPC : (padBodyStart input).pc =
      UInt256.ofNat (Artifact.instructionPC 260) := by
    rw [padBodyStart, hentryPC]
    exact Trace.succPC (index := 259) (by decide)
  have gjumpdest : Challenge.RouteB.GasSteps
      (padEntry input) (padBodyStart input) := by
    have hdecode := Trace.decodedOpAt (padEntry input) 259 .JUMPDEST rfl
      hentryPC rfl (by decide) trivial (by rfl)
    have hstep := Challenge.RouteB.GasStep.jumpdest (s := padEntry input)
      hdecode (by simp [padEntry, pushedPad, pushedOutput, pushedReturn,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [padBodyStart] using hstep
  have gsize : Challenge.RouteB.GasSteps
      (padBodyStart input) (padSized input) := by
    have hcalldata : (padBodyStart input).executionEnv.calldata = input := by rfl
    have hdecode := Trace.decodedOpAt (padBodyStart input) 260 .CALLDATASIZE
      rfl hbodyPC rfl (by decide) trivial (by rfl)
    have hstep := Challenge.RouteB.GasStep.calldatasize (s := padBodyStart input)
      hdecode (by simp [padBodyStart, padEntry, pushedPad, pushedOutput,
        pushedReturn]) (by rfl) (by rfl)
    simpa [padSized, hcalldata] using hstep
  exact gjumpdest.trans gsize

end Challenge.Sha256.RouteB.PaddingTrace
