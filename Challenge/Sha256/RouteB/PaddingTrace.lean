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

private def p262 (input : ByteArray) : State :=
  { padSized input with
    pc := (padSized input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 72 :: (padSized input).stack }

private def p263 (input : ByteArray) : State :=
  { p262 input with
    pc := (p262 input).pc.succ
    stack := UInt256.ofNat input.size :: (p262 input).stack }

private def p264 (input : ByteArray) : State :=
  { p263 input with
    pc := (p263 input).pc.succ
    stack := (UInt256.ofNat input.size + UInt256.ofNat 72) ::
      (padSized input).stack }

private def p265 (input : ByteArray) : State :=
  { p264 input with
    pc := (p264 input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 6 :: (p264 input).stack }

private def p266 (input : ByteArray) : State :=
  { p265 input with
    pc := (p265 input).pc.succ
    stack := UInt256.shiftRight
      (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6) ::
      (padSized input).stack }

private def p267 (input : ByteArray) : State :=
  { p266 input with
    pc := (p266 input).pc + UInt256.ofNat 2
    stack := UInt256.ofNat 6 :: (p266 input).stack }

private def p268 (input : ByteArray) : State :=
  { p267 input with
    pc := (p267 input).pc.succ
    stack := Padding.paddedWord input :: (padSized input).stack }

private def p269 (input : ByteArray) : State :=
  { p268 input with
    pc := (p268 input).pc.succ
    stack := [⟨0⟩, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 1367] }

def padLengthReady (input : ByteArray) : State :=
  { p269 input with
    pc := (p269 input).pc.succ
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 1367] }

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

theorem gasSteps_computePaddedLength (input : ByteArray) :
    Challenge.RouteB.GasSteps (padSized input) (padLengthReady input) := by
  have hinitStack : (Main.initializedState input).stack = [] := by rfl
  have hbodyStack : (padBodyStart input).stack =
      [⟨0⟩, UInt256.ofNat 1367] := by rfl
  have hentryPC : (padEntry input).pc =
      UInt256.ofNat (Artifact.instructionPC 259) := by
    rw [padEntry]
    congr 1
  have hbodyPC : (padBodyStart input).pc =
      UInt256.ofNat (Artifact.instructionPC 260) := by
    rw [padBodyStart, hentryPC]
    exact Trace.succPC (index := 259) (by decide)
  have h261 : (padSized input).pc =
      UInt256.ofNat (Artifact.instructionPC 261) := by
    rw [padSized, hbodyPC]
    exact Trace.succPC (index := 260) (by decide)
  have h262 : (p262 input).pc = UInt256.ofNat (Artifact.instructionPC 262) := by
    rw [p262, h261]
    exact Trace.pushPC (index := 261) (width := 1) (by decide)
  have h263 : (p263 input).pc = UInt256.ofNat (Artifact.instructionPC 263) := by
    rw [p263, h262]
    exact Trace.succPC (index := 262) (by decide)
  have h264 : (p264 input).pc = UInt256.ofNat (Artifact.instructionPC 264) := by
    rw [p264, h263]
    exact Trace.succPC (index := 263) (by decide)
  have h265 : (p265 input).pc = UInt256.ofNat (Artifact.instructionPC 265) := by
    rw [p265, h264]
    exact Trace.pushPC (index := 264) (width := 1) (by decide)
  have h266 : (p266 input).pc = UInt256.ofNat (Artifact.instructionPC 266) := by
    rw [p266, h265]
    exact Trace.succPC (index := 265) (by decide)
  have h267 : (p267 input).pc = UInt256.ofNat (Artifact.instructionPC 267) := by
    rw [p267, h266]
    exact Trace.pushPC (index := 266) (width := 1) (by decide)
  have h268 : (p268 input).pc = UInt256.ofNat (Artifact.instructionPC 268) := by
    rw [p268, h267]
    exact Trace.succPC (index := 267) (by decide)
  have h269 : (p269 input).pc = UInt256.ofNat (Artifact.instructionPC 269) := by
    rw [p269, h268]
    exact Trace.succPC (index := 268) (by decide)
  have g261 : Challenge.RouteB.GasSteps (padSized input) (p262 input) := by
    have hd := Trace.decodedPushAt (padSized input) 261 ⟨1, by decide⟩
      (UInt256.ofNat 72) rfl h261 rfl (by decide) (by rfl)
    have g := Challenge.RouteB.GasStep.pushN (s := padSized input)
      ⟨1, by decide⟩ (UInt256.ofNat 72) 1 (by decide) hd
      (by simp [padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
        pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p262] using g
  have g262 : Challenge.RouteB.GasSteps (p262 input) (p263 input) := by
    have hd := Trace.decodedOpAt (p262 input) 262 (.Dup ⟨1, by decide⟩)
      rfl h262 rfl (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.dup (s := p262 input) ⟨1, by decide⟩
      (UInt256.ofNat input.size) hd (by
        simp [p262, padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
          pushedReturn, hinitStack]) (by
        simp [p262, padSized, padBodyStart, padEntry, pushedPad, pushedOutput,
          pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p263] using g
  have g263 : Challenge.RouteB.GasSteps (p263 input) (p264 input) := by
    have hd := Trace.decodedOpAt (p263 input) 263 .ADD rfl h263 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.add (s := p263 input)
      (a := UInt256.ofNat input.size) (b := UInt256.ofNat 72)
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack]) (by
      simp [p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack, Operation.pushArity,
        Operation.popArity]) (by rfl) (by rfl)
    simpa [p264, p263, p262, padSized, hinitStack, hbodyStack] using g
  have g264 : Challenge.RouteB.GasSteps (p264 input) (p265 input) := by
    have hd := Trace.decodedPushAt (p264 input) 264 ⟨1, by decide⟩
      (UInt256.ofNat 6) rfl h264 rfl (by decide) (by rfl)
    have g := Challenge.RouteB.GasStep.pushN (s := p264 input)
      ⟨1, by decide⟩ (UInt256.ofNat 6) 1 (by decide) hd
      (by simp [p264, p263, p262, padSized, padBodyStart, padEntry, pushedPad,
        pushedOutput, pushedReturn, hinitStack]) (by rfl) (by rfl)
    simpa [p265] using g
  have g265 : Challenge.RouteB.GasSteps (p265 input) (p266 input) := by
    have hd := Trace.decodedOpAt (p265 input) 265 .SHR rfl h265 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.shr (s := p265 input)
      (shift := UInt256.ofNat 6)
      (value := UInt256.ofNat input.size + UInt256.ofNat 72)
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p265, p264, p263, p262, padSized, padBodyStart, padEntry,
        pushedPad, pushedOutput, pushedReturn, hinitStack]) (by
      simp [p265, p264, p263, p262, padSized, padBodyStart, padEntry,
        pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [p266, p265, p264, p263, p262, padSized, hinitStack,
      hbodyStack] using g
  have g266 : Challenge.RouteB.GasSteps (p266 input) (p267 input) := by
    have hd := Trace.decodedPushAt (p266 input) 266 ⟨1, by decide⟩
      (UInt256.ofNat 6) rfl h266 rfl (by decide) (by rfl)
    have g := Challenge.RouteB.GasStep.pushN (s := p266 input)
      ⟨1, by decide⟩ (UInt256.ofNat 6) 1 (by decide) hd
      (by simp [p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack])
      (by rfl) (by rfl)
    simpa [p267] using g
  have g267 : Challenge.RouteB.GasSteps (p267 input) (p268 input) := by
    have hd := Trace.decodedOpAt (p267 input) 267 .SHL rfl h267 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.shl (s := p267 input)
      (shift := UInt256.ofNat 6)
      (value := UInt256.shiftRight
        (UInt256.ofNat input.size + UInt256.ofNat 72) (UInt256.ofNat 6))
      (rest := [UInt256.ofNat input.size, ⟨0⟩, UInt256.ofNat 1367]) hd (by
      simp [p267, p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack]) (by
      simp [p267, p266, p265, p264, p263, p262, padSized, padBodyStart,
        padEntry, pushedPad, pushedOutput, pushedReturn, hinitStack,
        Operation.pushArity, Operation.popArity]) (by rfl) (by rfl)
    simpa [p268, Padding.paddedWord, p267, p266, p265, p264, p263, p262,
      padSized, hinitStack, hbodyStack] using g
  have g268 : Challenge.RouteB.GasSteps (p268 input) (p269 input) := by
    have hd := Trace.decodedOpAt (p268 input) 268 (.Swap ⟨1, by decide⟩)
      rfl h268 rfl (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.swap (s := p268 input) ⟨1, by decide⟩
      [⟨0⟩, UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 1367] hd (by
          simp [p268, p267, p266, p265, p264, p263, p262, padSized,
            padBodyStart, padEntry, pushedPad, pushedOutput, pushedReturn,
            hinitStack, List.exchange]) (by
          simp [p268, p267, p266, p265, p264, p263, p262, padSized,
            padBodyStart, padEntry, pushedPad, pushedOutput, pushedReturn,
            hinitStack, Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [p269] using g
  have g269 : Challenge.RouteB.GasSteps (p269 input) (padLengthReady input) := by
    have hd := Trace.decodedOpAt (p269 input) 269 .POP rfl h269 rfl
      (by decide) trivial (by rfl)
    have g := Challenge.RouteB.GasStep.pop (s := p269 input) hd (by rfl)
      (by simp [p269, Operation.pushArity, Operation.popArity])
      (by rfl) (by rfl)
    simpa [padLengthReady] using g
  exact g261.trans (g262.trans (g263.trans (g264.trans (g265.trans
    (g266.trans (g267.trans (g268.trans g269)))))))

end Challenge.Sha256.RouteB.PaddingTrace
