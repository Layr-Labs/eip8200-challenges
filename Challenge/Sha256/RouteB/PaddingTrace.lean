import Challenge.Sha256.RouteB.Padding
import Challenge.Sha256.RouteB.Trace
import Challenge.RouteB.Stepper
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

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  UInt256.ofNat Padding.messageOffset +
    (Padding.paddedWord input - UInt256.ofNat 8)

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

/-- Entry to the fixed eight-iteration loop that stores the big-endian bit
length.  The calldata bytes and the `0x80` sentinel are already in memory. -/
def lengthLoopStart (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat (Artifact.instructionPC 289)
    stack := [⟨0⟩, lengthOffsetWord input, bitLengthWord input,
      UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 1367] }

def lengthSetupPath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨270, .op (.Dup ⟨0, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨271, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨272, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨273, .op .CALLDATACOPY, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨274, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨275, .op (.Dup ⟨1, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨276, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨277, .op .ADD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨278, .op .MSTORE8, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨279, .op (.Dup ⟨0, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨280, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨281, .op .SHL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨282, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨283, .op (.Dup ⟨3, by decide⟩), by rfl,
      ⟨by decide, trivial, rfl⟩⟩,
   ⟨284, .op .SUB, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨285, .push ⟨2, by decide⟩ (UInt256.ofNat Padding.messageOffset),
      by rfl, by decide⟩,
   ⟨286, .op .ADD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨287, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨288, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩]

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = Artifact.instructionPC 270 := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat (Artifact.instructionPC 270) := by
  rfl

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 1367] := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem pc270 : Artifact.instructionPC 270 = 371 := by decide
@[simp] private theorem pc271 : Artifact.instructionPC 271 = 372 := by decide
@[simp] private theorem pc272 : Artifact.instructionPC 272 = 373 := by decide
@[simp] private theorem pc273 : Artifact.instructionPC 273 = 376 := by decide
@[simp] private theorem pc274 : Artifact.instructionPC 274 = 377 := by decide
@[simp] private theorem pc275 : Artifact.instructionPC 275 = 379 := by decide
@[simp] private theorem pc276 : Artifact.instructionPC 276 = 380 := by decide
@[simp] private theorem pc277 : Artifact.instructionPC 277 = 383 := by decide
@[simp] private theorem pc278 : Artifact.instructionPC 278 = 384 := by decide
@[simp] private theorem pc279 : Artifact.instructionPC 279 = 385 := by decide
@[simp] private theorem pc280 : Artifact.instructionPC 280 = 386 := by decide
@[simp] private theorem pc281 : Artifact.instructionPC 281 = 388 := by decide
@[simp] private theorem pc282 : Artifact.instructionPC 282 = 389 := by decide
@[simp] private theorem pc283 : Artifact.instructionPC 283 = 391 := by decide
@[simp] private theorem pc284 : Artifact.instructionPC 284 = 392 := by decide
@[simp] private theorem pc285 : Artifact.instructionPC 285 = 393 := by decide
@[simp] private theorem pc286 : Artifact.instructionPC 286 = 396 := by decide
@[simp] private theorem pc287 : Artifact.instructionPC 287 = 397 := by decide
@[simp] private theorem pc288 : Artifact.instructionPC 288 = 398 := by decide
@[simp] private theorem pc289 : Artifact.instructionPC 289 = 399 := by decide

@[simp] private theorem refPc270 :
    Artifact.referenceArtifact.instructionPC 270 = 371 := by decide
@[simp] private theorem refPc271 :
    Artifact.referenceArtifact.instructionPC 271 = 372 := by decide
@[simp] private theorem refPc272 :
    Artifact.referenceArtifact.instructionPC 272 = 373 := by decide
@[simp] private theorem refPc273 :
    Artifact.referenceArtifact.instructionPC 273 = 376 := by decide
@[simp] private theorem refPc274 :
    Artifact.referenceArtifact.instructionPC 274 = 377 := by decide
@[simp] private theorem refPc275 :
    Artifact.referenceArtifact.instructionPC 275 = 379 := by decide
@[simp] private theorem refPc276 :
    Artifact.referenceArtifact.instructionPC 276 = 380 := by decide
@[simp] private theorem refPc277 :
    Artifact.referenceArtifact.instructionPC 277 = 383 := by decide
@[simp] private theorem refPc278 :
    Artifact.referenceArtifact.instructionPC 278 = 384 := by decide
@[simp] private theorem refPc279 :
    Artifact.referenceArtifact.instructionPC 279 = 385 := by decide
@[simp] private theorem refPc280 :
    Artifact.referenceArtifact.instructionPC 280 = 386 := by decide
@[simp] private theorem refPc281 :
    Artifact.referenceArtifact.instructionPC 281 = 388 := by decide
@[simp] private theorem refPc282 :
    Artifact.referenceArtifact.instructionPC 282 = 389 := by decide
@[simp] private theorem refPc283 :
    Artifact.referenceArtifact.instructionPC 283 = 391 := by decide
@[simp] private theorem refPc284 :
    Artifact.referenceArtifact.instructionPC 284 = 392 := by decide
@[simp] private theorem refPc285 :
    Artifact.referenceArtifact.instructionPC 285 = 393 := by decide
@[simp] private theorem refPc286 :
    Artifact.referenceArtifact.instructionPC 286 = 396 := by decide
@[simp] private theorem refPc287 :
    Artifact.referenceArtifact.instructionPC 287 = 397 := by decide
@[simp] private theorem refPc288 :
    Artifact.referenceArtifact.instructionPC 288 = 398 := by decide

@[simp] private theorem next270 : (UInt256.ofNat 371).succ = UInt256.ofNat 372 := by decide
@[simp] private theorem next271 : (UInt256.ofNat 372).succ = UInt256.ofNat 373 := by decide
@[simp] private theorem next272 : UInt256.ofNat 373 + UInt256.ofNat 3 = UInt256.ofNat 376 := by decide
@[simp] private theorem next273 : (UInt256.ofNat 376).succ = UInt256.ofNat 377 := by decide
@[simp] private theorem next274 : UInt256.ofNat 377 + UInt256.ofNat 2 = UInt256.ofNat 379 := by decide
@[simp] private theorem next275 : (UInt256.ofNat 379).succ = UInt256.ofNat 380 := by decide
@[simp] private theorem next276 : UInt256.ofNat 380 + UInt256.ofNat 3 = UInt256.ofNat 383 := by decide
@[simp] private theorem next277 : (UInt256.ofNat 383).succ = UInt256.ofNat 384 := by decide
@[simp] private theorem next278 : (UInt256.ofNat 384).succ = UInt256.ofNat 385 := by decide
@[simp] private theorem next279 : (UInt256.ofNat 385).succ = UInt256.ofNat 386 := by decide
@[simp] private theorem next280 : UInt256.ofNat 386 + UInt256.ofNat 2 = UInt256.ofNat 388 := by decide
@[simp] private theorem next281 : (UInt256.ofNat 388).succ = UInt256.ofNat 389 := by decide
@[simp] private theorem next282 : UInt256.ofNat 389 + UInt256.ofNat 2 = UInt256.ofNat 391 := by decide
@[simp] private theorem next283 : (UInt256.ofNat 391).succ = UInt256.ofNat 392 := by decide
@[simp] private theorem next284 : (UInt256.ofNat 392).succ = UInt256.ofNat 393 := by decide
@[simp] private theorem next285 : UInt256.ofNat 393 + UInt256.ofNat 3 = UInt256.ofNat 396 := by decide
@[simp] private theorem next286 : (UInt256.ofNat 396).succ = UInt256.ofNat 397 := by decide
@[simp] private theorem next287 : (UInt256.ofNat 397).succ = UInt256.ofNat 398 := by decide
@[simp] private theorem next288 : (UInt256.ofNat 398).succ = UInt256.ofNat 399 := by decide

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

set_option maxHeartbeats 2000000 in
private theorem run_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.RouteB.Stepper.runLocatedBlock
      lengthSetupPath (padLengthReady input) = some (lengthLoopStart input) := by
  have hsize : input.size < 2 ^ 256 := by
    exact Nat.lt_trans hfit (by norm_num)
  have hoff : Padding.messageOffset < 2 ^ 256 := by decide
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : (UInt256.ofNat Padding.messageOffset +
      UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size := by
    rw [Challenge.RouteB.Word.ofNat_add_ofNat hsum,
      Challenge.RouteB.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.RouteB.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hoffWord : (UInt256.ofNat Padding.messageOffset).toNat =
      Padding.messageOffset := by
    rw [Challenge.RouteB.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hzeroWord : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [lengthSetupPath,
    Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    lengthLoopStart, padSentinel, padCopied, lengthOffsetWord, bitLengthWord,
    State.activeWordsAfterUInt256, hsizeWord, hoffWord, hzeroWord, hadd]

theorem gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.RouteB.GasSteps (padLengthReady input) (lengthLoopStart input) := by
  apply Challenge.RouteB.Stepper.runLocatedBlock_sound Artifact.referenceArtifact
    .Osaka lengthSetupPath
  · rfl
  · exact padLengthReady_fork input
  · exact run_lengthSetup input hfit
  · rfl
  · rfl

end Challenge.Sha256.RouteB.PaddingTrace
