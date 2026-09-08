import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameControl
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-!
# Raw execution model for the packed final combine

This module transcribes the exact instructions at indices `4401 .. 4479` of
the final packed artifact.  The first 78 instructions are the straight-line
five-word combine and cleanup.  The final instruction is the dynamic return
`JUMP`; it is deliberately kept separate because it does not advance to the
next byte PC.

There is no artifact lookup in this file.  `PackedCombineSite` supplies that
independent certificate.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open PackedStepFrame PackedFrameControl

private def push1 (value : Nat) : Instr :=
  .push ⟨1, by decide⟩ (UInt256.ofNat value)

private def push2 (value : Nat) : Instr :=
  .push ⟨2, by decide⟩ (UInt256.ofNat value)

private def dup (index : Fin 16) : Instr := .op (.Dup ⟨index⟩)

private def combine0 : List Instr :=
  [push2 352, .op .MLOAD, dup 3, dup 5, push1 64, .op .SHR, .op .ADD,
   push2 384, .op .MLOAD, .op .ADD, dup 8, .op .AND, push2 352, .op .MSTORE]

private def combine1 : List Instr :=
  [dup 4, dup 6, push1 64, .op .SHR, .op .ADD,
   push2 416, .op .MLOAD, .op .ADD, dup 8, .op .AND, push2 384, .op .MSTORE]

private def combine2 : List Instr :=
  [dup 5, dup 2, push1 64, .op .SHR, .op .ADD,
   push2 448, .op .MLOAD, .op .ADD, dup 8, .op .AND, push2 416, .op .MSTORE]

private def combine3 : List Instr :=
  [dup 1, dup 3, push1 64, .op .SHR, .op .ADD,
   push2 480, .op .MLOAD, .op .ADD, dup 8, .op .AND, push2 448, .op .MSTORE]

private def combine4 : List Instr :=
  [dup 2, dup 4, push1 64, .op .SHR, .op .ADD, dup 1, .op .ADD,
   dup 8, .op .AND, push2 480, .op .MSTORE]

private def cleanup : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

/-- Exact five-output combine and cleanup, stopping immediately before the
dynamic return jump at PC 5169. -/
def combineBody : List Instr :=
  combine0 ++ combine1 ++ combine2 ++ combine3 ++ combine4 ++ cleanup

def returnJump : List Instr := [.op .JUMP]

/-- All 79 concrete instructions, indices `4401 .. 4479`. -/
def combineTail : List Instr := combineBody ++ returnJump

@[simp] theorem combineBody_length : combineBody.length = 78 := rfl
@[simp] theorem combineTail_length : combineTail.length = 79 := rfl

/-- The exact 19-word even frame consumed by the final combine. -/
def entryStack (g : PackedStepCorrected.Regs) (ret xoff xend : UInt256)
    (rest : List UInt256) : List UInt256 :=
  regsStack .even g ++ suffixStack (finalSuffix ret xoff xend) ++ rest

def entryState (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 5066
    stack := entryStack g ret xoff xend rest }

def outputHash (s : State) (g : PackedStepCorrected.Regs) :
    Compression.EvmHashState :=
  PackedCombine.packedCombine (StackMemory.hashAt s.memory) g

def outputMemory (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  let h := outputHash s g
  PackedCombineMemory.writeHash s.memory h.h0 h.h1 h.h2 h.h3 h.h4

/-- State immediately before the dynamic return jump. -/
def preJumpState (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 5169
    stack := ret :: xoff :: xend :: rest
    memory := outputMemory s g }

/-- State after the return jump.  `ret` is fixed to PC 466 at the concrete
driver call site, while the raw evaluator remains useful for any certified
jump destination. -/
def resultState (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := ret
    stack := xoff :: xend :: rest
    memory := outputMemory s g }

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  have hofNat (word : UInt256) : UInt256.ofNat word.toNat = word := by
    cases word with
    | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, hofNat]

private theorem mask32_push (value : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff) value =
      Challenge.EvmProof.Word.mask32 value := by
  unfold Challenge.EvmProof.Word.mask32
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm
    (UInt256.ofNat 0xffffffff) value

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

/-- The machine computes `right + left` because the right-lane extraction is
on top of the stack.  This is the sole operand-order normalization needed to
reuse `PackedCombine.packedCombine` verbatim. -/
private theorem combine_add (hash left right : UInt256) :
    hash + (right + left) = hash + left + right := by
  rw [Challenge.EvmProof.Word.word_add_comm right left]
  exact (word_add_assoc hash left right).symm

private def stored0 (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  PackedGapInvariant.storeWord s.memory 352 (outputHash s g).h0

private def stored1 (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  PackedGapInvariant.storeWord (stored0 s g) 384 (outputHash s g).h1

private def stored2 (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  PackedGapInvariant.storeWord (stored1 s g) 416 (outputHash s g).h2

private def stored3 (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  PackedGapInvariant.storeWord (stored2 s g) 448 (outputHash s g).h3

private def stored4 (s : State) (g : PackedStepCorrected.Regs) : ByteArray :=
  PackedGapInvariant.storeWord (stored3 s g) 480 (outputHash s g).h4

private def retainedStack (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256) : List UInt256 :=
  MachineState.readWord s.memory 352 :: entryStack g ret xoff xend rest

private theorem read_after_store (memory : ByteArray) (writeStart readStart : Nat)
    (value : UInt256) (h : writeStart + 32 ≤ readStart) :
    MachineState.readWord (PackedGapInvariant.storeWord memory writeStart value)
        readStart = MachineState.readWord memory readStart := by
  exact PackedPreprocessPreservation.readWord_storeWord_above
    memory writeStart readStart value h

private theorem read_after_writeBytes (memory : ByteArray)
    (writeStart readStart : Nat) (value : UInt256)
    (h : writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using h

private theorem read_after_writeNat (memory : ByteArray)
    (writeStart readStart value : Nat) (h : writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simpa [Data.Bytes.natToBytesPadded, ByteArray.size] using h

set_option linter.unusedSimpArgs false in
theorem run_combineBody (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001) (hrun : s.halt = .Running) :
    StackRoundTrace.runInstrSeq combineBody (entryState s g ret xoff xend rest) =
      some (preJumpState s g ret xoff xend rest) := by
  have hcap (n : Nat) (hn : n ≤ 23) : rest.length + n < 1024 := by omega
  have haw (offset : Nat) (hoff : offset + 32 ≤ 512) :
      s.activeWordsAfterUInt256 offset 32 = s.activeWords :=
    activeWordsAfterUInt256_eq s offset 32 (by omega)
  have haw352 := haw 352 (by decide)
  have haw384 := haw 384 (by decide)
  have haw416 := haw 416 (by decide)
  have haw448 := haw 448 (by decide)
  have haw480 := haw 480 (by decide)
  have hawMod : s.activeWords.toNat % 2 ^ 256 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have hawWord : UInt256.ofNat s.activeWords.toNat = s.activeWords := by
    cases s.activeWords with
    | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [combineBody, combine0, combine1, combine2, combine3, combine4, cleanup,
      entryState, entryStack, preJumpState, retainedStack,
      stored0, stored1, stored2, stored3, stored4,
      outputMemory, outputHash, PackedCombine.packedCombine,
      PackedCombineMemory.writeHash, PackedGapInvariant.storeWord,
      StackMemory.hashAt, PackedFrameControl.finalSuffix,
      PackedInitialFrame.initialSuffix, PackedStepFrame.regsStack,
      PackedStepFrame.suffixStack, StackRoundTrace.runInstrSeq,
      Challenge.EvmProof.Stepper.runInstr, push1, push2, dup,
      State.activeWordsAfterUInt256, activeWordsAfter_eq_of_end_le,
      activeWordsAfterUInt256_eq, haw, haw352, haw384, haw416, haw448, haw480,
      hactive, hstack, hrun, hcap,
      read_after_store, read_after_writeBytes, read_after_writeNat, mask32_push,
      combine_add,
      Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneInvariant.maskL,
      Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask.maskLN,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Nat.add_assoc, List.getElem?_cons_zero, List.getElem?_cons_succ]
  change UInt256.ofNat (s.activeWords.toNat % 2 ^ 256) = s.activeWords
  rw [hawMod, hawWord]

theorem run_returnJump (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1001)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    StackRoundTrace.runInstrSeq returnJump (preJumpState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
  have hcap : rest.length + 3 < 1024 := by omega
  simp [returnJump, preJumpState, resultState, StackRoundTrace.runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, hvalid, hcap]

private theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : StackRoundTrace.runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : StackRoundTrace.runInstrSeq second middle = some result) :
    StackRoundTrace.runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, StackRoundTrace.runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction tail ih =>
      cases hrun : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none => simp [StackRoundTrace.runInstrSeq, hrun] at hfirst
      | some next =>
          cases tail with
          | nil =>
              have hnext : next = middle := by
                simpa [StackRoundTrace.runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil => simpa [StackRoundTrace.runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondTail =>
                  simpa [StackRoundTrace.runInstrSeq, hrun, hmiddle] using hsecond
          | cons nextInstruction tailRest =>
              cases hhalt : next.halt with
              | Running =>
                  have htail : StackRoundTrace.runInstrSeq
                      (nextInstruction :: tailRest) next = some middle := by
                    simpa [StackRoundTrace.runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih htail hmiddle hsecond
                  simpa [StackRoundTrace.runInstrSeq, hrun, hhalt] using hjoined
              | Success => simp [StackRoundTrace.runInstrSeq, hrun, hhalt] at hfirst
              | Returned => simp [StackRoundTrace.runInstrSeq, hrun, hhalt] at hfirst
              | Reverted => simp [StackRoundTrace.runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [StackRoundTrace.runInstrSeq, hrun, hhalt] at hfirst

theorem run_combineTail (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    StackRoundTrace.runInstrSeq combineTail (entryState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
  have hbody := run_combineBody s g ret xoff xend rest hactive hstack hrun
  have hjump := run_returnJump s g ret xoff xend rest hstack hvalid
  exact runInstrSeq_append_running hbody
    (by simpa [preJumpState] using hrun) hjump

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineTrace
