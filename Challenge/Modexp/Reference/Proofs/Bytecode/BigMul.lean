import Challenge.Modexp.Reference.Proofs.Bytecode.BigHelpers
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified multi-limb modular multiplication

This module composes the certified clear, copy, and masked-add helpers with
the emitted constant-shape double-and-add loops for `mulModBig`.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigMul

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Reference.Proofs.Bytecode

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : BigHelpers.Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located BigHelpers.Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : BigHelpers.Artifact.referenceInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located BigHelpers.Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def mulToClearPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 265 .JUMPDEST, pushAt 266 2 320,
   opAt 267 (.Dup ⟨5, by decide⟩), opAt 268 (.Dup ⟨4, by decide⟩),
   pushAt 269 2 19, opAt 270 .JUMP]

def mulToCopyPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 271 .JUMPDEST, pushAt 272 2 333,
   opAt 273 (.Dup ⟨5, by decide⟩), opAt 274 (.Dup ⟨2, by decide⟩),
   pushAt 275 2 4096, pushAt 276 2 58, opAt 277 .JUMP]

def mulSetupPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 278 .JUMPDEST, pushAt 279 0 0]

def mulEntry (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 310
           stack := [a, b, out, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def mulAfterClear (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 320
           stack := [a, b, out, modulus, UInt256.ofNat count,
             returnDest] ++ rest
           memory := BigHelpers.clearMemory s.memory out count
           activeWords := BigHelpers.clearWords s.activeWords out count }

def mulAfterCopy (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let cleared := mulAfterClear s a b out modulus count returnDest rest
  { cleared with pc := UInt256.ofNat 333
      memory := BigHelpers.copyMemory cleared.memory (UInt256.ofNat 4096) a count
      activeWords := BigHelpers.copyWords cleared.activeWords
        (UInt256.ofNat 4096) a count }

def mulOuterLoop (s : State) (a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  { copied with pc := UInt256.ofNat 335
      stack := [UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
        returnDest] ++ rest }

@[simp] private theorem mulPCs (i : Nat) (hi : 265 ≤ i) (hii : i ≤ 279) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [310,311,314,315,316,319,320,321,324,325,326,329,332,333,334]
        [i - 265]! := by
  interval_cases i <;> decide

@[simp] private theorem jump19 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 19 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 15 (by rfl)

@[simp] private theorem jump58 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 58 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 46 (by rfl)

@[simp] private theorem jump320 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 320 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 271 (by rfl)

@[simp] private theorem jump333 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 333 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 278 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_mulToClear (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hcode : s.executionEnv.code =
      BigHelpers.referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulToClearPath
      (mulEntry s a b out modulus count returnDest rest) =
    some (BigHelpers.clearEntry s out count (UInt256.ofNat 320)
      ([a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest)) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (19 : UInt256).toNat = true := by simpa using jump19
  simp [mulToClearPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulEntry, BigHelpers.clearEntry, mulPCs, hcode, hrun, hvalid, jump19,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulToCopy (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hcode : s.executionEnv.code =
      BigHelpers.referenceBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulToCopyPath
      (mulAfterClear s a b out modulus count returnDest rest) =
    some (BigHelpers.copyEntry (mulAfterClear s a b out modulus count
      returnDest rest) (UInt256.ofNat 4096) a count (UInt256.ofNat 333)
      ([a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest)) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (58 : UInt256).toNat = true := by simpa using jump58
  simp [mulToCopyPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterClear, BigHelpers.copyEntry, mulPCs, hcode, hrun, hvalid, jump58,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulSetup (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1012) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulSetupPath
      (mulAfterCopy s a b out modulus count returnDest rest) =
    some (mulOuterLoop s a b out modulus count 0 returnDest rest) := by
  simp [mulSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterCopy, mulAfterClear, mulOuterLoop, mulPCs, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_mulInitialize (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (mulOuterLoop s a b out modulus count 0 returnDest rest) := by
  let saved := [a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest
  have htoClear := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulToClearPath
      (by simpa [mulEntry, BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [mulEntry, State.fork] using hfork)
      (run_mulToClear s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulEntry] using hrun)
      (by simpa [mulEntry, State.fork] using hnp)
  have hclear := BigHelpers.gasSteps_clear s out count (UInt256.ofNat 320)
    saved (by simp [saved]; omega) hcount hcode hfork hrun hnp (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 320 < 2 ^ 256)]
      exact jump320)
  have hclear' : Challenge.EvmProof.GasSteps
      (BigHelpers.clearEntry s out count (UInt256.ofNat 320) saved)
      (mulAfterClear s a b out modulus count returnDest rest) := by
    simpa [saved, mulAfterClear, BigHelpers.clearReturned] using hclear
  have htoCopy := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulToCopyPath
      (by simpa [mulAfterClear, BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [mulAfterClear, State.fork] using hfork)
      (run_mulToCopy s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulAfterClear] using hrun)
      (by simpa [mulAfterClear, State.fork] using hnp)
  have hcopy := BigHelpers.gasSteps_copy
    (mulAfterClear s a b out modulus count returnDest rest)
    (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved
    (by simp [saved]; omega) hcount
    (by simpa [mulAfterClear] using hcode)
    (by simpa [mulAfterClear, State.fork] using hfork)
    (by simpa [mulAfterClear] using hrun)
    (by simpa [mulAfterClear, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 333 < 2 ^ 256)]
      exact jump333)
  have hcopy' : Challenge.EvmProof.GasSteps
      (BigHelpers.copyEntry (mulAfterClear s a b out modulus count
        returnDest rest) (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved)
      (mulAfterCopy s a b out modulus count returnDest rest) := by
    simpa [saved, mulAfterCopy, BigHelpers.copyReturned] using hcopy
  have hsetup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulSetupPath
      (by simpa [mulAfterCopy, mulAfterClear,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hfork)
      (run_mulSetup s a b out modulus count returnDest rest (by omega) hrun)
      (by simpa [mulAfterCopy, mulAfterClear] using hrun)
      (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hnp)
  exact htoClear.trans <| hclear'.trans <| htoCopy.trans <|
    hcopy'.trans hsetup

end Challenge.Modexp.Reference.Proofs.Bytecode.BigMul
