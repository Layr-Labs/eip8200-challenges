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

def mulOuterGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 280 .JUMPDEST, opAt 281 (.Dup ⟨5, by decide⟩),
   opAt 282 (.Dup ⟨1, by decide⟩), opAt 283 .LT, opAt 284 .ISZERO,
   pushAt 285 2 426, opAt 286 .JUMPI]

def mulOuterLoadPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 287 (.Dup ⟨0, by decide⟩), pushAt 288 1 5, opAt 289 .SHL,
   opAt 290 (.Dup ⟨3, by decide⟩), opAt 291 .ADD, opAt 292 .MLOAD,
   pushAt 293 0 0]

def mulInnerGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 294 .JUMPDEST, pushAt 295 2 256,
   opAt 296 (.Dup ⟨1, by decide⟩), opAt 297 .LT, opAt 298 .ISZERO,
   pushAt 299 2 413, opAt 300 .JUMPI]

def mulInnerToAddPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [pushAt 301 1 1, opAt 302 (.Dup ⟨2, by decide⟩),
   opAt 303 (.Dup ⟨2, by decide⟩), opAt 304 .SHR, opAt 305 .AND,
   pushAt 306 2 383, opAt 307 (.Dup ⟨9, by decide⟩),
   opAt 308 (.Dup ⟨9, by decide⟩), opAt 309 (.Dup ⟨3, by decide⟩),
   pushAt 310 2 4096, opAt 311 (.Dup ⟨11, by decide⟩),
   pushAt 312 2 104, opAt 313 .JUMP]

def mulAddToDoublePath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 314 .JUMPDEST, pushAt 315 2 401,
   opAt 316 (.Dup ⟨9, by decide⟩), opAt 317 (.Dup ⟨9, by decide⟩),
   pushAt 318 1 1, pushAt 319 2 4096, pushAt 320 2 4096,
   pushAt 321 2 104, opAt 322 .JUMP]

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

def mulOuterBody (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 344
      stack := [UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
        returnDest] ++ rest }

def mulInnerLoop (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let bAt := b + off
  let word := MachineState.readWord current.memory bAt.toNat
  { current with pc := UInt256.ofNat 352
      stack := [UInt256.ofNat j, word, UInt256.ofNat i, a, b, out, modulus,
        UInt256.ofNat count, returnDest] ++ rest
      activeWords := UInt256.ofNat (MachineState.activeWordsAfter
        current.activeWords.toNat bAt.toNat 32) }

def mulBit (current : State) (b : UInt256) (i j : Nat) : UInt256 :=
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let word := MachineState.readWord current.memory (b + off).toNat
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat j)) (UInt256.ofNat 1)

def mulBitRest (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [mulBit current b i j, UInt256.ofNat j,
    MachineState.readWord current.memory
      (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat,
    UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
    returnDest] ++ rest

@[simp] private theorem mulPCs (i : Nat) (hi : 265 ≤ i) (hii : i ≤ 279) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [310,311,314,315,316,319,320,321,324,325,326,329,332,333,334]
        [i - 265]! := by
  interval_cases i <;> decide

@[simp] private theorem mulLoopPCs (i : Nat) (hi : 280 ≤ i) (hii : i ≤ 300) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [335,336,337,338,339,340,343,344,345,347,348,349,350,351,352,
       353,356,357,358,359,362][i - 280]! := by
  interval_cases i <;> decide

@[simp] private theorem mulInnerPCs (i : Nat) (hi : 301 ≤ i) (hii : i ≤ 322) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [363,365,366,367,368,369,372,373,374,375,378,379,382,383,384,
       387,388,389,391,394,397,400][i - 301]! := by
  interval_cases i <;> decide

@[simp] private theorem jump104 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 104 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 83 (by rfl)

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

@[simp] private theorem jump413 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 413 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 332 (by rfl)

@[simp] private theorem jump426 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 426 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 342 (by rfl)

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

set_option linter.unusedSimpArgs false in
theorem run_mulOuterGuard (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterGuardPath
      { current with pc := UInt256.ofNat 335
          stack := [UInt256.ofNat i, a, b, out, modulus,
            UInt256.ofNat count, returnDest] ++ rest } =
    some (mulOuterBody current a b out modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [mulOuterGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulOuterBody, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero]

set_option linter.unusedSimpArgs false in
theorem run_mulOuterLoad (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1014) (hi : i < 2 ^ 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulOuterLoadPath
      (mulOuterBody current a b out modulus count i returnDest rest) =
    some (mulInnerLoop current a b out modulus count i 0 returnDest rest) := by
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 300000 })
    [mulOuterLoadPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulOuterBody, mulInnerLoop, mulLoopPCs, hrun, hfive, hzero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerGuard (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hj : j < 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerLoop current a b out modulus count i j returnDest rest) =
    some { mulInnerLoop current a b out modulus count i j returnDest rest with
      pc := UInt256.ofNat 363 } := by
  have hlt : j % 2 ^ 256 < 256 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)]
    exact hj
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerToAdd (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToAddPath
      { mulInnerLoop current a b out modulus count i j returnDest rest with
        pc := UInt256.ofNat 363 } =
    some (BigHelpers.addEntry
      (mulInnerLoop current a b out modulus count i j returnDest rest)
      out (UInt256.ofNat 4096) (mulBit current b i j) modulus count
      (UInt256.ofNat 383)
      (mulBitRest current a b out modulus count i j returnDest rest)) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (104 : UInt256).toNat = true := by simpa using jump104
  simp (config := { maxSteps := 500000 })
    [mulInnerToAddPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulInnerLoop, mulBit, mulBitRest, BigHelpers.addEntry, mulInnerPCs,
      hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulAddToDouble (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerLoop current a b out modulus count i j returnDest rest
    let bit := mulBit current b i j
    let saved := mulBitRest current a b out modulus count i j returnDest rest
    let afterAdd := BigHelpers.addReturned inner out (UInt256.ofNat 4096) bit
      modulus count (UInt256.ofNat 383) saved
    Challenge.EvmProof.Stepper.runLocatedBlock mulAddToDoublePath afterAdd =
      some (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) := by
  dsimp only
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (104 : UInt256).toNat = true := by simpa using jump104
  simp (config := { maxSteps := 500000 })
    [mulAddToDoublePath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      BigHelpers.addReturned, BigHelpers.addEntry, mulInnerPCs,
      hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

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
