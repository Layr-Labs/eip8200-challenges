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

def mulDoubleToNextPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 323 .JUMPDEST, opAt 324 .POP, pushAt 325 1 1,
   opAt 326 (.Dup ⟨1, by decide⟩), opAt 327 .ADD,
   opAt 328 (.Swap ⟨0, by decide⟩), opAt 329 .POP,
   pushAt 330 2 352, opAt 331 .JUMP]

def mulInnerToOuterPath :
    List (Challenge.EvmProof.Stepper.Located
      BigHelpers.Artifact.referenceArtifact .Osaka) :=
  [opAt 332 .JUMPDEST, opAt 333 .POP, opAt 334 .POP,
   pushAt 335 1 1, opAt 336 (.Dup ⟨1, by decide⟩), opAt 337 .ADD,
   opAt 338 (.Swap ⟨0, by decide⟩), opAt 339 .POP,
   pushAt 340 2 335, opAt 341 .JUMP]

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

/-- Inner-loop state with the multiplier word fixed after its single `MLOAD`.
This form is used to iterate all 256 bits without re-reading memory. -/
def mulInnerState (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 352
      stack := [UInt256.ofNat j, word, UInt256.ofNat i, a, b, out, modulus,
        UInt256.ofNat count, returnDest] ++ rest }

def mulWordBit (word : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat j)) (UInt256.ofNat 1)

def mulWordRest (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [mulWordBit word j, UInt256.ofNat j, word, UInt256.ofNat i, a, b, out,
    modulus, UInt256.ofNat count, returnDest] ++ rest

def mulWordAfterAdd (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned inner out (UInt256.ofNat 4096) (mulWordBit word j)
    modulus count (UInt256.ofNat 383)
    (mulWordRest word a b out modulus count i j returnDest rest)

def mulWordAfterDouble (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned afterAdd (UInt256.ofNat 4096) (UInt256.ofNat 4096)
    (UInt256.ofNat 1) modulus count (UInt256.ofNat 401)
    (mulWordRest word a b out modulus count i j returnDest rest)

def mulWordInnerNext (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let doubled := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  mulInnerState doubled word a b out modulus count i (j + 1) returnDest rest

def mulWordBits (word : UInt256) (length : Nat) : List Nat :=
  (List.range length).map fun j => (mulWordBit word j).toNat

def mulWordProgress (current : State) (word a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : Nat → State
  | 0 => current
  | j + 1 => mulWordAfterDouble
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest

@[simp] theorem mulWordProgress_executionEnv (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (mulWordProgress current word a b out modulus count i returnDest rest j)
        .executionEnv = current.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [mulWordProgress, mulWordAfterDouble, mulWordAfterAdd,
        BigHelpers.addReturned, ih]

@[simp] theorem mulWordProgress_halt (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    (mulWordProgress current word a b out modulus count i returnDest rest j)
        .halt = current.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [mulWordProgress, mulWordAfterDouble, mulWordAfterAdd,
        BigHelpers.addReturned, ih]

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

theorem mulBit_toNat_le_one (current : State) (b : UInt256) (i j : Nat) :
    (mulBit current b i j).toNat ≤ 1 := by
  rw [mulBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_right

theorem mulWordBit_toNat_le_one (word : UInt256) (j : Nat) :
    (mulWordBit word j).toNat ≤ 1 := by
  rw [mulWordBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_right

def mulBitRest (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) :
    List UInt256 :=
  [mulBit current b i j, UInt256.ofNat j,
    MachineState.readWord current.memory
      (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat,
    UInt256.ofNat i, a, b, out, modulus, UInt256.ofNat count,
    returnDest] ++ rest

def mulAfterBitAdd (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  BigHelpers.addReturned inner out (UInt256.ofNat 4096) bit modulus count
    (UInt256.ofNat 383)
    (mulBitRest current a b out modulus count i j returnDest rest)

def mulAfterBitDouble (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  BigHelpers.addReturned afterAdd (UInt256.ofNat 4096) (UInt256.ofNat 4096)
    (UInt256.ofNat 1) modulus count (UInt256.ofNat 401)
    (mulBitRest current a b out modulus count i j returnDest rest)

def mulInnerNext (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  let doubled := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  let word := MachineState.readWord current.memory
    (b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat
  { doubled with pc := UInt256.ofNat 352
      stack := [UInt256.ofNat (j + 1), word, UInt256.ofNat i, a, b, out,
        modulus, UInt256.ofNat count, returnDest] ++ rest }

def mulOuterNext (inner : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { inner with pc := UInt256.ofNat 335
      stack := [UInt256.ofNat (i + 1), a, b, out, modulus,
        UInt256.ofNat count, returnDest] ++ rest }

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

@[simp] private theorem mulNextPCs (i : Nat) (hi : 323 ≤ i) (hii : i ≤ 331) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [401,402,403,405,406,407,408,409,412][i - 323]! := by
  interval_cases i <;> decide

@[simp] private theorem mulInnerExitPCs (i : Nat) (hi : 332 ≤ i)
    (hii : i ≤ 341) :
    BigHelpers.Artifact.referenceArtifact.instructionPC i =
      [413,414,415,416,418,419,420,421,422,425][i - 332]! := by
  interval_cases i <;> decide

@[simp] private theorem jump335 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 335 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 280 (by rfl)

@[simp] private theorem jump352 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 352 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 294 (by rfl)

@[simp] private theorem jump383 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 383 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 314 (by rfl)

@[simp] private theorem jump401 :
    Decode.isValidJumpDest BigHelpers.referenceBytecode 401 = true :=
  BigHelpers.Artifact.isValidJumpDest_index 323 (by rfl)

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
theorem run_mulWordInnerGuard (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hj : j < 256)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerState current word a b out modulus count i j returnDest rest) =
    some { mulInnerState current word a b out modulus count i j returnDest rest
      with pc := UInt256.ofNat 363 } := by
  have hlt : j % 2 ^ 256 < 256 % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)]
    exact hj
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerState, mulLoopPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerFinishGuard (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hcode : current.executionEnv.code =
      BigHelpers.referenceBytecode) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerGuardPath
      (mulInnerLoop current a b out modulus count i 256 returnDest rest) =
    some { mulInnerLoop current a b out modulus count i 256 returnDest rest with
      pc := UInt256.ofNat 413 } := by
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (413 : UInt256).toNat = true := by simpa using jump413
  simp [mulInnerGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulLoopPCs, hcode, hrun, UInt256.lt, UInt256.isTrue,
    hzeroFalse, hvalid, jump413,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_mulInnerToOuter (current : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hi : i + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerLoop current a b out modulus count i 256 returnDest rest
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToOuterPath
      { inner with pc := UInt256.ofNat 413 } =
    some (mulOuterNext inner a b out modulus count i returnDest rest) := by
  dsimp only
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (335 : UInt256).toNat = true := by simpa using jump335
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat (a := i) (b := 1) hi
  simp [mulInnerToOuterPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulInnerLoop, mulOuterNext, mulInnerExitPCs, hcode, hrun, hvalid,
    jump335, hinc, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    List.exchange]

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
theorem run_mulWordInnerToAdd (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulInnerToAddPath
      { mulInnerState current word a b out modulus count i j returnDest rest with
        pc := UInt256.ofNat 363 } =
    some (BigHelpers.addEntry
      (mulInnerState current word a b out modulus count i j returnDest rest)
      out (UInt256.ofNat 4096) (mulWordBit word j) modulus count
      (UInt256.ofNat 383)
      (mulWordRest word a b out modulus count i j returnDest rest)) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (104 : UInt256).toNat = true := by simpa using jump104
  simp (config := { maxSteps := 500000 })
    [mulInnerToAddPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulInnerState, mulWordBit, mulWordRest, BigHelpers.addEntry,
      mulInnerPCs, hcode, hrun, hvalid, jump104,
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

set_option linter.unusedSimpArgs false in
theorem run_mulWordAddToDouble (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    let inner := mulInnerState current word a b out modulus count i j
      returnDest rest
    let saved := mulWordRest word a b out modulus count i j returnDest rest
    let afterAdd := mulWordAfterAdd current word a b out modulus count i j
      returnDest rest
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
      mulWordAfterAdd, BigHelpers.addReturned, BigHelpers.addEntry,
      mulInnerPCs, hcode, hrun, hvalid, jump104,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulDoubleToNext (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulDoubleToNextPath
      (mulAfterBitDouble current a b out modulus count i j returnDest rest) =
    some (mulInnerNext current a b out modulus count i j returnDest rest) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (352 : UInt256).toNat = true := by simpa using jump352
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) hj
  simp (config := { maxSteps := 400000 })
    [mulDoubleToNextPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulAfterBitDouble, mulAfterBitAdd, mulInnerNext, mulBitRest,
      BigHelpers.addReturned, mulNextPCs, hcode, hrun, hvalid, jump352, hinc,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_mulWordDoubleToNext (current : State) (word a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1008) (hj : j + 1 < 2 ^ 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulDoubleToNextPath
      (mulWordAfterDouble current word a b out modulus count i j
        returnDest rest) =
    some (mulWordInnerNext current word a b out modulus count i j
      returnDest rest) := by
  have hvalid : Decode.isValidJumpDest BigHelpers.referenceBytecode
      (352 : UInt256).toNat = true := by simpa using jump352
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) hj
  simp (config := { maxSteps := 400000 })
    [mulDoubleToNextPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      mulWordAfterDouble, mulWordAfterAdd, mulWordInnerNext, mulWordRest,
      mulInnerState, BigHelpers.addReturned, mulNextPCs, hcode, hrun,
      hvalid, jump352, hinc,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

def gasSteps_mulBitIteration (current : State) (a b out modulus : UInt256)
    (count i j : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerLoop current a b out modulus count i j returnDest rest)
      (mulInnerNext current a b out modulus count i j returnDest rest) := by
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  let saved := mulBitRest current a b out modulus count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  let afterDouble := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulInnerGuardPath
      (by simpa [inner, mulInnerLoop,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (run_mulInnerGuard current a b out modulus count i j returnDest rest
        (by omega) hj hrun)
      (by simpa [inner, mulInnerLoop] using hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hnp)
  have htoAdd := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulInnerToAddPath
      (by simpa [inner, mulInnerLoop,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (run_mulInnerToAdd current a b out modulus count i j returnDest rest
        (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerLoop] using hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod inner out (UInt256.ofNat 4096)
    bit modulus count (UInt256.ofNat 383) saved (by simp [saved]; omega)
    hcount (by simpa [inner, mulInnerLoop] using hcode)
    (by simpa [inner, mulInnerLoop, State.fork] using hfork)
    (by simpa [inner, mulInnerLoop] using hrun)
    (by simpa [inner, mulInnerLoop, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have hadd' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry inner out (UInt256.ofNat 4096) bit modulus count
        (UInt256.ofNat 383) saved) afterAdd := by
    simpa [afterAdd, mulAfterBitAdd, inner, bit, saved] using hadd
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulAddToDoublePath
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterAdd, mulAfterBitAdd, inner, bit, saved] using
        run_mulAddToDouble current a b out modulus count i j returnDest rest
          (by omega) hcode hrun)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned] using hrun)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved (by simp [saved]; omega) hcount
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hdouble' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) afterDouble := by
    simpa [afterDouble, mulAfterBitDouble, afterAdd, saved] using hdouble
  have hnext := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulDoubleToNextPath
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterDouble] using run_mulDoubleToNext current a b out modulus
        count i j returnDest rest (by omega) (by omega) hcode hrun)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned] using hrun)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hnp)
  exact hguard.trans <| htoAdd.trans <| hadd'.trans <|
    htoDouble.trans <| hdouble'.trans hnext

def gasSteps_mulWordBitIteration (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerState current word a b out modulus count i j returnDest rest)
      (mulWordInnerNext current word a b out modulus count i j
        returnDest rest) := by
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  let bit := mulWordBit word j
  let saved := mulWordRest word a b out modulus count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  let afterDouble := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulInnerGuardPath
      (by simpa [inner, mulInnerState,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (run_mulWordInnerGuard current word a b out modulus count i j returnDest
        rest (by omega) hj hrun)
      (by simpa [inner, mulInnerState] using hrun)
      (by simpa [inner, mulInnerState, State.fork] using hnp)
  have htoAdd := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulInnerToAddPath
      (by simpa [inner, mulInnerState,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (run_mulWordInnerToAdd current word a b out modulus count i j returnDest
        rest (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerState] using hrun)
      (by simpa [inner, mulInnerState, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod inner out (UInt256.ofNat 4096)
    bit modulus count (UInt256.ofNat 383) saved (by simp [saved]; omega)
    hcount (by simpa [inner, mulInnerState] using hcode)
    (by simpa [inner, mulInnerState, State.fork] using hfork)
    (by simpa [inner, mulInnerState] using hrun)
    (by simpa [inner, mulInnerState, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have hadd' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry inner out (UInt256.ofNat 4096) bit modulus count
        (UInt256.ofNat 383) saved) afterAdd := by
    simpa [afterAdd, mulWordAfterAdd, inner, bit, saved] using hadd
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulAddToDoublePath
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterAdd, mulWordAfterAdd, inner, saved] using
        run_mulWordAddToDouble current word a b out modulus count i j returnDest
          rest (by omega) hcode hrun)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned] using hrun)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved (by simp [saved]; omega) hcount
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hdouble' : Challenge.EvmProof.GasSteps
      (BigHelpers.addEntry afterAdd (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 401) saved) afterDouble := by
    simpa [afterDouble, mulWordAfterDouble, afterAdd, saved] using hdouble
  have hnext := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    BigHelpers.Artifact.referenceArtifact .Osaka mulDoubleToNextPath
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned,
        BigHelpers.Artifact.referenceArtifact] using hcode)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hfork)
      (by simpa [afterDouble] using run_mulWordDoubleToNext current word a b out
        modulus count i j returnDest rest (by omega) (by omega) hcode hrun)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned] using hrun)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hnp)
  exact hguard.trans <| htoAdd.trans <| hadd'.trans <|
    htoDouble.trans <| hdouble'.trans hnext

def gasSteps_mulWordLoop (current : State) (word a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulInnerState current word a b out modulus count i 0 returnDest rest)
      (mulInnerState
        (mulWordProgress current word a b out modulus count i returnDest rest 256)
        word a b out modulus count i 256 returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded 256 fun j hj =>
    gasSteps_mulWordBitIteration
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest hcap hcount hj
      (by simpa using hcode)
      (by simpa [State.fork] using hfork)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)

theorem mulAfterBitDouble_represents (current : State) (a b : UInt256)
    (count i j acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let doubled := mulAfterBitDouble current a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i j returnDest rest
    let bit := (mulBit current b i j).toNat
    Limbs.Represents doubled.memory 3072 count
        ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 4096 count
        ((addend + addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 0 count modulusValue := by
  let inner := mulInnerLoop current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let bitWord := mulBit current b i j
  let bit := bitWord.toNat
  let saved := mulBitRest current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let doubled := mulAfterBitDouble current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  have hbitLe : bit ≤ 1 := mulBit_toNat_le_one current b i j
  have hbitWord : bitWord = UInt256.ofNat bit :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat bitWord
  have hfit0 : 0 + 32 * count < 2 ^ 256 := by omega
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  have hinnerAcc : Limbs.Represents inner.memory 3072 count acc := by
    simpa [inner, mulInnerLoop] using hacc
  have hinnerAddend : Limbs.Represents inner.memory 4096 count addend := by
    simpa [inner, mulInnerLoop] using haddend
  have hinnerModulus : Limbs.Represents inner.memory 0 count modulusValue := by
    simpa [inner, mulInnerLoop] using hmodulus
  have hafterAcc : Limbs.Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    rw [hbitWord]
    exact BigHelpers.addReturned_represents_mod inner 3072 4096 0 count bit
      acc addend modulusValue (UInt256.ofNat 383) saved hbitLe hfit3072
      hfit4096 hfit0 hfit5120 (by right; left; omega) (by right; omega)
      (by left; omega) (by left; omega) hinnerAcc hinnerAddend
      hinnerModulus haccReduced haddendReduced hmodulusBound
  have hafterAddend : Limbs.Represents afterAdd.memory 4096 count addend := by
    rw [hbitWord]
    exact BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 4096
      count addend (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by left; omega) (by left; omega) hinnerAddend
  have hafterModulus :
      Limbs.Represents afterAdd.memory 0 count modulusValue := by
    rw [hbitWord]
    exact BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 0
      count modulusValue (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by right; omega) (by left; omega) hinnerModulus
  have hdoubleAddend : Limbs.Represents doubled.memory 4096 count
      ((addend + addend) % modulusValue) := by
    exact BigHelpers.addReturned_represents_mod afterAdd 4096 4096 0 count 1
      addend addend modulusValue (UInt256.ofNat 401) saved (by omega)
      hfit4096 hfit4096 hfit0 hfit5120 (by left) (by right; omega)
      (by left; omega) (by left; omega) hafterAddend hafterAddend
      hafterModulus haddendReduced haddendReduced hmodulusBound
  have hdoubleAcc : Limbs.Represents doubled.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 3072
      count ((acc + bit * addend) % modulusValue) (UInt256.ofNat 401) saved
      hfit4096 hfit5120 (by right; omega) (by left; omega) hafterAcc
  have hdoubleModulus :
      Limbs.Represents doubled.memory 0 count modulusValue := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 0
      count modulusValue (UInt256.ofNat 401) saved hfit4096 hfit5120
      (by right; omega) (by left; omega) hafterModulus
  exact ⟨hdoubleAcc, hdoubleAddend, hdoubleModulus⟩

theorem mulWordAfterDouble_represents (current : State) (word a b : UInt256)
    (count i j acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let doubled := mulWordAfterDouble current word a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i j returnDest rest
    let bit := (mulWordBit word j).toNat
    Limbs.Represents doubled.memory 3072 count
        ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 4096 count
        ((addend + addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 0 count modulusValue := by
  let inner := mulInnerState current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let bitWord := mulWordBit word j
  let bit := bitWord.toNat
  let saved := mulWordRest word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  let doubled := mulWordAfterDouble current word a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count i j returnDest rest
  have hbitLe : bit ≤ 1 := mulWordBit_toNat_le_one word j
  have hbitWord : bitWord = UInt256.ofNat bit :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat bitWord
  have hfit0 : 0 + 32 * count < 2 ^ 256 := by omega
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  have hinnerAcc : Limbs.Represents inner.memory 3072 count acc := by
    simpa [inner, mulInnerState] using hacc
  have hinnerAddend : Limbs.Represents inner.memory 4096 count addend := by
    simpa [inner, mulInnerState] using haddend
  have hinnerModulus : Limbs.Represents inner.memory 0 count modulusValue := by
    simpa [inner, mulInnerState] using hmodulus
  have hafterAcc : Limbs.Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    rw [hbitWord]
    exact BigHelpers.addReturned_represents_mod inner 3072 4096 0 count bit
      acc addend modulusValue (UInt256.ofNat 383) saved hbitLe hfit3072
      hfit4096 hfit0 hfit5120 (by right; left; omega) (by right; omega)
      (by left; omega) (by left; omega) hinnerAcc hinnerAddend
      hinnerModulus haccReduced haddendReduced hmodulusBound
  have hafterAddend : Limbs.Represents afterAdd.memory 4096 count addend := by
    rw [hbitWord]
    exact BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 4096
      count addend (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by left; omega) (by left; omega) hinnerAddend
  have hafterModulus :
      Limbs.Represents afterAdd.memory 0 count modulusValue := by
    rw [hbitWord]
    exact BigHelpers.addReturned_preserves_region inner 3072 4096 bit 0 0
      count modulusValue (UInt256.ofNat 383) saved hfit3072 hfit5120
      (by right; omega) (by left; omega) hinnerModulus
  have hdoubleAddend : Limbs.Represents doubled.memory 4096 count
      ((addend + addend) % modulusValue) := by
    exact BigHelpers.addReturned_represents_mod afterAdd 4096 4096 0 count 1
      addend addend modulusValue (UInt256.ofNat 401) saved (by omega)
      hfit4096 hfit4096 hfit0 hfit5120 (by left) (by right; omega)
      (by left; omega) (by left; omega) hafterAddend hafterAddend
      hafterModulus haddendReduced haddendReduced hmodulusBound
  have hdoubleAcc : Limbs.Represents doubled.memory 3072 count
      ((acc + bit * addend) % modulusValue) := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 3072
      count ((acc + bit * addend) % modulusValue) (UInt256.ofNat 401) saved
      hfit4096 hfit5120 (by right; omega) (by left; omega) hafterAcc
  have hdoubleModulus :
      Limbs.Represents doubled.memory 0 count modulusValue := by
    exact BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 0
      count modulusValue (UInt256.ofNat 401) saved hfit4096 hfit5120
      (by right; omega) (by left; omega) hafterModulus
  exact ⟨hdoubleAcc, hdoubleAddend, hdoubleModulus⟩

theorem mulWordProgress_represents (current : State) (word a b : UInt256)
    (count i steps acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hsteps : steps ≤ 256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := mulWordProgress current word a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count i returnDest rest steps
    let result := Algorithm.mulBits modulusValue acc addend
      (mulWordBits word steps)
    Limbs.Represents progress.memory 3072 count result.1 ∧
      Limbs.Represents progress.memory 4096 count result.2 ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  induction steps with
  | zero =>
      simp [mulWordProgress, mulWordBits, Algorithm.mulBits, hacc, haddend,
        hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ 256 := by omega
      let before := mulWordProgress current word a b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count i returnDest rest steps
      let beforeResult := Algorithm.mulBits modulusValue acc addend
        (mulWordBits word steps)
      have hbefore := ih hsteps'
      have hbeforeReduced := Algorithm.mulBits_lt (mulWordBits word steps)
        hmodulusPos haccReduced haddendReduced
      have hstep := mulWordAfterDouble_represents before word a b count i steps
        beforeResult.1 beforeResult.2 modulusValue returnDest rest hcount
        hmodulusPos hmodulusBound hbefore.1 hbefore.2.1 hbefore.2.2
        hbeforeReduced.1 hbeforeReduced.2
      simpa [mulWordProgress, mulWordBits, List.range_succ,
        List.map_append, Algorithm.mulBits_append, Algorithm.mulBits,
        before, beforeResult] using hstep

theorem gasSteps_mulBitIteration_cost_potential (current : State)
    (a b out modulus : UInt256) (count i j : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulBitIteration current a b out modulus count i j returnDest rest
        hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulInnerLoop current a b out modulus count i j returnDest rest).activeWords.toNat =
      (423 + count * 906) + MachineState.memCost
        (mulInnerNext current a b out modulus count i j returnDest rest).activeWords.toNat := by
  let inner := mulInnerLoop current a b out modulus count i j returnDest rest
  let bit := mulBit current b i j
  let saved := mulBitRest current a b out modulus count i j returnDest rest
  let afterAdd := mulAfterBitAdd current a b out modulus count i j
    returnDest rest
  let afterDouble := mulAfterBitDouble current a b out modulus count i j
    returnDest rest
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 25
      (run_mulInnerGuard current a b out modulus count i j returnDest rest
        (by omega) hj hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (by native_decide) (by rfl)
  have htoAdd := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToAddPath 44
      (run_mulInnerToAdd current a b out modulus count i j returnDest rest
        (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerLoop, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hadd := BigHelpers.gasSteps_addMaskedMod_cost_potential inner out
    (UInt256.ofNat 4096) bit modulus count (UInt256.ofNat 383) saved
    (by simp [saved]; omega) hcount
    (by simpa [inner, mulInnerLoop] using hcode)
    (by simpa [inner, mulInnerLoop, State.fork] using hfork)
    (by simpa [inner, mulInnerLoop] using hrun)
    (by simpa [inner, mulInnerLoop, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have htoDouble :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      mulAddToDoublePath 29
      (by simpa [afterAdd, mulAfterBitAdd, inner, bit, saved] using
        run_mulAddToDouble current a b out modulus count i j returnDest rest
          (by omega) hcode hrun)
      (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
        BigHelpers.addReturned, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hdouble := BigHelpers.gasSteps_addMaskedMod_cost_potential afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved (by simp [saved]; omega) hcount
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulAfterBitAdd, inner, mulInnerLoop,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulDoubleToNextPath 27
      (by simpa [afterDouble] using run_mulDoubleToNext current a b out modulus
        count i j returnDest rest (by omega) (by omega) hcode hrun)
      (by simpa [afterDouble, mulAfterBitDouble, mulAfterBitAdd, inner,
        mulInnerLoop, BigHelpers.addReturned, State.fork] using hfork)
      (by native_decide) (by rfl)
  unfold gasSteps_mulBitIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  omega

theorem gasSteps_mulWordBitIteration_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i j : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulWordBitIteration current word a b out modulus count i j
      returnDest rest hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (mulInnerState current word a b out modulus count i j
            returnDest rest).activeWords.toNat =
      (423 + count * 906) + MachineState.memCost
        (mulWordInnerNext current word a b out modulus count i j
          returnDest rest).activeWords.toNat := by
  let inner := mulInnerState current word a b out modulus count i j
    returnDest rest
  let bit := mulWordBit word j
  let saved := mulWordRest word a b out modulus count i j returnDest rest
  let afterAdd := mulWordAfterAdd current word a b out modulus count i j
    returnDest rest
  let afterDouble := mulWordAfterDouble current word a b out modulus count i j
    returnDest rest
  have hguard := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerGuardPath 25
      (run_mulWordInnerGuard current word a b out modulus count i j returnDest
        rest (by omega) hj hrun)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (by native_decide) (by rfl)
  have htoAdd := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulInnerToAddPath 44
      (run_mulWordInnerToAdd current word a b out modulus count i j returnDest
        rest (by omega) hj hcode hrun)
      (by simpa [inner, mulInnerState, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hadd := BigHelpers.gasSteps_addMaskedMod_cost_potential inner out
    (UInt256.ofNat 4096) bit modulus count (UInt256.ofNat 383) saved
    (by simp [saved]; omega) hcount
    (by simpa [inner, mulInnerState] using hcode)
    (by simpa [inner, mulInnerState, State.fork] using hfork)
    (by simpa [inner, mulInnerState] using hrun)
    (by simpa [inner, mulInnerState, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 383 < 2 ^ 256)]
      exact jump383)
  have htoDouble :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      mulAddToDoublePath 29
      (by simpa [afterAdd, mulWordAfterAdd, inner, saved] using
        run_mulWordAddToDouble current word a b out modulus count i j returnDest
          rest (by omega) hcode hrun)
      (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
        BigHelpers.addReturned, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hdouble := BigHelpers.gasSteps_addMaskedMod_cost_potential afterAdd
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus
    count (UInt256.ofNat 401) saved (by simp [saved]; omega) hcount
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hcode)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hfork)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned] using hrun)
    (by simpa [afterAdd, mulWordAfterAdd, inner, mulInnerState,
      BigHelpers.addReturned, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 401 < 2 ^ 256)]
      exact jump401)
  have hnext := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulDoubleToNextPath 27
      (by simpa [afterDouble] using run_mulWordDoubleToNext current word a b out
        modulus count i j returnDest rest (by omega) (by omega) hcode hrun)
      (by simpa [afterDouble, mulWordAfterDouble, mulWordAfterAdd, inner,
        mulInnerState, BigHelpers.addReturned, State.fork] using hfork)
      (by native_decide) (by rfl)
  unfold gasSteps_mulWordBitIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  omega

theorem gasSteps_mulWordLoop_cost_potential (current : State)
    (word a b out modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompile current.executionEnv.fork
      current.executionEnv.codeAddr = false) :
    (gasSteps_mulWordLoop current word a b out modulus count i returnDest rest
      hcap hcount hcode hfork hrun hnp).cost + MachineState.memCost
        (mulInnerState current word a b out modulus count i 0
          returnDest rest).activeWords.toNat =
      256 * (423 + count * 906) + MachineState.memCost
        (mulInnerState
          (mulWordProgress current word a b out modulus count i returnDest rest 256)
          word a b out modulus count i 256 returnDest rest).activeWords.toNat := by
  unfold gasSteps_mulWordLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro j hj
  simpa [mulWordInnerNext, mulWordProgress] using
    gasSteps_mulWordBitIteration_cost_potential
      (mulWordProgress current word a b out modulus count i returnDest rest j)
      word a b out modulus count i j returnDest rest hcap hcount hj
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)

theorem mulAfterCopy_represents (s : State) (bPtr count aValue bValue
    modulusValue : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32) (hbPtr : bPtr + 32 * count ≤ 3072)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    Limbs.Represents copied.memory 3072 count 0 ∧
      Limbs.Represents copied.memory 4096 count aValue ∧
      Limbs.Represents copied.memory bPtr count bValue ∧
      Limbs.Represents copied.memory 0 count modulusValue := by
  let cleared := mulAfterClear s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
  let copied := mulAfterCopy s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit2048 : 2048 + 32 * count < 2 ^ 256 := by omega
  have hclearedZero : Limbs.Represents cleared.memory 3072 count 0 := by
    exact BigHelpers.clearMemory_represents_zero s.memory 3072 count hfit3072
  have hclearedA : Limbs.Represents cleared.memory 2048 count aValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 2048
      count aValue hfit3072 (by right; omega) ha
  have hclearedB : Limbs.Represents cleared.memory bPtr count bValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 bPtr
      count bValue hfit3072 (by right; omega) hb
  have hclearedModulus :
      Limbs.Represents cleared.memory 0 count modulusValue := by
    exact BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 0
      count modulusValue hfit3072 (by right; omega) hmodulus
  have hcopiedAddend : Limbs.Represents copied.memory 4096 count aValue := by
    exact BigHelpers.copyMemory_represents cleared.memory 4096 2048 count aValue
      hclearedA hfit4096 hfit2048 (by right; omega)
  have hcopiedZero : Limbs.Represents copied.memory 3072 count 0 := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 3072 count 0 hfit4096 (by right; omega) hclearedZero
  have hcopiedB : Limbs.Represents copied.memory bPtr count bValue := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 bPtr count bValue hfit4096 (by right; omega) hclearedB
  have hcopiedModulus :
      Limbs.Represents copied.memory 0 count modulusValue := by
    exact BigHelpers.represents_copyMemory_disjoint_region cleared.memory 4096
      2048 0 count modulusValue hfit4096 (by right; omega) hclearedModulus
  exact ⟨hcopiedZero, hcopiedAddend, hcopiedB, hcopiedModulus⟩

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

theorem gasSteps_mulInitialize_cost_potential (s : State)
    (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = BigHelpers.referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_mulInitialize s a b out modulus count returnDest rest hcap
      hcount hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (135 + count * 158) + MachineState.memCost
        (mulOuterLoop s a b out modulus count 0 returnDest rest).activeWords.toNat := by
  let saved := [a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest
  let cleared := mulAfterClear s a b out modulus count returnDest rest
  let copied := mulAfterCopy s a b out modulus count returnDest rest
  have htoClear := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulToClearPath 20
      (run_mulToClear s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [mulEntry, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hclear := BigHelpers.gasSteps_clear_cost_potential s out count
    (UInt256.ofNat 320) saved (by simp [saved]; omega) hcount hcode hfork
    hrun hnp (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 320 < 2 ^ 256)]
      exact jump320)
  have htoCopy := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulToCopyPath 23
      (run_mulToCopy s a b out modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [cleared, mulAfterClear, State.fork] using hfork)
      (by native_decide) (by rfl)
  have hcopy := BigHelpers.gasSteps_copy_cost_potential cleared
    (UInt256.ofNat 4096) a count (UInt256.ofNat 333) saved
    (by simp [saved]; omega) hcount
    (by simpa [cleared, mulAfterClear] using hcode)
    (by simpa [cleared, mulAfterClear, State.fork] using hfork)
    (by simpa [cleared, mulAfterClear] using hrun)
    (by simpa [cleared, mulAfterClear, State.fork] using hnp) (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num : 333 < 2 ^ 256)]
      exact jump333)
  have hsetup := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    mulSetupPath 2
      (run_mulSetup s a b out modulus count returnDest rest (by omega) hrun)
      (by simpa [copied, mulAfterCopy, mulAfterClear, State.fork] using hfork)
      (by native_decide) (by rfl)
  unfold gasSteps_mulInitialize
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigMul
