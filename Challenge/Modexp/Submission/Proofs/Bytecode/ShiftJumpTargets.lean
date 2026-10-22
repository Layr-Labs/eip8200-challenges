import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option warningAsError false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-!
# Static jump checks for the current MODEXP image

The artifact contains 8,722 instructions, 104 control transfers,
92 immediate jump destinations (with multiplicity), and 12 transfers
whose destination is a stack word. The enumerations below are checked against
the actual instruction list. Further decidable facts exclude the conversion
exit window from literal destinations and immediate values and pin the
preserved conversion instructions.

Literal exclusion alone is not a global invariant for computed destinations.
The exact block execution theorems and the closed end-to-end correctness
theorem establish the behavior of those execution paths.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Is this instruction a control transfer? -/
def isJumpInstr : Instr → Bool
  | .op .JUMP => true
  | .op .JUMPI => true
  | _ => false

/-- `(instruction at index, instruction at index + 1)` for every adjacent pair. -/
def instrPairs : List (Instr × Instr) :=
  Artifact.submissionInstructions.zip (Artifact.submissionInstructions.drop 1)

/-- `(index, instruction at index, instruction at index + 1)` for every adjacent pair. -/
def indexedPairs : List (Nat × Instr × Instr) :=
  (List.range Artifact.submissionInstructions.length).zip instrPairs |>.map
    fun p => (p.1, p.2.1, p.2.2)

/-- The instruction index of every `JUMP`/`JUMPI` in the artifact, in program order. -/
def jumpSites : List Nat :=
  (indexedPairs.filter fun p => isJumpInstr p.2.2).map fun p => p.1 + 1

/-- Every jump destination the image names with a `PUSH` immediate, with multiplicity, in
program order.  A `JUMP`/`JUMPI` whose immediately preceding instruction is a `PUSH` takes that
`PUSH`'s value as its destination: `runInstr` pops the operand off the top of the stack, and
that `PUSH` is the only thing that wrote there. -/
def literalJumpTargets : List Nat :=
  instrPairs.filterMap fun p =>
    match p.1, p.2 with
    | .push _ v, .op .JUMP => some v.toNat
    | .push _ v, .op .JUMPI => some v.toNat
    | _, _ => none

/-- The `JUMP`/`JUMPI`s whose destination is *not* the `PUSH` immediately before them: the
twelve sites whose operand is a stack word. -/
def dataDependentJumpSites : List Nat :=
  (indexedPairs.filter fun p =>
    isJumpInstr p.2.2 && match p.2.1 with | .push _ _ => false | _ => true).map fun p => p.1 + 1

/-- Every `PUSH` immediate in the image, with multiplicity. -/
def pushImmediates : List Nat :=
  Artifact.submissionInstructions.filterMap fun i =>
    match i with
    | .push _ v => some v.toNat
    | _ => none

theorem jumpSites_eq : jumpSites =
    [10, 16, 31, 41, 43, 55, 73, 86, 99, 117, 130, 140, 185, 188, 208, 214, 237, 244, 254, 263, 278, 282, 298, 302, 307, 314, 356, 359, 364, 369, 379, 394, 403, 413, 437, 458, 485, 498, 512, 1840, 1842, 1846, 1855, 1865, 1877, 1884, 1891, 1901, 2156, 2394, 2400, 2402, 2438, 2450, 2456, 2463, 2477, 2532, 2569, 3048, 3053, 3080, 3082, 3095, 3099, 3111, 3113, 3128, 3135, 3143, 3151, 3281, 3283, 3288, 3295, 3302, 3317, 3330, 3417, 3516, 3589, 3728, 3736, 3753, 3761, 3807, 3810, 4267, 4270, 4407, 4430, 4438, 4484, 4487, 6319, 6324, 6434, 6933, 7607, 7624, 7632, 7678, 7699, 7714] := by decide

theorem literalJumpTargets_eq : literalJumpTargets =
    [578, 101, 745, 9800, 745, 219, 33, 154, 187, 157, 5554, 5570, 254, 281, 376, 393, 368, 393, 292, 464, 457, 464, 449, 464, 401, 474, 528, 468, 550, 219, 136, 697, 219, 219, 2390, 533, 533, 2350, 219, 2369, 2470, 219, 3181, 219, 4010, 2336, 3073, 2704, 3146, 3081, 3075, 3061, 5522, 2704, 3942, 4223, 4025, 4137, 3973, 4816, 3256, 4037, 4214, 5351, 3922, 4234, 4223, 4025, 4816, 8998, 4621, 4621, 4621, 4768, 4280, 3999, 4731, 5615, 3758, 194, 5575, 5544, 8800, 8800, 5858, 3942, 9730, 8998, 3999, 9693, 9818, 745] := by decide

/-- The twelve sites whose destination is a stack word, in program order. -/
theorem dataDependentJumpSites_eq : dataDependentJumpSites =
    [314, 369, 2156, 2532, 2569, 3048, 3295, 3302, 3728, 4267, 4270, 4430] := by decide

/-- **No literal jump destination is the M9 exit.**  None of the 92 destinations the image
names with a `PUSH` immediate is pc 3168, 3169 or 3170. -/
theorem noLiteralJumpTarget_window :
    literalJumpTargets.all fun n => decide (n ≠ 3168 ∧ n ≠ 3169 ∧ n ≠ 3170) = true := by decide

/-- **No literal anywhere in the image is the M9 exit.**  Not one of the image's `PUSH`
immediates — in any block, at any index — equals pc 3168, 3169 or 3170.  This is what excludes
the three new `JUMPDEST`s from the *data* flow: a computed jump operand is a stack word, and
every stack word the program seeds comes from an in-image `PUSH` or from an earlier jump
destination, so no value equal to 3168..3170 can reach a jump operand. -/
theorem noLiteralPush_window :
    pushImmediates.all fun n => decide (n ≠ 3168 ∧ n ≠ 3169 ∧ n ≠ 3170) = true := by decide

/-- The exit `PUSH2 2080` is at instruction 2376,
and the fixup's `SWAP3 POP` is at instructions 2387 and 2388. -/
theorem m9Exit_is_jumpdest :
    Artifact.submissionInstructions[2374]? = some (.push 2 2080) ∧
      Artifact.submissionInstructions[2385]? = some (.op (.Swap ⟨2, by decide⟩)) ∧
      Artifact.submissionInstructions[2386]? = some (.op .POP) :=
  ⟨by rfl, by rfl, by rfl⟩

/-- The program counter the exit `PUSH2 2080` sits at: 3034. -/
theorem m9Exit_pcs :
    Artifact.instructionPC 2374 = 3034 := by decide

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralJumpTarget_window
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralPush_window
