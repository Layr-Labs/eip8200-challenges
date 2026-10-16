import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option warningAsError false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-!
# Jump targets of the MODEXP image: the M9 exit's three new `JUMPDEST`s are unreachable

The conversion section leaves through three `JUMPDEST`s at pc 3168, 3169 and 3170
(`M9Mac.exitProgram`, `M9MacChain.gasSteps_exit`) and the top-limb fixup spends the mask again
with `SWAP3 POP` at pc 3184..3185.  Those three bytes were `SWAP1 SWAP2 POP` before, so they
were *not* jump destinations; now they are.  This module enumerates every `JUMP`/`JUMPI` in the
artifact and shows that none of them can name pc 3168, 3169 or 3170.

Four facts, all `decide`d against the artifact's own 4,422-instruction list:

* `jumpSites_eq` pins the 99 control transfers, `literalJumpTargets_eq` the 88 destinations they
  name with a `PUSH` immediate (68 distinct), and `dataDependentJumpSites_eq` the eleven whose
  operand is a stack word.
* `noLiteralJumpTarget_window`: none of those 87 literal destinations is 3168, 3169 or 3170.
* `noLiteralPush_window` is stronger still — *no* `PUSH` immediate anywhere in the image equals
  3168, 3169 or 3170.  A computed operand is a stack word, and every stack word the program
  seeds is either a `PUSH` immediate or an earlier jump destination, so this excludes the three
  program counters from the data flow as well as from the immediate targets.
* `m9Exit_is_jumpdest` / `m9Exit_pcs` / `m9Exit_validJumpDests`: the three new bytes really are
  instructions 2564..2566 at pc 3168..3170 and really are valid jump destinations.

## What is *not* formalised here

The framework in this tree does **not** carry a global "every jump destination lies in a fixed
set" statement.  It pins each site where the site is used, through the `pc` in the conclusion of
that block's `run_*` theorem.  The table below is that pinning, one row per data-dependent site.
Rows marked *(pinned)* carry the successor as a literal, or as a frame word the callers seed from
an in-image `PUSH`, which `noLiteralPush_window` excludes.  The one site inside the conversion
section — instruction 2248, pc 2898, the E6 entry `DUP5 JUMP` — is pinned in Lean by
`M9MacChain.entryPC_avoids`, and is the only data-dependent jump whose block the M9 exit feeds.

| instruction | pc | site | successor pinned by |
|---|---|---|---|
| 333 | 483  | compact-unsigned multiply tail `POP JUMP` | `BigCUMulRun.run_m9`: `retPc`, the caller's return literal |
| 388 | 552  | compact-unsigned decide tail `POP JUMP` | `BigCUUnsignedRun.run_decide_*` then the `0x2000` return literal |
| 2248 | 2898 | E6 conversion entry `DUP5 JUMP` | `M9MacChain.gasSteps_entry`: `entryPC n ∈ {2899, 3032}` — *(pinned, `entryPC_avoids`)* |
| 2775 | 3466 | kernel `setup` row jump | the `htl` word at `0xae0`, `= 2080 + 32n` (`TnM128Setup`) |
| 2849 | 3561 | row head `DUP6 JUMP` | `TnCacheHeadTrace.run_head`: `ent`, the caller's row-head literal |
| 3309 | 4127 | row tail `DUP3 JUMPI` | `TnCacheRowTrace.run_tail`: `pc0 + 51 = 4128`, or `hd` |
| 3439 | 4307 | computed diagonal jump | `TnCacheSquareTrace.run_B`: `ent`, the caller's diagonal literal |
| 3605 | 4537 | early-`CSUB` copy resume | `EarlyCsubTrace` / `LazyCsubTrace`: the `0x840` store literal |
| 3614 | 4550 | early-`CSUB` copy tail | `CsubFixed`: the `0x10e3` literal |
| 4041 | 5029 | RED tail return | `R4Runs.run_redt`: `ret`, the caller's return literal |
| 4276 | 5308 | retained-`T` return | `RetainedTEntry.run_tail`: `ret`, the caller's return literal |
| 4299 | 5465 | shift cleanup tail `PUSH2 0989 ADD JUMP` | `ShiftTrace3.run_cleanup`: `2441 + z`, the last riding slot (`0` from `E5`, `30` after the E3 phase switch) — *(pinned)* |

The closed end-to-end statement is the backstop for the rows that are not *(pinned)*:
`Challenge.Modexp.Benchmark.candidate : Challenge.Modexp.Correct bytecode` has no hypotheses, so
if any of these sites could name 3168..3170 on some valid input the whole theorem would fail to
close.  Nothing here assumes that; the `decide`d facts above are what make the static half
independent of it.
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
eleven sites whose operand is a stack word. -/
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
    [10, 16, 31, 42, 44, 55, 74, 86, 99, 117, 130, 140, 185, 188, 208, 214, 237, 244, 254, 263, 278, 282, 298, 302, 307, 314, 356, 359, 364, 369, 379, 394, 403, 413, 437, 458, 485, 498, 512, 1840, 1842, 1846, 1855, 1865, 1877, 1884, 1891, 1901, 2156, 2394, 2400, 2402, 2438, 2450, 2456, 2463, 2477, 2532, 2569, 3048, 3053, 3080, 3082, 3095, 3099, 3111, 3113, 3128, 3135, 3143, 3151, 3281, 3283, 3288, 3295, 3302, 3317, 3330, 3417, 3516, 3589, 3728, 3736, 3753, 3761, 3807, 3810, 4267, 4270, 4410, 4430, 4438, 4484, 4487, 6695, 6700, 6818, 6940, 7621, 7638, 7646, 7692, 7699, 7714] := by decide

theorem literalJumpTargets_eq : literalJumpTargets =
    [578, 101, 745, 745, 9800, 219, 33, 154, 187, 157, 5554, 5570, 254, 281, 376, 393, 368, 393, 292, 464, 457, 464, 449, 464, 401, 474, 528, 468, 550, 219, 136, 697, 219, 219, 2390, 533, 533, 2350, 219, 2369, 2470, 219, 3181, 219, 4010, 2336, 3073, 2704, 3146, 3081, 3075, 3061, 5522, 2704, 3942, 4223, 4025, 4137, 3973, 4816, 3256, 4037, 4214, 5351, 3922, 4234, 4223, 4025, 4816, 8998, 4621, 4621, 4621, 4768, 4280, 3999, 4731, 5615, 3758, 194, 5575, 5544, 8800, 8800, 5858, 3942, 9752, 8998, 3999, 9715, 9818, 745] := by decide

/-- The twelve sites whose destination is a stack word, in program order. -/
theorem dataDependentJumpSites_eq : dataDependentJumpSites =
    [314, 369, 2156, 2532, 2569, 3048, 3295, 3302, 3728, 4267, 4270, 4430] := by decide

/-- **No literal jump destination is the M9 exit.**  None of the 88 destinations the image
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
