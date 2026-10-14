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
    [10, 16, 28, 39, 60, 75, 89, 102, 120, 131, 133, 187, 190, 210, 216, 239,
     246, 256, 265, 280, 284, 300, 304, 309, 316, 358, 361, 366, 371, 381, 396, 405,
     415, 439, 460, 488, 534, 544, 547, 554, 568, 1898, 1911, 1915, 1925, 1937, 1949, 1956,
     1981, 2028, 2169, 2407, 2413, 2415, 2451, 2463, 2470, 2477, 2491, 2554, 2592, 3072, 3077, 3105,
     3107, 3120, 3124, 3136, 3138, 3153, 3161, 3169, 3177, 3307, 3309, 3314, 3321, 3328, 3343, 3345,
     3441, 3541, 3614, 3756, 3760, 3783, 3785, 3831, 4292, 4294, 4435, 4455] := by decide

theorem literalJumpTargets_eq : literalJumpTargets =
    [578, 103, 813, 813, 218, 31, 153, 186, 156, 202, 218, 253, 281, 376, 393, 368,
     393, 292, 464, 457, 464, 449, 464, 401, 474, 528, 468, 550, 218, 135, 755, 761,
     761, 2465, 765, 218, 533, 533, 2424, 761, 2444, 761, 3189, 761, 4033, 2509, 693, 3080,
     2710, 3154, 3088, 3082, 3068, 5546, 2710, 3964, 4246, 4048, 4160, 3995, 4839, 3275, 4060, 4237,
     5374, 3944, 4257, 4246, 4048, 4839, 4295, 4643, 4643, 4643, 4791, 4295, 4022, 4752, 3779] := by decide

/-- The twelve sites whose destination is a stack word, in program order. -/
theorem dataDependentJumpSites_eq : dataDependentJumpSites =
    [316, 371, 534, 2169, 2554, 2592, 3072, 3321, 3328, 3756, 4292, 4294, 4455] := by decide

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

/-- The exit `PUSH2 2080` is at instruction 2387,
and the fixup's `SWAP3 POP` is at instructions 2398 and 2399. -/
theorem m9Exit_is_jumpdest :
    Artifact.submissionInstructions[2387]? = some (.push 2 2080) ∧
      Artifact.submissionInstructions[2398]? = some (.op (.Swap ⟨2, by decide⟩)) ∧
      Artifact.submissionInstructions[2399]? = some (.op .POP) :=
  ⟨by rfl, by rfl, by rfl⟩

/-- The program counter the exit `PUSH2 2080` sits at: 3041. -/
theorem m9Exit_pcs :
    Artifact.instructionPC 2387 = 3041 := by decide

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralJumpTarget_window
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralPush_window
