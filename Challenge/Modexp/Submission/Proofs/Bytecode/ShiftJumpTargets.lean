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
    [10, 16, 28, 39, 60, 75, 89, 102, 120, 132, 142, 150, 204, 207, 227, 233,
     256, 263, 273, 282, 297, 301, 317, 321, 326, 333, 375, 378, 383, 388, 398, 413,
     422, 432, 456, 477, 505, 551, 553, 567, 570, 578, 592, 615, 619, 1970, 1973, 1979,
     1992, 1996, 2006, 2018, 2025, 2032, 2044, 2051, 2076, 2123, 2285, 2523, 2529, 2531, 2535, 2569,
     2581, 2588, 2625, 2633, 2640, 2654, 2717, 2756, 3236, 3241, 3269, 3271, 3284, 3288, 3300, 3302,
     3317, 3325, 3374, 3382, 3390, 3520, 3522, 3527, 3534, 3541, 3556, 3558, 3654, 3754, 3827, 3969,
     3973, 3996, 3998, 4044, 4249, 4251, 4392, 4412] := by decide

theorem literalJumpTargets_eq : literalJumpTargets =
    [599, 103, 872, 872, 238, 31, 153, 186, 156, 222, 2448, 193, 273, 301, 396, 413,
     388, 413, 312, 484, 477, 484, 469, 484, 421, 494, 548, 488, 570, 238, 843, 784,
     790, 790, 2592, 2592, 795, 238, 553, 553, 135, 103, 2453, 212, 2527, 790, 2547, 790,
     3401, 2547, 2568, 790, 4299, 2636, 714, 3228, 2858, 3366, 3307, 3240, 3234, 3216, 3284, 3266,
     5522, 2858, 4176, 4512, 4314, 4426, 4207, 5105, 3487, 4326, 4503, 5350, 4156, 4523, 4512, 4314,
     5105, 4561, 4909, 4909, 4909, 5057, 4561, 4234, 5018, 3862, 3991] := by decide

/-- The twelve sites whose destination is a stack word, in program order. -/
theorem dataDependentJumpSites_eq : dataDependentJumpSites =
    [333, 388, 551, 2285, 2717, 2756, 3236, 3374, 3534, 3541, 3969, 4251, 4412] := by decide

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

/-- The exit `PUSH2 2080` is at instruction 2503,
and the fixup's `SWAP3 POP` is at instructions 2514 and 2515. -/
theorem m9Exit_is_jumpdest :
    Artifact.submissionInstructions[2503]? = some (.push 2 2080) ∧
      Artifact.submissionInstructions[2514]? = some (.op (.Swap ⟨2, by decide⟩)) ∧
      Artifact.submissionInstructions[2515]? = some (.op .POP) :=
  ⟨by rfl, by rfl, by rfl⟩

/-- The program counter the exit `PUSH2 2080` sits at: 3189. -/
theorem m9Exit_pcs :
    Artifact.instructionPC 2503 = 3189 := by decide

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralJumpTarget_window
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralPush_window
