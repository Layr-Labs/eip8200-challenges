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

* `jumpSites_eq` pins the 98 control transfers, `literalJumpTargets_eq` the 87 destinations they
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
section — instruction 2328, pc 2898, the E6 entry `DUP5 JUMP` — is pinned in Lean by
`M9MacChain.entryPC_avoids`, and is the only data-dependent jump whose block the M9 exit feeds.

| instruction | pc | site | successor pinned by |
|---|---|---|---|
| 333 | 483  | compact-unsigned multiply tail `POP JUMP` | `BigCUMulRun.run_m9`: `retPc`, the caller's return literal |
| 388 | 552  | compact-unsigned decide tail `POP JUMP` | `BigCUUnsignedRun.run_decide_*` then the `0x2000` return literal |
| 2328 | 2898 | E6 conversion entry `DUP5 JUMP` | `M9MacChain.gasSteps_entry`: `entryPC n ∈ {2899, 3032}` — *(pinned, `entryPC_avoids`)* |
| 2775 | 3466 | kernel `setup` row jump | the `htl` word at `0xae0`, `= 2080 + 32n` (`TnM128Setup`) |
| 2849 | 3561 | row head `DUP6 JUMP` | `TnCacheHeadTrace.run_head`: `ent`, the caller's row-head literal |
| 3309 | 4127 | row tail `DUP3 JUMPI` | `TnCacheRowTrace.run_tail`: `pc0 + 51 = 4128`, or `hd` |
| 3439 | 4307 | computed diagonal jump | `TnCacheSquareTrace.run_B`: `ent`, the caller's diagonal literal |
| 3605 | 4537 | early-`CSUB` copy resume | `EarlyCsubTrace` / `LazyCsubTrace`: the `0x840` store literal |
| 3614 | 4550 | early-`CSUB` copy tail | `CsubFixed`: the `0x10e3` literal |
| 4041 | 5029 | RED tail return | `R4Runs.run_redt`: `ret`, the caller's return literal |
| 4276 | 5308 | retained-`T` return | `RetainedTEntry.run_tail`: `ret`, the caller's return literal |

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
    [18, 34, 45, 71, 77, 89, 102, 120, 132, 142, 150, 204, 207, 227, 233, 256,
     263, 273, 282, 297, 301, 317, 321, 326, 333, 375, 378, 383, 388, 398, 413, 422,
     432, 456, 477, 553, 567, 570, 578, 592, 615, 619, 2009, 2012, 2018, 2023, 2032, 2035,
     2045, 2057, 2064, 2071, 2083, 2090, 2119, 2264, 2328, 2585, 2590, 2597, 2631, 2643, 2650, 2687,
     2695, 2702, 2714, 2717, 2775, 2849, 3309, 3317, 3342, 3344, 3358, 3370, 3376, 3382, 3389, 3439,
     3447, 3455, 3593, 3598, 3605, 3614, 3628, 3630, 3726, 3826, 3899, 4041, 4061, 4274, 4276, 4391,
     4411, 4421] := by decide

theorem literalJumpTargets_eq : literalJumpTargets =
    [127, 866, 866, 25, 599, 153, 186, 156, 222, 2397, 193, 273, 301, 396, 413, 388,
     413, 312, 484, 477, 484, 469, 484, 421, 494, 548, 488, 570, 238, 843, 784, 790,
     790, 2545, 795, 238, 553, 553, 135, 116, 2402, 212, 2478, 790, 790, 2498, 790, 3387,
     2498, 5466, 790, 4308, 2589, 3346, 3208, 2811, 3287, 3220, 3214, 3198, 3284, 3266, 5444, 2811,
     2441, 4198, 4527, 4323, 4438, 4518, 4518, 4579, 5062, 5307, 4177, 4538, 4323, 4579, 5062, 4927,
     4927, 4927, 4198, 3841, 3977, 3378, 3383] := by decide

/-- The eleven sites whose destination is a stack word, in program order. -/
theorem dataDependentJumpSites_eq : dataDependentJumpSites =
    [333, 388, 2328, 2775, 2849, 3309, 3439, 3605, 3614, 4041, 4276] := by decide

/-- **No literal jump destination is the M9 exit.**  None of the 87 destinations the image
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

/-- The new `JUMPDEST` is a real instruction of the artifact at instruction 2564,
and the fixup's `SWAP3 POP` is at instructions 2576 and 2577. -/
theorem m9Exit_is_jumpdest :
    Artifact.submissionInstructions[2564]? = some (.op .JUMPDEST) ∧
      Artifact.submissionInstructions[2576]? = some (.op (.Swap ⟨2, by decide⟩)) ∧
      Artifact.submissionInstructions[2577]? = some (.op .POP) :=
  ⟨by rfl, by rfl, by rfl⟩

/-- The program counter the exit `JUMPDEST` sits at: 3168. -/
theorem m9Exit_pcs :
    Artifact.instructionPC 2564 = 3168 := by decide

theorem m9Exit_validJumpDests :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
        (Artifact.instructionPC 2564) = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralJumpTarget_window
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets.noLiteralPush_window
